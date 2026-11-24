/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.MetadataInitialize

/-- The three owned Rust string values, in source declaration/serialization order. -/
structure Text where
  /-- Token name. -/
  name : String
  /-- Token symbol. -/
  symbol : String
  /-- Metadata URI. -/
  uri : String
  deriving DecidableEq, Repr

/-- UTF-8 is serialized, not a sequence of Unicode code points. -/
def Text.bytes (text : Text) : List Bytes :=
  [text.name.toUTF8.data.toList, text.symbol.toUTF8.data.toList, text.uri.toUTF8.data.toList]

/-- the three checked u32 byte lengths of Borsh. An oversized string makes `to_vec`
return an I/O error, which this SDK unwraps; it is not an SDK Result return. -/
def Text.fits (text : Text) : Prop := ∀ bytes ∈ text.bytes, bytes.length < 2^32

instance (text : Text) : Decidable text.fits := inferInstanceAs (Decidable (∀ b ∈ text.bytes,
  b.length < 2^32))

/-- The successful Borsh payload, with one little-endian u32 length per string. -/
def Text.encoded (text : Text) : Bytes :=
  text.bytes.flatMap fun bytes => Solanalib.Runtime.u32le bytes.length ++ bytes

/-- The first eight SHA-256 bytes for the compile-time discriminator
input of the source `spl_token_metadata_interface:initialize_account`. It is a constant,
not a runtime hash syscall. -/
def discriminator : Bytes := [210, 225, 30, 162, 88, 184, 77, 141]

/-- Resource identities of the same three owned strings moved into Initialize.
They need not coincide with byte-vector identities in an implementation. -/
structure Owners (Resource : Type) where
  /-- Name buffer owner. -/
  name : Resource
  /-- Symbol buffer owner. -/
  symbol : Resource
  /-- URI buffer owner. -/
  uri : Resource

/-- Five borrowed keys and three moved strings. No program-ID check is made. -/
structure Args (Resource : Type) where
  /-- Arbitrary program identity retained in the returned instruction. -/
  programId : Solanalib.Runtime.Pubkey
  /-- Writable metadata account. -/
  metadata : Solanalib.Runtime.Pubkey
  /-- Readonly update authority, not marked as a signer. -/
  updateAuthority : Solanalib.Runtime.Pubkey
  /-- Readonly mint. -/
  mint : Solanalib.Runtime.Pubkey
  /-- Readonly signer mint authority. -/
  mintAuthority : Solanalib.Runtime.Pubkey
  /-- Their actual owned resource identities. -/
  owners : Owners Resource

/-- Owned dependencies beyond the shared metadata/byte-vector operations.
`toVec` is the concrete Borsh dependency, including its local allocation and
cleanup; it is not an instruction builder or CPI oracle. Its success encoding
and partial/error effects are separately expressible by `Serialization`.
The append and destructor callbacks retain actual resource IDs and exit states. -/
structure Types where
  /-- Shared actual vector state, providers, and unwind policy. -/
  vectors : InstructionAllocated.Types
  /-- Logical identities of owned String values. -/
  StringResource : Type
  /-- Observe an existing String owner in the actual current state. -/
  stringCurrent : vectors.State → StringResource → Option String
  /-- Actual Borsh `to_vec` dependency on the borrowed Initialize owners.
Unit denotes exactly ErrorKind::InvalidData from u32 length conversion;
`unwrap` consumes that complete error value. -/
  toVec : Callback.Run vectors.State (Owners StringResource) (Except Unit vectors.ByteResource)
    vectors.Unwind vectors.Terminal
  /-- `Vec::append` receives target then temporary source, retaining both tokens. -/
  append : Callback.Run vectors.State (vectors.ByteResource × vectors.ByteResource)
    Unit vectors.Unwind vectors.Terminal
  /-- Destructor of one moved String. Struct fields are dropped name/symbol/URI. -/
  dropString : Callback.Run vectors.State StringResource Unit vectors.Unwind vectors.Terminal
  /-- The actual unwrap failure. It has no normal return value. -/
  unwrap : Callback.Run vectors.State Unit Empty vectors.Unwind vectors.Terminal

/-- Read all three actual owners at the serialization call, after preceding
vector effects. No initial text snapshot substitutes for these observations. -/
def currentText (types : Types) (state : types.vectors.State)
    (owners : Owners types.StringResource) : Option Text := do
  let name ← types.stringCurrent state owners.name
  let symbol ← types.stringCurrent state owners.symbol
  let uri ← types.stringCurrent state owners.uri
  return ⟨name, symbol, uri⟩

/-- Dependency correspondence for Borsh 1.x string serialization. It constrains
actual ordinary exits without requiring termination, determinism or a successful
allocator. Representation/ownership framing remains separate. -/
def Serialization (types : Types) : Prop :=
  ∀ before owners result after, types.toVec before owners (.returned result after) →
    ∃ text, currentText types before owners = some text ∧
    match result with
    | .ok resource => text.fits ∧ types.vectors.bytes.current after resource = some text.encoded
    | .error () => ¬ text.fits

/-- Exact account order and flags, retaining even identical key occurrences. -/
def metas {Resource : Type} (args : Args Resource) : List Solanalib.Runtime.CpiMeta :=
  [Solanalib.Specs.Core.Instruction.accountMeta args.metadata false true,
   Solanalib.Specs.Core.Instruction.accountMeta args.updateAuthority false false,
   Solanalib.Specs.Core.Instruction.accountMeta args.mint false false,
   Solanalib.Specs.Core.Instruction.accountMeta args.mintAuthority true false]

/-- Three source field destructors, each receiving the actual preceding state. -/
def textDrops (types : Types) (owners : Owners types.StringResource) :
    List (Owned.DropAction types.vectors.State types.vectors.Unwind types.vectors.Terminal) :=
  [fun state => types.dropString state owners.name,
   fun state => types.dropString state owners.symbol,
   fun state => types.dropString state owners.uri]

/-- `pack`: empty Vec, discriminator extension, Borsh temporary, append,
temporary drop. The output buffer is cleaned after any surviving inner unwind. -/
def pack (types : Types) (before : types.vectors.State) (owners : Owners types.StringResource)
    (final : Outcome types.vectors.State types.vectors.ByteResource
      types.vectors.Unwind types.vectors.Terminal) : Prop :=
  let (buffer, empty) := types.vectors.bytes.empty before
  Owned.protect types.vectors.doubleUnwind [types.vectors.bytes.dropAction buffer]
    (Callback.bind (fun state (_ : Unit) => types.vectors.bytes.extend state (buffer,
      discriminator))
      fun _ state outcome => Callback.bind types.toVec
        (fun result current resultOutcome => match result with
          | .error () => Callback.map Empty.elim types.unwrap current () resultOutcome
          | .ok temporary => Owned.scope types.vectors.doubleUnwind
              [types.vectors.bytes.dropAction temporary]
              (Callback.map (fun _ => buffer) (fun state (_ : Unit) =>
                types.append state (buffer, temporary))) current () resultOutcome)
        state owners outcome) empty () final

/-- Construct both instruction fields. An unwind cleans any completed metadata
after pack has cleaned its own temporary and buffer. -/
def construct (types : Types) : Callback.Run types.vectors.State (Args types.StringResource)
    (InstructionAllocated.Value types.vectors) types.vectors.Unwind types.vectors.Terminal :=
  fun before args => Callback.bind
    (fun state (_ : Unit) => types.vectors.metas.fromList state (metas args))
    (fun metadata state final => Owned.protect types.vectors.doubleUnwind
      [types.vectors.metas.dropAction metadata]
      (Callback.map (fun data =>
        ({ programId := args.programId, metas := metadata, data } : InstructionAllocated.Value
          types.vectors))
        (pack types)) state args.owners final) before ()

/-- The completed return place is protected while the local Initialize value
is dropped. If that cleanup unwinds, the returned instruction is also dropped;
construction unwind instead drops only the remaining input strings. -/
def run (types : Types) : Callback.Run types.vectors.State (Args types.StringResource)
    (InstructionAllocated.Value types.vectors) types.vectors.Unwind types.vectors.Terminal :=
  fun before args final => ∃ pending, construct types before args pending ∧
    match pending with
    | .returned instruction after => Owned.protect types.vectors.doubleUnwind
        (InstructionAllocated.drops types.vectors instruction)
        (Owned.scope types.vectors.doubleUnwind (textDrops types args.owners)
          (fun state (_ : Unit) outcome => outcome = .returned instruction state)) after () final
    | .unwound reason after => Owned.cleanup types.vectors.doubleUnwind
        (textDrops types args.owners) (.unwound reason after) final
    | .terminated reason => final = .terminated reason

/-- Complete local Initialize model, with explicit Borsh/Vec/String dependencies. -/
def family : Family where
  Index := Types
  State := fun types => types.vectors.State
  Args := fun types => Args types.StringResource
  Value := fun types => InstructionAllocated.Value types.vectors
  Unwind := fun types => types.vectors.Unwind
  Terminal := fun types => types.vectors.Terminal
  contract := fun types => { requires := fun _ _ => True, post := run types }

/-- Reference traversing all actual local dependency exits. -/
def reference : FamilyRun family := run

/-- All selected finite callback exits satisfy the local constructor contract. -/
theorem reference_holds : FamilyReference family reference := fun _ _ _ _ _ h => h

/-- Any actual successful Borsh return has the specified bytes when its
separate serialization correspondence is supplied. -/
theorem serialized_bytes {types : Types} (correct : Serialization types)
    {before after : types.vectors.State} {owners : Owners types.StringResource} {resource :
      types.vectors.ByteResource}
    (called : types.toVec before owners (.returned (.ok resource) after)) :
    ∃ text, currentText types before owners = some text ∧
      text.fits ∧ types.vectors.bytes.current after resource = some text.encoded :=
  correct before owners (.ok resource) after called

end Solanalib.Specs.Core.Token.MetadataInitialize
