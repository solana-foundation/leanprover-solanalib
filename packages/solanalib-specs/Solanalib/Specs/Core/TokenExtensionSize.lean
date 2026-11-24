/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- Saturating usize addition for the pinned 64-bit source target. -/
def saturatingSizeAdd (left right : Nat) : Nat := min (left + right) Solanalib.Runtime.U64_MAX

/-- Extensible layouts reserve two extra zero bytes if their size would equal
the 355-byte multisig representation. -/
def adjustMultisigLength (length : Nat) : Nat :=
  if length = multisigLength then saturatingSizeAdd length 2 else length

/-- The four-byte TLV header is added only after fixed-size type validation. -/
def ExtensionType.tlvLength (kind : ExtensionType) : Except Error Nat :=
  kind.fixedLength.map fun length => saturatingSizeAdd (saturatingSizeAdd length 2) 2

/-- Mathematical observation of the distinct-type bitset of the source and total.
The list records first insertion order; only membership affects deduplication. -/
structure ExtensionLengths where
  /-- Distinct inserted tags, in first-insertion order. -/
  seen : List ExtensionType
  /-- Sum of their complete fixed TLV lengths. -/
  byteCount : Nat
  deriving DecidableEq, Repr

/-- No extensions have yet been sized. -/
def ExtensionLengths.empty : ExtensionLengths := ⟨[], 0⟩

/-- A duplicate is ignored before type sizing; the first insertion contributes
its complete TLV length. Ordinary errors are retained. -/
def ExtensionLengths.insert (lengths : ExtensionLengths) (kind : ExtensionType) :
    Except Error ExtensionLengths :=
  if kind ∈ lengths.seen then .ok lengths
  else kind.tlvLength.map fun length =>
    ⟨lengths.seen ++ [kind], saturatingSizeAdd lengths.byteCount length⟩

/-- Insert a list in source order, stopping at the first ordinary error. -/
def ExtensionLengths.insertAll (lengths : ExtensionLengths) :
    List ExtensionType → Except Error ExtensionLengths
  | [] => .ok lengths
  | kind :: rest => (lengths.insert kind).bind fun next => next.insertAll rest

/-- An empty set needs only the size of the selected base type. Any extension adds
the common 165-byte prefix and one account-type byte before multisig adjustment. -/
def ExtensionLengths.accountLength (lengths : ExtensionLengths) (baseLength : Nat) : Nat :=
  if lengths.seen.isEmpty then baseLength
  else adjustMultisigLength (saturatingSizeAdd lengths.byteCount
    (Solanalib.Specs.Core.Token.accountLength + 1))

/-- Generic fixed-extension sizing, used by the ExtensionType helper of the source.
This helper does not add a base-account association check that Rust omits. -/
def calculateExtensionAccountLength (baseLength : Nat) (types : List ExtensionType) :
    Except Error Nat :=
  (ExtensionLengths.empty.insertAll types).map (·.accountLength baseLength)

/-- Add the account extensions required by one encountered mint tag. -/
def insertRequiredAccountExtensions (lengths : ExtensionLengths) (kind : ExtensionType) :
    Except Error ExtensionLengths :=
  lengths.insertAll kind.requiredAccountExtensions

/-- Compute the size of a token account from raw mint bytes. Additional-extension
kind validation comes first; all PodMint/layout errors become InvalidMint (2).
TLV-walk and extension-sizing errors keep their original codes. Required tags
are visited in TLV order before additional tags, with one shared deduplication set. -/
def calculateAccountLengthFromMint (mintBytes : Bytes) (additional : List ExtensionType) :
    Except Error Nat :=
  if additional.any (fun kind => kind.accountType != .account) then .error (.Custom 20)
  else
    match unpackPodMintWithExtensions mintBytes with
    | .error _ => .error (.Custom 2)
    | .ok mint => do
      let (required, _) ← foldExtensionTypes insertRequiredAccountExtensions
        ExtensionLengths.empty 0 mint.tlv
      let complete ← required.insertAll additional
      pure (complete.accountLength accountLength)

/-- Deduplication keeps both the seen set and total unchanged. -/
theorem ExtensionLengths.insert_duplicate (lengths : ExtensionLengths) (kind : ExtensionType)
    (seen : kind ∈ lengths.seen) : lengths.insert kind = .ok lengths := by
  simp [insert, seen]

/-- Empty extensions use the actual selected base size. -/
theorem calculateExtensionAccountLength_empty (baseLength : Nat) :
    calculateExtensionAccountLength baseLength [] = .ok baseLength := rfl

/-- Every production mint-required extension belongs to a token account. -/
theorem ExtensionType.required_is_account (kind required : ExtensionType)
    (member : required ∈ kind.requiredAccountExtensions) : required.accountType = .account := by
  cases kind <;> simp only [requiredAccountExtensions, List.mem_cons, List.not_mem_nil,
    or_false] at member
  all_goals first | contradiction | obtain rfl | rfl := member <;> rfl

/-- All production token-account extension types have a fixed size. -/
theorem ExtensionType.account_fixed (kind : ExtensionType)
    (account : kind.accountType = .account) : ∃ length, kind.fixedLength = .ok length := by
  cases kind <;> simp_all [accountType, fixedLength]

/-- An invalid requested type wins over every malformed-mint error. -/
theorem calculateAccountLengthFromMint_wrong_additional (mintBytes : Bytes)
    (additional : List ExtensionType)
    (wrong : additional.any (fun kind => kind.accountType != .account) = true) :
    calculateAccountLengthFromMint mintBytes additional = .error (.Custom 20) := by
  simp [calculateAccountLengthFromMint, wrong]

/-- The exact multisig collision receives two additional bytes. -/
theorem adjustMultisigLength_collision : adjustMultisigLength 355 = 357 := by decide

end Solanalib.Specs.Core.Token
