/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Specs.Core.Token
public import Solanalib.Specs.Core.Instruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Instruction

/-- The canonical runtime instruction value. -/
abbrev Value := Solanalib.Specs.Core.Instruction.Value
/-- The canonical runtime account metadata value. -/
abbrev Meta := Solanalib.Specs.Core.Instruction.Meta

/-- The common single-owner/multisig suffix. Repeated signer keys are preserved,
and the authority is a signer exactly when the supplied signer list is empty. -/
def authorityMetas (authority : Solanalib.Runtime.Pubkey) (signers : List Solanalib.Runtime.Pubkey)
  : List Meta :=
  Solanalib.Specs.Core.Instruction.accountMeta authority signers.isEmpty false ::
    signers.map (fun signer => Solanalib.Specs.Core.Instruction.accountMeta signer true false)

/-- Transfer tag followed by the little-endian u64 amount. -/
def transferData (amount : Nat) : Bytes := 3 :: Solanalib.Runtime.u64le amount

/-- Checked-transfer tag, little-endian u64 amount and decimal byte. -/
def transferCheckedData (amount decimals : Nat) : Bytes :=
  12 :: (Solanalib.Runtime.u64le amount ++ [UInt8.ofNat decimals])

/-- The one-byte CloseAccount instruction payload. -/
def closeAccountData : Bytes := [9]

/-- Common ordered account arguments for transfer, close and lamport withdrawal. -/
structure AuthorityArgs where
  /-- The caller-supplied program identity. -/
  programId : Solanalib.Runtime.Pubkey
  /-- The source account or observed account reference. -/
  source : Solanalib.Runtime.Pubkey
  /-- The destination account or observed account reference. -/
  destination : Solanalib.Runtime.Pubkey
  /-- The authority account or observed account reference. -/
  authority : Solanalib.Runtime.Pubkey
  /-- Ordered signer keys or seed slices, preserving duplicates. -/
  signers : List Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- The authority account list and an unsigned 64-bit transfer amount. -/
structure TransferArgs extends AuthorityArgs where
  /-- Mathematical amount; the Rust binding supplies the source u64 bound. -/
  amount : Nat
  deriving DecidableEq, Repr

/-- Transfer arguments with the mint account and declared decimals. -/
structure TransferCheckedArgs extends TransferArgs where
  /-- The readonly mint account or observed reference. -/
  mint : Solanalib.Runtime.Pubkey
  /-- Mathematical decimals; the Rust binding supplies the source u8 bound. -/
  decimals : Nat
  deriving DecidableEq, Repr

/-- Construct ordered source, destination, authority and signer metadata. -/
def authorityInstruction (args : AuthorityArgs) (data : Bytes) : Value :=
  Solanalib.Specs.Core.Instruction.make args.programId
    (Solanalib.Specs.Core.Instruction.accountMeta args.source false true ::
      Solanalib.Specs.Core.Instruction.accountMeta args.destination false true ::
      authorityMetas args.authority args.signers) data

/-- Insert the readonly mint between source and destination metadata. -/
def transferCheckedInstruction (args : TransferCheckedArgs) : Value :=
  Solanalib.Specs.Core.Instruction.make args.programId
    (Solanalib.Specs.Core.Instruction.accountMeta args.source false true ::
      Solanalib.Specs.Core.Instruction.accountMeta args.mint false false ::
      Solanalib.Specs.Core.Instruction.accountMeta args.destination false true ::
      authorityMetas args.authority args.signers)
    (transferCheckedData args.amount args.decimals)

/-- A return-only mathematical value contract. Allocation and Rust execution
correspondence are separate obligations, rather than consequences of this relation. -/
def valueContract {Args Result : Type} (pre : Args → Prop) (run : Args → Result) :
    Solanalib.Contracts.Model Unit Args Result :=
  .returning (fun _ args => pre args)
    (fun before args result after => result = run args ∧ after = before)

/-- The exact return graph of a pure constructor-value observation. -/
def valueReference {Args Result : Type} (run : Args → Result) :
    Unit → Args → Result × Unit := fun before args => (run args, before)

theorem valueReference_realizes {Args Result : Type} (pre : Args → Prop)
    (run : Args → Result) :
    (valueContract pre run).RealizedBy (valueReference run) := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

/-- The authority suffix retains the exact supplied account multiplicity. -/
theorem authorityMetas_keys (authority : Solanalib.Runtime.Pubkey) (signers : List
  Solanalib.Runtime.Pubkey) :
    (authorityMetas authority signers).map Solanalib.Runtime.CpiMeta.key = authority :: signers :=
      by
  simp [authorityMetas, Solanalib.Specs.Core.Instruction.accountMeta, Function.comp_def]

/-- A successful transfer has the source and destination before every authority account. -/
theorem authorityInstruction_keys (args : AuthorityArgs) (data : Bytes) :
    (authorityInstruction args data).metas.map Solanalib.Runtime.CpiMeta.key =
      args.source :: args.destination :: args.authority :: args.signers := by
  simp [authorityInstruction, Solanalib.Specs.Core.Instruction.make,
    Solanalib.Specs.Core.Instruction.accountMeta, authorityMetas_keys]

/-- No signer sorting or deduplication occurs in checked transfers. -/
theorem transferCheckedInstruction_keys (args : TransferCheckedArgs) :
    (transferCheckedInstruction args).metas.map Solanalib.Runtime.CpiMeta.key =
      args.source :: args.mint :: args.destination :: args.authority :: args.signers := by
  simp [transferCheckedInstruction, Solanalib.Specs.Core.Instruction.make,
    Solanalib.Specs.Core.Instruction.accountMeta, authorityMetas_keys]


end Solanalib.Specs.Core.Token.Instruction
