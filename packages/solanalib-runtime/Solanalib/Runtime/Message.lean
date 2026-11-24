/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Exec

@[expose] public section

/-!
# Messages, top-level instructions and the Instructions sysvar

A value representation of a message after sanitization and address-table lookup:
the account keys with their signer and writable flags, and the compiled top-level
instructions. `Message.WF` records only part of sanitization; see
[message privileges and the Instructions
sysvar](../../source-notes/agave-4.3.2.md#message-privileges-and-instructions-sysvar).
-/

namespace Solanalib.Runtime

/-- A compiled top-level instruction. -/
structure CompiledIx where
  programIdIndex : Nat
  accounts : List Nat
  data : Bytes
  deriving DecidableEq, Repr

/-- A loaded message: the static keys of the header, followed by the writable and the
read-only addresses loaded from lookup tables (version 0). -/
structure Message where
  numRequiredSignatures : Nat
  numReadonlySigned : Nat
  numReadonlyUnsigned : Nat
  staticKeys : List Pubkey
  loadedWritable : List Pubkey
  loadedReadonly : List Pubkey
  recentBlockhash : Bytes
  instructions : List CompiledIx
  deriving Repr

namespace Message

/-- All account keys of the message. -/
def keys (m : Message) : List Pubkey := m.staticKeys ++ m.loadedWritable ++ m.loadedReadonly

def isSigner (m : Message) (i : Nat) : Bool := decide (i < m.numRequiredSignatures)

/-- The writable flag of the header and of the lookup tables, before demotion. -/
def isWritableIndex (m : Message) (i : Nat) : Bool :=
  if i < m.staticKeys.length then
    if i < m.numRequiredSignatures then decide (i < m.numRequiredSignatures - m.numReadonlySigned)
    else decide (i < m.staticKeys.length - m.numReadonlyUnsigned)
  else decide (i < m.staticKeys.length + m.loadedWritable.length)

/-- Whether index `i` is the program of a top-level instruction. -/
def isInvoked (m : Message) (i : Nat) : Bool := m.instructions.any (·.programIdIndex == i)

/-- The writable flag after demotion: reserved keys, and invoked programs unless loader
v3 is among the keys, are read-only. This corresponds to `is_writable` and the
program-demotion check in solana-message 4.5.0; see
[message privileges](../../source-notes/agave-4.3.2.md#message-privileges-and-instructions-sysvar).
-/
def isWritable (p : Profile) (m : Message) (i : Nat) : Bool :=
  let k := m.keys.getD i default
  let secp256r1 := p.release != .agave_3_1_12 || p.features.secp256r1Precompile
  m.isWritableIndex i && !(Ids.reservedKeys secp256r1).contains k &&
    !(m.isInvoked i && !m.keys.contains Ids.bpfLoaderUpgradeable)

/-- The frame of a top-level instruction, with the flags of the message. -/
def frame (p : Profile) (m : Message) (ix : CompiledIx) : Frame :=
  { programIdx := ix.programIdIndex
    accounts := ix.accounts.map fun i => ⟨i, m.isSigner i, m.isWritable p i⟩
    data := ix.data }

/-- The frames of all top-level instructions. -/
def frames (p : Profile) (m : Message) : List Frame := m.instructions.map (m.frame p)

/-- The partial sanitization conditions recorded by the model: key and index validity
and selected count limits. This predicate does not check every message-header,
blockhash, signature or address-table requirement of Agave. See
[transaction admission](../../source-notes/agave-4.3.2.md#transaction-admission-and-loading). -/
def WF (p : Profile) (m : Message) : Prop :=
  m.keys.Nodup ∧ 0 < m.numRequiredSignatures ∧
  (∀ ix ∈ m.instructions, ix.programIdIndex < m.keys.length ∧ ∀ i ∈ ix.accounts, i < m.keys.length)
    ∧
  m.keys.length ≤ p.maxTxAccountLocks ∧
  (p.features.staticInstructionLimit → m.instructions.length ≤ 64) ∧
  (p.features.limitInstructionAccounts → ∀ ix ∈ m.instructions, ix.accounts.length ≤ 255)

end Message

/-! ## The Instructions sysvar -/

/-- The serialization of one instruction in the Instructions sysvar: account count,
flags and keys, program id, data length and data, corresponding to
`serialize_instructions` in solana-instructions-sysvar 4.0.0. See
[the Instructions
sysvar](../../source-notes/agave-4.3.2.md#message-privileges-and-instructions-sysvar). -/
def ixSysvarEntry (m : Message) (p : Profile) (ix : CompiledIx) : Bytes :=
  u16le ix.accounts.length ++
    (ix.accounts.map fun i =>
      UInt8.ofNat ((if m.isSigner i then 1 else 0) + (if m.isWritable p i then 2 else 0)) ::
        (m.keys.getD i default).bytes).flatten ++
    (m.keys.getD ix.programIdIndex default).bytes ++ u16le ix.data.length ++ ix.data

theorem ixSysvarEntry_length (m : Message) (p : Profile) (ix : CompiledIx) :
    (ixSysvarEntry m p ix).length = 36 + 33 * ix.accounts.length + ix.data.length := by
  have sum : ∀ accounts : List Nat,
      (accounts.map (fun _ => 33)).sum = accounts.length * 33 := by
    intro accounts
    induction accounts with
    | nil => rfl
    | cons index rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  simp [ixSysvarEntry, u16le, List.length_flatten, List.map_map, Function.comp_def,
    Pubkey.length_eq,
    sum, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

/-- `construct_instructions_data`: the count, the absolute offsets, the entries, and two
bytes for the index of the current top-level instruction, initially 0. -/
def ixSysvarData (p : Profile) (m : Message) : Bytes :=
  let entries := m.instructions.map (ixSysvarEntry m p)
  let n := entries.length
  let offsets := (List.range n).map fun i => u16le (2 + 2 * n + prefixLen entries i)
  u16le n ++ offsets.flatten ++ entries.flatten ++ u16le 0

/-- Every instruction start offset must fit the u16 offset table. The last
instruction may extend beyond that range: no final-buffer-size check is made
(`solana-instructions-sysvar-4.0.0/src/lib.rs:123-155`). -/
def ixSysvarOffsetsFit (p : Profile) (m : Message) : Bool :=
  let entries := m.instructions.map (ixSysvarEntry m p)
  (List.range entries.length).all fun i =>
    decide (2 + 2 * entries.length + prefixLen entries i < 2^16)

/-- The constructed sysvar account: owner `Sysvar1111…`, default lamports, executable
flag and rent epoch, as constructed by Agave 4.3.2
`svm/src/account_loader.rs::construct_instructions_account`. -/
def ixSysvarAccount (p : Profile) (m : Message) : Account :=
  { lamports := 0, data := ixSysvarData p m, owner := Ids.sysvarOwner, executable := false,
    rentEpoch := 0 }

/-! ## Top-level instructions -/

/-- `process_precompile`: push, verification, pop; a verification failure is
`Custom` with the discriminant of the `PrecompileError`, following Agave 4.3.2
`InvokeContext::process_precompile`. Verification is a supplied primitive; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def processPrecompile (W : World) (ts : TxState) (f : Frame) (allData : List Bytes) :
    Except InstrError TxState :=
  match push W.prof ts f with
  | .error e => .error e
  | .ok ts1 =>
    match W.prims.precompileVerify (ts.key f.programIdx) f.data allData with
    | some n => .error (.Custom n)
    | none => pop ts1

/-- `process_message`: the top-level instructions in order; the first failure ends the
transaction with its index, following Agave 4.3.2 `InvokeContext::process_message`.
See [execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
inductive ProcMessage (W : World) (allData : List Bytes) :
    TxState → List Frame → Nat → Except TxError TxState → Prop
  | nil {ts : TxState} {k : Nat} : ProcMessage W allData ts [] k (.ok ts)
  | precompile {ts ts' : TxState} {f : Frame} {fs : List Frame} {k : Nat}
      {r : Except TxError TxState} :
      isPrecompile W.prof (ts.key f.programIdx) = true →
      processPrecompile W ts f allData = .ok ts' → ProcMessage W allData ts' fs (k + 1) r →
      ProcMessage W allData ts (f :: fs) k r
  | precompileFail {ts : TxState} {f : Frame} {fs : List Frame} {k : Nat} {e : InstrError} :
      isPrecompile W.prof (ts.key f.programIdx) = true →
      processPrecompile W ts f allData = .error e →
      ProcMessage W allData ts (f :: fs) k (.error (.InstructionError k e))
  | instr {ts ts' : TxState} {f : Frame} {fs : List Frame} {k : Nat} {r : Except TxError TxState} :
      isPrecompile W.prof (ts.key f.programIdx) = false →
      ProcInstr W ts f (.ok ts') → ProcMessage W allData ts' fs (k + 1) r →
      ProcMessage W allData ts (f :: fs) k r
  | instrFail {ts : TxState} {f : Frame} {fs : List Frame} {k : Nat} {e : InstrError} :
      isPrecompile W.prof (ts.key f.programIdx) = false →
      ProcInstr W ts f (.error e) →
      ProcMessage W allData ts (f :: fs) k (.error (.InstructionError k e))

end Solanalib.Runtime
