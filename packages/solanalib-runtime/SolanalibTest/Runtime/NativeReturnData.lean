/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Runtime.TransactionSuccess

@[expose] public section

/-!
A hypothetical registered native builtin can set return data directly, without
instruction accounts or a CPI. This exercises the native transaction-context
API, whose explicit program tag and data are caller supplied. The SBF syscall
separately supplies the current program id and limits the data to 1,024 bytes.

The fixture uses the mainnet profile and the closed environment of the successful
System transaction test. Its additional native builtin is a capability witness;
it does not assert that a builtin currently registered on mainnet performs this
operation. Every successful transition below is constructed from execution rules.

Source: Agave `a203300045b405f86c9c84308b2eae76af69ac3b`,
`transaction-context/src/transaction.rs:504-515` (`set_return_data`) and
`syscalls/src/lib.rs:1931-1958` (`SyscallSetReturnData`).
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.NativeReturnDataTest

def programKey : Pubkey := Pubkey.ofNat 9001
def suppliedTag : Pubkey := Pubkey.ofNat 9002

def programAccount : Account :=
  { lamports := 1000000, data := [], owner := Ids.nativeLoader,
    executable := true, rentEpoch := 0 }

def world : World :=
  { TransactionSuccessTest.bank.world TransactionSuccessTest.tx with
    builtins := builtinTable (fun key => decide (key = programKey)) }

def frame : Frame := { programIdx := 0, accounts := [], data := [] }

def initial : TxState := initTxState [programKey] [programAccount]

def pushed : TxState := { initial with stack := [frame], trace := [⟨1, frame⟩] }

def running : TxState := resetReturnData pushed

def payload : Bytes := List.replicate (MAX_RETURN_DATA + 1) 0x5a

def afterNative : TxState := { running with returnData := (suppliedTag, payload) }

def post : TxState := { afterNative with stack := [], topIndex := 1 }

theorem world_well_formed : world.WF :=
  ⟨TransactionSuccessTest.world_well_formed.profile,
    TransactionSuccessTest.world_well_formed.sysvars,
    TransactionSuccessTest.world_well_formed.rent, builtinTable_wf _⟩

theorem program_registered : world.builtins programKey = some (.unmodelled programKey) := by
  rfl

theorem program_is_not_loader : programKey ≠ Ids.bpfLoaderUpgradeable := by
  decide

theorem explicit_tag_differs : suppliedTag ≠ programKey := by
  decide

theorem context_bounds :
    programAccount.WF ∧ initial.keys.Nodup ∧
    initial.keys.length = initial.accts.length ∧
    frame.programIdx < initial.keys.length ∧ frame.programIdx < initial.accts.length ∧
    initial.lamportSum < 2^128 ∧
    (initial.acct frame.programIdx).owner = Ids.nativeLoader ∧
    initial.ixSysvarIdx = none := by
  unfold Account.WF
  decide

theorem frame_has_no_accounts : frame.accounts = [] := rfl

theorem frame_flags_consistent : frame.FlagsConsistent := by
  simp [Frame.FlagsConsistent, frame]

theorem payload_length : payload.length = MAX_RETURN_DATA + 1 :=
  List.length_replicate

theorem payload_bounds :
    payload.length = 1025 ∧ MAX_RETURN_DATA < payload.length ∧
    payload.length < U64_LIMIT := by
  rw [payload_length]
  decide

theorem payload_nonempty : payload ≠ [] := by
  intro empty
  have length := payload_length
  rw [empty] at length
  simp only [List.length_nil, MAX_RETURN_DATA] at length
  omega

/-- A direct native call can set any represented tag and bytes. This proof has
no successful execution as a premise and does not borrow an instruction account. -/
theorem native_sets_return_data (W : World) (ts : TxState) (f : Frame)
    (programId : Pubkey) (data : Bytes) :
    Havoc W ts f (.ok (setNativeReturnData ts programId data)) :=
  Exec.havocReturnData programId data Exec.havocDone

/-- The native operation preserves arbitrary existing account state, counters,
touch flags and program-cache modifications. -/
theorem native_preserves_account_state (ts : TxState) (programId : Pubkey) (data : Bytes) :
    (setNativeReturnData ts programId data).keys = ts.keys ∧
    (setNativeReturnData ts programId data).accts = ts.accts ∧
    (setNativeReturnData ts programId data).lamportsDelta = ts.lamportsDelta ∧
    (setNativeReturnData ts programId data).resizeDelta = ts.resizeDelta ∧
    (setNativeReturnData ts programId data).touched = ts.touched ∧
    (setNativeReturnData ts programId data).modifiedPrograms = ts.modifiedPrograms :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem native_preserves_control_state (ts : TxState) (programId : Pubkey) (data : Bytes) :
    (setNativeReturnData ts programId data).stack = ts.stack ∧
    (setNativeReturnData ts programId data).trace = ts.trace ∧
    (setNativeReturnData ts programId data).topIndex = ts.topIndex :=
  ⟨rfl, rfl, rfl⟩

theorem native_tag_and_bytes (ts : TxState) (programId : Pubkey) (data : Bytes) :
    (setNativeReturnData ts programId data).returnData = (programId, data) := rfl

theorem instruction_pushed : push world.prof initial frame = .ok pushed := by
  rfl

theorem reset_before_native : running.returnData = (programKey, []) := rfl

theorem native_dispatched : dispatch world running frame = .builtin (.unmodelled programKey) := by
  rfl

theorem native_havoc : Havoc world running frame (.ok afterNative) :=
  native_sets_return_data world running frame suppliedTag payload

theorem native_executed : RunProgram world running frame (.ok afterNative) :=
  Exec.unmodelled native_dispatched program_is_not_loader native_havoc

theorem instruction_popped : afterProgram (.ok afterNative) = .ok post := by
  rfl

/-- The complete instruction succeeds through push, reset, direct native effect
and the checked pop. No account setter or nested invocation is needed. -/
theorem instruction_executed : ProcInstr world initial frame (.ok post) := by
  have execution : ProcInstr world initial frame (afterProgram (.ok afterNative)) :=
    Exec.run instruction_pushed native_executed
  simpa only [instruction_popped] using execution

theorem final_return_data : post.returnData = (suppliedTag, payload) := rfl

theorem final_accounts_unchanged :
    post.keys = initial.keys ∧ post.accts = initial.accts ∧
    post.lamportSum = initial.lamportSum ∧ post.lamportsDelta = 0 ∧
    post.resizeDelta = 0 ∧ post.touched = [] ∧
    post.modifiedPrograms = initial.modifiedPrograms :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem final_control_state :
    post.stack = [] ∧ post.trace = [⟨1, frame⟩] ∧ post.topIndex = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The same payload remains too large at the SBF syscall boundary, regardless
of the profile, cryptographic primitives or invocation state. -/
theorem sbf_rejects_same_payload (p : Profile) (P : Prims) (sv : Sysvars)
    (es : Option Pubkey → Nat) (c : InvCtx) (st : InvState) :
    sysStep p P sv es c st (.setReturnData payload) = .error .ProgramFailedToComplete := by
  simp only [sysStep, ite_eq_left payload_bounds.2.1]

/-- A closed successful native instruction with no instruction accounts, a
nonempty payload exceeding the SBF limit and an explicit non-current tag. -/
theorem native_return_data_witness :
    world.WF ∧ world.prof = mainnet ∧ frame.accounts = [] ∧
    ProcInstr world initial frame (.ok post) ∧
    post.returnData = (suppliedTag, payload) ∧ suppliedTag ≠ programKey ∧
    payload ≠ [] ∧ MAX_RETURN_DATA < payload.length ∧
    payload.length < U64_LIMIT ∧ post.accts = initial.accts :=
  ⟨world_well_formed, rfl, frame_has_no_accounts, instruction_executed,
    final_return_data, explicit_tag_differs, payload_nonempty,
    payload_bounds.2.1, payload_bounds.2.2, rfl⟩

end SolanalibTest.Runtime.NativeReturnDataTest
