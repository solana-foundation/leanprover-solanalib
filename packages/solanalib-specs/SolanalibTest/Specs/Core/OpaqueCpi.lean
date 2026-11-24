/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiWitness
public import Solanalib.Specs.Core.Versioning

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.OpaqueCpi

open Solanalib.Runtime Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

/-- Fixed source/build facts for the public CPI catalog controls. -/
def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def onchainTarget : List Versioning.TargetFact :=
  [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "abort"⟩]

def dependency (package version : String) : Versioning.Dependency :=
  ⟨package, version, registry⟩

/-- A request-level successful mock does not need an SDK invocation body. -/
theorem unit_success : run Witness.index Witness.before Witness.request
    (.returned () Witness.before) := ⟨Witness.success, rfl⟩

theorem raw_success : rawRun Witness.index Witness.before Witness.request
    (.returned 0 Witness.before) := ⟨rfl, unit_success⟩

/-- A nonzero raw return is not an on-chain CPI success. -/
theorem nonzero_is_rejected : ¬ rawRun Witness.index Witness.before Witness.request
    (.returned 7 Witness.before) := by
  intro returned
  have impossible : (7 : UInt64) = 0 := returned.1
  contradiction

/-- The external contract reports an instruction error after successful
preparation and synchronization. No invocation body is supplied. -/
def failingCallee : Index :=
  { Witness.index with callee := fun _ _ result => result = .error (.Custom 17) }

theorem callee_failure_terminal : run failingCallee Witness.before Witness.request
    (.terminated (.Custom 17)) :=
  Or.inr (.callee (prepared := Witness.success.prepared)
    (synchronized := Witness.before) rfl rfl rfl)

theorem callee_failure_no_return (after : InvState) :
    ¬ run failingCallee Witness.before Witness.request (.returned () after) := by
  rintro ⟨success, _⟩
  have impossible : (Except.ok success.returned : Except InstrError TxState) =
      .error (.Custom 17) := success.execute
  cases impossible

theorem callee_failure_no_raw_return (status : UInt64) (after : InvState) :
    ¬ rawRun failingCallee Witness.before Witness.request (.returned status after) :=
  fun returned => callee_failure_no_return after returned.2

theorem callee_failure_sdk_terminal : Sdk.run failingCallee Witness.sdkBefore
    Witness.signedArgs (.terminated (.Custom 17)) := Or.inr callee_failure_terminal

/-- An external runtime error is not a recoverable SDK Result::Err. The
positive terminal witness above uses the same otherwise valid call. -/
theorem callee_failure_no_sdk_error (error : ProgramError.Value) (after : Sdk.State) :
    ¬ Sdk.run failingCallee Witness.sdkBefore Witness.signedArgs
      (.returned (.error error) after) := by
  intro returned
  obtain ⟨_, borrows, rejected, _⟩ := Sdk.error_before_runtime returned
  have impossible : (true, Witness.sdkBefore.borrows) = (false, borrows) := rejected
  cases impossible

def seedError : CpiReq :=
  { Witness.request with
    ix := ⟨Ids.nativeLoader, [], []⟩
    signers := [List.replicate 17 []] }

/-- Seed failure precedes the forbidden-callee check. -/
theorem seeds_before_authorization : cpiPrepare Witness.index.profile
    Witness.index.primitives Witness.index.context Witness.before.ts seedError =
      .error .MaxSeedLengthExceeded := rfl

theorem seed_failure_terminal : run Witness.index Witness.before seedError
    (.terminated .MaxSeedLengthExceeded) :=
  Or.inr (.prepare seeds_before_authorization)

theorem seed_failure_no_return : ¬ run Witness.index Witness.before seedError
    (.returned () Witness.before) := no_return_of_prepare_error seeds_before_authorization

def lookupError : CpiReq :=
  { Witness.request with ix := ⟨Witness.programId,
      [⟨Witness.programId, 0, 1⟩, ⟨.ofNat 234, 0, 0⟩], []⟩ }

/-- Every transaction lookup occurs before privilege checking: a later missing
account wins over an earlier writable escalation. -/
theorem lookup_before_privilege : cpiPrepare Witness.index.profile
    Witness.index.primitives Witness.index.context Witness.before.ts lookupError =
      .error .MissingAccount := rfl

def privilegeError : CpiReq :=
  { lookupError with ix := ⟨Witness.programId, [⟨Witness.programId, 0, 1⟩], []⟩ }

theorem writable_escalation_rejected : cpiPrepare Witness.index.profile
    Witness.index.primitives Witness.index.context Witness.before.ts privilegeError =
      .error .PrivilegeEscalation := rfl

theorem pointer_array_rejected : cpiPrepare Witness.index.profile
    Witness.index.primitives Witness.index.context Witness.before.ts
    { Witness.request with infosBelowInput := false } = .error .ProgramFailedToComplete := rfl

def info : CpiAccountInfo :=
  ⟨.ofNat 31, 100, 200, 300, 400, 0, true, 0, .zero, []⟩

def first : Sdk.Account := ⟨info, ⟨0⟩, ⟨1⟩⟩
def sameKeyDistinctCells : Sdk.Account := ⟨info, ⟨2⟩, ⟨3⟩⟩

def free : Sdk.BorrowState :=
  ⟨List.replicate 4 ⟨(), Borrow.Policy.refCell 64⟩, []⟩

def lamportsBorrowed : Sdk.BorrowState :=
  { free with slots := [some ⟨⟨0⟩, .shared, 0, ()⟩] }

def dataBorrowed : Sdk.BorrowState :=
  { free with slots := [some ⟨⟨1⟩, .exclusive, 0, ()⟩] }

def writable : CpiMeta := ⟨info.key, 0, 1⟩
def readonly : CpiMeta := ⟨info.key, 0, 0⟩

/-- A later free AccountInfo with the same key cannot bypass the borrow conflict of the first alias.
No data probe follows the failed lamports probe. -/
theorem first_match_cannot_bypass_borrow :
    Sdk.preflight [first, sameKeyDistinctCells] lamportsBorrowed [writable] =
      (false, lamportsBorrowed) := rfl

/-- When data is borrowed, the completed lamports probe has already released
its temporary lease, leaving exactly its tombstone. -/
theorem lamports_before_data : Sdk.preflight [first] dataBorrowed [writable] =
    (false, { dataBorrowed with slots := dataBorrowed.slots ++ [none] }) := rfl

/-- Duplicate metas each trigger their required checks; none is deduplicated
by the local RefCell preflight of the SDK. -/
theorem duplicate_checks_retained : Sdk.preflight [first] free [writable, writable] =
    (true, { free with slots := [none, none, none, none] }) := rfl

theorem readonly_shared_allowed : Sdk.preflight [first] lamportsBorrowed [readonly] =
    (true, { lamportsBorrowed with slots := lamportsBorrowed.slots ++ [none, none] }) := rfl

def signed : Sdk.Args :=
  ⟨⟨⟨Ids.nativeLoader, [writable], [5]⟩, [first, first, sameKeyDistinctCells], true⟩,
    [[], [[], [1, 2]], [[1, 2]]]⟩

theorem ordered_duplicates_preserved : signed.runtimeRequest.infos = [info, info, info] := rfl

theorem nested_seeds_preserved : signed.runtimeRequest.signers =
    [[], [[], [1, 2]], [[1, 2]]] := rfl

theorem unsigned_empty_seeds : signed.toUnsignedArgs.signed.runtimeRequest.signers = [] := rfl

/-- Local borrow failure takes precedence even over a forbidden runtime callee. -/
theorem local_error_before_runtime : Sdk.run Witness.index
    ⟨Witness.before, lamportsBorrowed⟩ signed
    (.returned (.error .accountBorrowFailed) ⟨Witness.before, lamportsBorrowed⟩) :=
  Or.inr rfl

theorem changed_local_error_rejected : ¬ Sdk.run Witness.index
    ⟨Witness.before, lamportsBorrowed⟩ signed
    (.returned (.error .missingRequiredSignature) ⟨Witness.before, lamportsBorrowed⟩) := by
  intro returned
  have mismatch := (Sdk.error_before_runtime returned).1
  cases mismatch

/-- Metering can terminate before the local error is returned. -/
theorem local_metering_preserved : Sdk.run Witness.index
    ⟨Witness.before, lamportsBorrowed⟩ signed (.terminated .ComputationalBudgetExceeded) :=
  Or.inl rfl

end SolanalibTest.Specs.Core.OpaqueCpi
