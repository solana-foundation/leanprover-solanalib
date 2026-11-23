/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleRead
public import Solanalib.Specs.Core.AnchorLifecycleConstruct

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

/-- The actual serializer is passed a BpfWriter starting at offset zero over
the currently held whole mutable data slice. Its writes live in the shared
guard store; a returned error is not a rollback. -/
structure SerializeArgs (Payload : Type) where
  payload : Payload
  info : AccountInfo.Value
  guard : Borrow.Guard
  bytes : Solanalib.Runtime.Bytes
  position : Nat

structure ExitTypes extends Base where
  Payload : Type
  ownerAt : AccountInfo.OwnerAt Aux
  owner : Callback.Run (World Aux) Unit Solanalib.Runtime.Pubkey Unwind Terminal
  serialize : Callback.Run (World Aux) (SerializeArgs Payload)
    (Except (AnchorErrorOperations.Error errorStorage Program StringResource BoxResource) Unit)
      Unwind Terminal
  rc : AccountInfoRc.Ops (World Aux) Terminal

structure ExitArgs (kind : PayloadKind) (Payload : Type) where
  profile : AccountInfo.Profile
  wrapper : kind.constructor.Result Payload
  programId : Solanalib.Runtime.Pubkey

def ExitArgs.account {Payload : Type} : {kind : PayloadKind} → ExitArgs kind Payload →
  AnchorAccount.Account Payload
  | .account, args => args.wrapper
  | .interfaceAccount, args => args.wrapper.account

def ExitArgs.infoArgs {kind : PayloadKind} {Payload : Type} (args : ExitArgs kind Payload) :
  AccountInfo.Args :=
  ⟨args.profile, args.account.info⟩

def serializeAccount (types : ExitTypes) :
    types.toBase.Run (AnchorAccount.Account types.Payload × AccountInfo.Profile) (Except
      types.toBase.Error Unit) :=
  fun before (account, profile) outcome =>
    let (borrowed, during) := AccountInfo.tryBorrowMutData before.1 ⟨profile, account.info⟩
    match borrowed with
    | .error failure => Callback.map Except.error (programError types.toBase failure) (during,
      before.2) () outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) => AnchorEffects.withGuard guard
          (AnchorAccount.widenCallback types.serialize) (during, before.2)
          ⟨account.value, account.info, guard, bytes, 0⟩ outcome

/-- Only 0.27/0.29 create an extra local AccountInfo before borrowing mutably.
That local is dropped after the guard on every return/unwind of this scope. -/
def serializeScoped (cloneLocal : Bool) (types : ExitTypes) :
    types.toBase.Run (AnchorAccount.Account types.Payload × AccountInfo.Profile) (Except
      types.toBase.Error Unit) :=
  fun before (account, profile) outcome =>
    if cloneLocal then Callback.bind (cloneInfo types.toBase types.rc)
      (fun info afterClone => Owned.scope (noDoubleUnwind types.toBase)
        [dropInfo types.toBase types.rc info] (serializeAccount types) afterClone
        (⟨account.value, info⟩, profile)) before account.info outcome
    else serializeAccount types before (account, profile) outcome

def exitExpected (cloneLocal : Bool) (types : ExitTypes)
    (account : AnchorAccount.Account types.Payload) (profile : AccountInfo.Profile)
    (programId expected : Solanalib.Runtime.Pubkey) :
    types.toBase.Run Unit (Except types.toBase.Error Unit) :=
  fun before _ outcome =>
    if expected = programId then Callback.bind (isClosed types.ownerAt)
      (fun closed checked result =>
        if closed then result = .returned (.ok ()) checked
        else serializeScoped cloneLocal types checked (account, profile) result)
      before ⟨profile, account.info⟩ outcome
    else outcome = .returned (.ok ()) before

/-- Account obtains the expected owner from its trait callback. InterfaceAccount
uses its saved construction owner, not a fresh owner check or current owner. -/
def exit (kind : PayloadKind) (cloneLocal : Bool) (types : ExitTypes) :
    types.toBase.Run (ExitArgs kind types.Payload) (Except types.toBase.Error Unit) :=
  match kind with
  | .account => fun before args => Callback.bind (AnchorAccount.widenCallback types.owner)
      (fun expected after => exitExpected cloneLocal types args.wrapper args.profile args.programId
        expected after ())
      before ()
  | .interfaceAccount => fun before args =>
      exitExpected cloneLocal types args.wrapper.account args.profile args.programId
        args.wrapper.owner before ()

def SerializeReady (types : ExitTypes) (before : World types.Aux)
    (account : AnchorAccount.Account types.Payload) (profile : AccountInfo.Profile) : Prop :=
  (∃ bytes policy, before.1.lookupCell account.info.data = some ⟨.data bytes, policy⟩) ∧
    ∀ guard during, AccountInfo.tryBorrowMutData before.1 ⟨profile, account.info⟩ = (.ok guard,
      during) →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        MutableAdmissible guard (AnchorAccount.widenCallback types.serialize) (during, before.2)
          ⟨account.value, account.info, guard, bytes, 0⟩

def SerializeScopedReady (cloneLocal : Bool) (types : ExitTypes) (before : World types.Aux)
    (account : AnchorAccount.Account types.Payload) (profile : AccountInfo.Profile) : Prop :=
  if cloneLocal then
    ∀ info after, cloneInfo types.toBase types.rc before account.info (.returned info after) →
      SerializeReady types after ⟨account.value, info⟩ profile
  else SerializeReady types before account profile

def ExitExpectedReady (cloneLocal : Bool) (types : ExitTypes) (before : World types.Aux)
    (account : AnchorAccount.Account types.Payload) (profile : AccountInfo.Profile)
    (programId expected : Solanalib.Runtime.Pubkey) : Prop :=
  expected = programId →
    IsClosedReady types.ownerAt before ⟨profile, account.info⟩ ∧
      ∀ checked, isClosed (Unwind := types.Unwind) (Terminal := types.Terminal) types.ownerAt
        before ⟨profile, account.info⟩ (.returned false checked) →
        SerializeScopedReady cloneLocal types checked account profile

def ExitReady (kind : PayloadKind) (cloneLocal : Bool) (types : ExitTypes)
    (before : World types.Aux) (args : ExitArgs kind types.Payload) : Prop :=
  match kind, args with
  | .account, args => ∀ expected after,
      AnchorAccount.widenCallback types.owner before () (.returned expected after) →
        ExitExpectedReady cloneLocal types after args.wrapper args.profile args.programId expected
  | .interfaceAccount, args => ExitExpectedReady cloneLocal types before args.wrapper.account
      args.profile args.programId args.wrapper.owner

/-- The exact selected mutable data cell supplies a real serializer argument.
Each admitted finite callback exit has its state-preserving guard cleanup. -/
theorem SerializeReady.retain {types : ExitTypes} {before : World types.Aux}
    {account : AnchorAccount.Account types.Payload} {profile : AccountInfo.Profile}
    (ready : SerializeReady types before account profile)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowMutData before.1 ⟨profile, account.info⟩ = (.ok guard, during))
    {view : AccountInfo.View} {bytes : Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Except types.toBase.Error Unit) types.toBase.Unw
      types.toBase.Term}
    (called : AnchorAccount.widenCallback types.serialize (during, before.2)
      ⟨account.value, account.info, guard, bytes, 0⟩ produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard produced = some outcome ∧
      serializeAccount types before (account, profile) outcome := by
  have live := AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released, continued⟩ :=
    (ready.2 guard during acquired view bytes current).retain live called
  exact ⟨outcome, released, by simpa only [serializeAccount, acquired, current] using continued⟩

def exitFamily (kind : PayloadKind) (cloneLocal : Bool) : Family where
  Index := ExitTypes
  State := fun types => World types.Aux
  Args := fun types => ExitArgs kind types.Payload
  Value := fun types => Except types.toBase.Error Unit
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types =>
    { requires := ExitReady kind cloneLocal types, post := exit kind cloneLocal types }

def exitRun (kind : PayloadKind) (cloneLocal : Bool) : FamilyRun (exitFamily kind cloneLocal) :=
  exit kind cloneLocal

theorem exit_reference (kind : PayloadKind) (cloneLocal : Bool) :
    FamilyReference (exitFamily kind cloneLocal) (exitRun kind cloneLocal) := by
  intro _ _ _ _ _ called
  exact called

def exitSample (errors : AnchorErrorOperations.Storage) : ExitTypes where
  toBase := { Base.ofConstructor AnchorOwnedSamples.constructor with errorStorage := errors }
  Payload := Nat
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned .zero state
  serialize := Callback.ofFunction fun state _ => .returned (.ok ()) state
  rc := {
    cloneRc := Callback.ofFunction fun state _ => .returned () state
    dropRc := Callback.ofFunction fun state _ => .returned () state }

def exitSampleProgram : Solanalib.Runtime.Pubkey := ⟨List.replicate 32 1, by decide⟩

def exitSampleArgs : (kind : PayloadKind) → ExitArgs kind Nat
  | .account => ⟨AccountInfo.sampleProfile, ⟨7, AccountInfo.sampleInfo⟩, exitSampleProgram⟩
  | .interfaceAccount => ⟨AccountInfo.sampleProfile, ⟨⟨7, AccountInfo.sampleInfo⟩, .zero⟩,
    exitSampleProgram⟩

theorem exitSample_ne : (Solanalib.Runtime.Pubkey.zero : Solanalib.Runtime.Pubkey) ≠
  exitSampleProgram := by decide

/-- A legitimate foreign-owner bypass witnesses the universal family without
requiring an allocator or serializer execution. Positive serialization and
write/error/unwind cases are checked separately. -/
theorem exit_execution (kind : PayloadKind) (cloneLocal : Bool) (errors :
  AnchorErrorOperations.Storage) :
    FamilyHasExecution (exitFamily kind cloneLocal) (exitRun kind cloneLocal) (exitSample errors)
      := by
  let state := (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary)
  refine ⟨state, exitSampleArgs kind, .returned (.ok ()) state, ?_, ?_⟩
  · cases kind with
    | account =>
      intro expected after ⟨produced, called, widened⟩ equal
      cases called
      cases widened
      exact False.elim (exitSample_ne equal)
    | interfaceAccount => intro equal; exact False.elim (exitSample_ne equal)
  · cases kind with
    | account =>
      exact ⟨.returned .zero state, ⟨.returned .zero state, rfl, rfl⟩,
        by simp only [exitExpected, exitSampleArgs, exitSample_ne, ↓reduceIte]; rfl⟩
    | interfaceAccount =>
      change exitExpected cloneLocal (exitSample errors) ⟨(7 : Nat), AccountInfo.sampleInfo⟩
        AccountInfo.sampleProfile exitSampleProgram .zero state () (.returned (.ok ()) state)
      simp only [exitExpected, exitSample_ne, ↓reduceIte]

end Solanalib.Specs.Core.AnchorLifecycle
