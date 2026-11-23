/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoDataAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Admission

open AllocatedControl

/-- The first authority read is reached only after both actual initial
constructors returned their owned values. No later source outcome is assumed. -/
inductive AuthorityPrefix (types : Types) (initial : World types.Extra) (args : Onchain.Args) :
    Prepared types → World types.Extra → Prop
  | allocated {instruction : Instruction.OwnedValue types.MetaResource types.ByteResource}
      {infos : types.InfoResource} {built before : World types.Extra}
      (instructionBuilt : InstructionAllocated.run types.constructor initial (transferPlan args)
        (.returned (.ok instruction) built))
      (infosBuilt : initialInfos types args built (.returned (.ok infos) before)) :
      AuthorityPrefix types initial args ⟨instruction, infos⟩ before

/-- The validation borrow follows the actual successful source prefix up to
the Execute array. The mint clone is used in every helper argument thereafter. -/
inductive ValidationPrefix (types : Types) (initial : World types.Extra) (args : Onchain.Args) :
    Onchain.Args → Prepared types → AccountInfo.Value → World types.Extra → Prop
  | reached {transfer : Prepared types} {reference : DataRef} {programId validationKey :
    Solanalib.Runtime.Pubkey}
      {mintClone program validation : AccountInfo.Value}
      {instruction : Instruction.OwnedValue types.MetaResource types.ByteResource}
      {infos : types.InfoResource}
      {based minted cloned entered built before : World types.Extra}
      (baseReturned : base types args initial (.returned (.ok transfer) based))
      (mintReturned : beginMint types args based (.returned (.ok (reference, some programId))
        minted))
      (clonedMint : cloneInfo types args.mint minted (.returned (.ok mintClone) cloned))
      (hookEntered : hookEntry types { args with mint := mintClone } programId cloned
        (.returned (.ok (validationKey, program, some validation)) entered))
      (instructionBuilt : executePrelude types { args with mint := mintClone } programId
        validationKey entered
        (.returned (.ok instruction) built))
      (infosBuilt : executeInfos types { args with mint := mintClone } validation instruction built
        (.returned (.ok infos) before)) :
      ValidationPrefix types initial args { args with mint := mintClone } ⟨instruction, infos⟩
        validation before

/-- A source extra-entry loop prefix advances only after actual resolution
and append success. It does not require completion of the current entry. -/
inductive ExtraPrefix (types : Types) (deps : Dependencies types) (args : Onchain.Args)
    (execute : Prepared types) (slice : ExtraSlice) (entry : World types.Extra) :
    Nat → Nat → World types.Extra → Prop
  | start : ExtraPrefix types deps args execute slice entry slice.count 0 entry
  | next {remaining index : Nat} {before resolved after : World types.Extra} {item :
    Solanalib.Runtime.CpiMeta}
      (reached : ExtraPrefix types deps args execute slice entry (remaining + 1) index before)
      (resolution : resolveExtra types deps execute slice index before (.returned (.ok item)
        resolved))
      (appended : appendResolved types args execute item resolved (.returned (.ok ()) after)) :
      ExtraPrefix types deps args execute slice entry remaining (index + 1) after

/-- These are the five data-acquisition sites of ordinary fee=None preparation. -/
inductive BorrowKind where
  | authorityLength | authorityUnchecked | mint | validation | collection
  deriving DecidableEq

/-- The source checked/unchecked failure interpretation at each site. -/
def BorrowKind.checked : BorrowKind → Bool
  | .authorityLength | .authorityUnchecked => false
  | .mint | .validation | .collection => true

/-- Reachability stops before the selected acquisition. In particular the
collection site uses the forward prefix of the same explicit protocol, never a
completed collection or enclosing preparation result. -/
inductive BorrowSite (types : Types) (deps : Dependencies types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource types.Unwind
      types.Terminal)
    (initial : World types.Extra) (args : Onchain.Args) :
    BorrowKind → World types.Extra → AccountInfo.Value → Prop
  | authorityLength {prepared : Prepared types} {before : World types.Extra}
      (reached : AuthorityPrefix types initial args prepared before)
      (owned : types.ownerAt before.2 args.authority.ownerRef = token2022ProgramId ∨
        types.ownerAt before.2 args.authority.ownerRef = legacyProgramId) :
      BorrowSite types deps protocol initial args .authorityLength before args.authority
  | authorityUnchecked {prepared : Prepared types} {before recognized after : World types.Extra}
      (reached : AuthorityPrefix types initial args prepared before)
      (selected : isMultisig types args.authority before (.returned (.ok true) recognized))
      (written : clearAuthoritySigner types prepared.instruction.metas recognized (.returned (.ok
        ()) after)) :
      BorrowSite types deps protocol initial args .authorityUnchecked after args.authority
  | mint {prepared : Prepared types} {before : World types.Extra}
      (reached : base types args initial (.returned (.ok prepared) before)) :
      BorrowSite types deps protocol initial args .mint before args.mint
  | validation {helperArgs : Onchain.Args} {execute : Prepared types}
      {info : AccountInfo.Value} {before : World types.Extra}
      (reached : ValidationPrefix types initial args helperArgs execute info before) :
      BorrowSite types deps protocol initial args .validation before info
  | collection {helperArgs : Onchain.Args} {execute : Prepared types} {validation info :
    AccountInfo.Value}
      {validationBefore borrowed validated listed entry before : World types.Extra}
      {reference : DataRef} {slice : ExtraSlice} {remaining index position : Nat}
      {infos : List AccountInfo.Value} {acquired : List AllocatedCollect.Element} {calls : List Nat}
      (reached : ValidationPrefix types initial args helperArgs execute validation validationBefore)
      (validationBorrowed : borrow types.raise true validation validationBefore (.returned (.ok
        reference) borrowed))
      (checked : AllocatedTlv.validate types.discriminators types.doubleUnwind reference.read
        borrowed ()
        (.returned (.ok ()) validated))
      (selected : extraSlice types reference validated (.returned (.ok slice) listed))
      (entries : ExtraPrefix types deps helperArgs execute slice listed (remaining + 1) index entry)
      (current : types.infos.current entry execute.infos = some infos)
      (progress : AllocatedCollect.ForwardPrefix protocol (infoIterator types execute.infos
        infos.length)
        (AllocatedCollect.borrowElement types.raise) entry position acquired before calls)
      (within : position < infos.length)
      (read : (infoIterator types execute.infos infos.length).elementAt before position = some
        info) :
      BorrowSite types deps protocol initial args .collection before info

/-- Unlike checked tryBorrow, the getter treats a missing representation as
malformed. Its actual conflict and shared-limit errors remain source panics. -/
def GetterFailures (before : AccountInfo.State) (handle : Borrow.Handle) : Prop :=
  ∀ failure during, Borrow.acquire before handle .shared .whole = (.error failure, during) →
    failure = .conflict ∨ failure = .sharedLimit

/-- Protocol validity is needed only when an actual successful acquisition
retains a Ref across source providers. The complete authority getter needs
only its own current read and failure classification. A checked borrow error
imposes no unrelated store invariant or data-cell requirement. -/
def BorrowDomain (kind : BorrowKind) (before : AccountInfo.State) (info : AccountInfo.Value) : Prop
  :=
  AccountInfo.DataBorrow.Ready .shared before info.data ∧
    (kind ≠ .authorityLength → ∀ guard during,
      AccountInfo.tryBorrow .shared info.data before = (.ok guard, during) → before.Valid) ∧
    (kind = .authorityLength → GetterFailures before info.data)

/-- Input admission at precisely the reached local acquisition prefixes. -/
def BorrowReady (types : Types) (deps : Dependencies types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource types.Unwind
      types.Terminal)
    (initial : World types.Extra) (args : Onchain.Args) : Prop :=
  ∀ kind before info, BorrowSite types deps protocol initial args kind before info →
    BorrowDomain kind before.1 info

variable {types : Types} {deps : Dependencies types}
  {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource types.Unwind types.Terminal}
  {initial : World types.Extra} {args : Onchain.Args}

/-- Every actual reached successful acquisition supplies its current data,
the captured-length Ref, and the valid guard world needed by later callbacks. -/
theorem BorrowReady.acquired
    (ready : BorrowReady types deps protocol initial args)
    {kind : BorrowKind} {before : World types.Extra} {info : AccountInfo.Value}
    (reached : BorrowSite types deps protocol initial args kind before info)
    (retained : kind ≠ .authorityLength)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow .shared info.data before.1 = (.ok guard, during)) :
    ∃ bytes, borrow types.raise kind.checked info before
        (.returned (.ok ⟨guard, bytes.length⟩) (during, before.2)) ∧
      (⟨guard, bytes.length⟩ : DataRef).read (during, before.2) = some bytes ∧ during.Valid := by
  have domain := ready kind before info reached
  obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current domain.1 acquired
  have valid := AccountInfo.GuardCallback.tryBorrow_valid (domain.2.1 retained guard during
    acquired) .shared info.data
  refine ⟨bytes, ?_, ?_, ?_⟩
  · simp only [borrow, fromStep, Onchain.borrowData, acquired, current]
  · simp only [DataRef.read, current, ↓reduceIte]
  · simpa only [acquired] using valid

/-- Reached checked borrows always retain their actual success or ordinary
error. Neither provider termination nor a later completed helper is assumed. -/
theorem BorrowReady.checked_continue
    (ready : BorrowReady types deps protocol initial args)
    {kind : BorrowKind} {before : World types.Extra} {info : AccountInfo.Value}
    (reached : BorrowSite types deps protocol initial args kind before info)
    (checked : kind.checked = true) :
    ∃ result after, borrow types.raise true info before (.returned result after) := by
  cases acquired : AccountInfo.tryBorrow .shared info.data before.1 with
  | mk result during =>
    cases result with
    | error failure =>
      refine ⟨.error .AccountBorrowFailed, (during, before.2), ?_⟩
      simp only [borrow, fromStep, Onchain.borrowData, acquired, ↓reduceIte]
    | ok guard =>
      obtain ⟨bytes, borrowed, _, _⟩ := ready.acquired reached (by
        intro same
        cases same
        cases checked) acquired
      exact ⟨.ok ⟨guard, bytes.length⟩, (during, before.2), checked ▸ borrowed⟩

/-- The mint gate is connected directly to the earlier actual base prefix. -/
theorem BorrowReady.mint_continue
    (ready : BorrowReady types deps protocol initial args)
    {prepared : Prepared types} {before : World types.Extra}
    (based : base types args initial (.returned (.ok prepared) before)) :
    ∃ result after, borrow types.raise true args.mint before (.returned result after) :=
  ready.checked_continue (.mint based) rfl

/-- A successful new Ref immediately supports its actual local read and
checked drop, before any opaque provider is called. -/
theorem BorrowReady.acquired_read_scope
    (ready : BorrowReady types deps protocol initial args)
    {kind : BorrowKind} {before : World types.Extra} {info : AccountInfo.Value}
    (reached : BorrowSite types deps protocol initial args kind before info)
    (retained : kind ≠ .authorityLength)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow .shared info.data before.1 = (.ok guard, during)) :
    ∃ bytes : Bytes, withData types.raise types.doubleUnwind kind.checked info
      (fun reference => inspect reference.read) before
      (.returned (.ok bytes) ((Borrow.release during guard).2, before.2)) := by
  obtain ⟨bytes, borrowed, read, _⟩ := ready.acquired reached retained acquired
  have live := AccountInfo.GuardCallback.tryBorrow_live acquired
  have released := AccountInfo.GuardCallback.releaseOutcome_returned
    (Aux := types.Extra) (Unwind := types.Unwind) (Terminal := types.Terminal)
    (after := (during, before.2)) live (Except.ok bytes : Except Error Bytes)
  refine ⟨bytes, .returned (.ok ⟨guard, bytes.length⟩) (during, before.2), borrowed,
    .returned (.ok bytes) (during, before.2), ⟨bytes, read, rfl⟩, ?_⟩
  exact (AllocatedGuard.data_cleanup_iff types.doubleUnwind ⟨guard, bytes.length⟩ _ _).mpr released

private theorem getter_represented {before : AccountInfo.State} {info : AccountInfo.Value}
    (domain : BorrowDomain .authorityLength before info) :
    (AccountInfo.observe .dataLen before info).1 ≠ .malformed := by
  cases acquired : Borrow.acquire before info.data .shared .whole with
  | mk result during =>
    cases result with
    | error failure =>
      rcases domain.2.2 rfl failure during acquired with conflict | limit
      · subst failure
        simp [AccountInfo.observe, AccountInfo.Observation.handle, acquired]
      · subst failure
        simp [AccountInfo.observe, AccountInfo.Observation.handle, acquired]
    | ok guard =>
      have checked : AccountInfo.tryBorrow .shared info.data before = (.ok guard, during) := by
        simp [AccountInfo.tryBorrow, acquired, Except.mapError]
      obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current domain.1 checked
      have released := Borrow.release_live (AccountInfo.GuardCallback.tryBorrow_live checked)
      simp [AccountInfo.observe, AccountInfo.Observation.handle, acquired, current,
        AccountInfo.Observation.project, released]

/-- The selected authority getter reaches its actual length result or keeps
every actual panic-provider exit. The getter-specific error classification is
consumed here; no panic termination or successful borrow is postulated. -/
theorem BorrowReady.authority_length_continue
    (ready : BorrowReady types deps protocol initial args)
    {before : World types.Extra} {info : AccountInfo.Value}
    (reached : BorrowSite types deps protocol initial args .authorityLength before info) :
    match AccountInfo.observe .dataLen before.1 info with
    | (.value length, after) =>
        isMultisig types info before (.returned (.ok (length == multisigLength)) (after, before.2))
    | (.borrowFailed, after) => ∀ pending,
        types.raise (after, before.2) .borrowFailed pending →
          isMultisig types info before (Outcome.map (fun impossible : Empty => nomatch impossible)
            pending)
    | (.malformed, _) => False := by
  have represented := getter_represented (ready _ _ _ reached)
  have owned : types.ownerAt before.2 info.ownerRef = token2022ProgramId ∨
      types.ownerAt before.2 info.ownerRef = legacyProgramId := by
    cases reached with
    | authorityLength _ owned => exact owned
  have step : Onchain.isMultisig before.1
      { info with owner := types.ownerAt before.2 info.ownerRef } =
      match AccountInfo.observe .dataLen before.1 info with
      | (.value length, after) => (.success (length == multisigLength), after)
      | (.borrowFailed, after) => (.panic .borrowFailed, after)
      | (.malformed, after) => (.malformed, after) := by
    rcases owned with token | legacy
    · simp only [Onchain.isMultisig, token, bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]
      rfl
    · simp only [Onchain.isMultisig, legacy, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte]
      rfl
  cases observed : AccountInfo.observe .dataLen before.1 info with
  | mk result after =>
    cases result with
    | malformed => simp only [observed, ne_eq, not_true_eq_false] at represented
    | value length => simp only [isMultisig, fromStep, step, observed]
    | borrowFailed =>
      intro pending called
      simp only [isMultisig, fromStep, step, observed]
      exact ⟨pending, called, rfl⟩

/-- An unchecked borrow conflict reaches the supplied panic call and skips
the unacquired Ref scope. Every actual unwind or terminal exit is retained. -/
theorem unchecked_failure_continue {before : World types.Extra} {info : AccountInfo.Value}
    {failure : ProgramError.Value} {during : AccountInfo.State}
    (failed : AccountInfo.tryBorrow .shared info.data before.1 = (.error failure, during))
    {Value : Type} (body : DataRef → Run types Value)
    {pending : Outcome (World types.Extra) Empty types.Unwind types.Terminal}
    (called : types.raise (during, before.2) .borrowFailed pending) :
    withData types.raise types.doubleUnwind false info body before
      (Outcome.map (fun impossible : Empty => nomatch impossible) pending) := by
  refine ⟨Outcome.map (fun impossible : Empty => nomatch impossible) pending, ?_, ?_⟩
  · simp only [borrow, fromStep, Onchain.borrowData, failed, Bool.false_eq_true, ↓reduceIte]
    exact ⟨pending, called, rfl⟩
  · cases pending with
    | returned impossible _ => exact nomatch impossible
    | unwound _ _ | terminated _ => rfl

/-- The family-supplied successful-acquisition domain feeds the existing
primitive scope theorem. Its validity and current read are conclusions of the
reached site gate, not additional disconnected assumptions. -/
theorem BorrowReady.primitive_scope
    (ready : BorrowReady types deps protocol initial args) (admitted : Admitted types deps protocol)
    {kind : BorrowKind} {before : World types.Extra} {info : AccountInfo.Value}
    (reached : BorrowSite types deps protocol initial args kind before info)
    (retained : kind ≠ .authorityLength)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow .shared info.data before.1 = (.ok guard, during))
    {CallArgs Value : Type}
    {call : Callback.Run (World types.Extra) CallArgs Value types.Unwind types.Terminal}
    (selected : Primitive types call) {callArgs : CallArgs}
    {pending : Outcome (World types.Extra) Value types.Unwind types.Terminal}
    (called : call (during, before.2) callArgs pending) :
    ∃ bytes : Bytes, ∃ observed final,
      borrow types.raise kind.checked info before (.returned (.ok ⟨guard, bytes.length⟩) (during,
        before.2)) ∧
      bind (perform fun state => call state callArgs)
        (fun _ => inspect (⟨guard, bytes.length⟩ : DataRef).read) (during, before.2) observed ∧
      AccountInfo.GuardCallback.releaseOutcome guard observed = some final ∧
      withData types.raise types.doubleUnwind kind.checked info
        (fun reference => bind (perform fun state => call state callArgs)
          (fun _ => inspect reference.read)) before final := by
  obtain ⟨bytes, borrowed, read, valid⟩ := ready.acquired reached retained acquired
  obtain ⟨observed, final, continued, released, scopeRun⟩ :=
    admitted.read_cleanup selected valid read called
  exact ⟨bytes, observed, final, borrowed, continued, released,
    .returned (.ok ⟨guard, bytes.length⟩) (during, before.2), borrowed, scopeRun⟩

/-- Program rejection precedes every data-read site. It adds no data, scalar
width or store-validity condition to this source early-error branch. -/
theorem BorrowReady.of_instruction_error {error : Error}
    (rejected : Instruction.checkProgram (transferPlan args).programs (transferPlan args).programId
      = .error error) :
    BorrowReady types deps protocol initial args := by
  have noInstruction : ∀ instruction after,
      ¬ InstructionAllocated.run types.constructor initial (transferPlan args) (.returned (.ok
        instruction) after) := by
    intro instruction after called
    simp only [InstructionAllocated.run, rejected] at called
    cases called
  have noBase : ∀ prepared after, ¬ base types args initial (.returned (.ok prepared) after) := by
    rintro prepared after ⟨pending, built, rest⟩
    simp only [InstructionAllocated.run, rejected] at built
    cases built
    cases rest
  have noValidation : ∀ helperArgs execute info before,
      ¬ ValidationPrefix types initial args helperArgs execute info before := by
    intro helperArgs execute info before reached
    cases reached with
    | reached based _ _ _ _ _ => exact noBase _ _ based
  intro kind before info reached
  cases reached with
  | authorityLength progress _ =>
    cases progress with
    | allocated built _ => exact False.elim (noInstruction _ _ built)
  | authorityUnchecked progress _ _ =>
    cases progress with
    | allocated built _ => exact False.elim (noInstruction _ _ built)
  | mint based => exact False.elim (noBase _ _ based)
  | validation reached => exact False.elim (noValidation _ _ _ _ reached)
  | collection reached _ _ _ _ _ _ _ _ => exact False.elim (noValidation _ _ _ _ reached)

end Solanalib.Specs.Core.Token.OnchainAllocated.Admission
