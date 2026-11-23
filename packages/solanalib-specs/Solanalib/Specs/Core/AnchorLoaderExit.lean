/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoaderConstruct
public import Solanalib.Specs.Core.AnchorLifecycleRead
public import Solanalib.Specs.Core.AnchorCodec
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoaderExit

/-- The two source-local panic sites retain distinct reasons. -/
inductive Panic where
  | borrowFailed
  | writeZero
  deriving DecidableEq, Repr

/-- Exit does not inspect payload size or alignment. Only a reached short
write constructs an owned WriteZero diagnostic. `makeError` has the same
primitive boundary as `AnchorCodec.WriteTypes.makeError`: successful allocation
effects are retained, while diagnostic allocation failure is outside BINDINGS.
The other callbacks model unwrap formatting/panic and the drop of the owned error.
They act on Aux with the data guard of the caller held by `Owned.Focus.snd`. -/
structure Types extends AnchorLoader.ConstructorTypes where
  discriminator : Solanalib.Runtime.Bytes
  IoError : Type
  makeError : Callback.Run Aux Borsh.IoError IoError Empty Terminal
  /-- Borrows the error for `unwrap_failed`; it does not drop that owner.
  The Bool is the actual panic-abort profile. No normal return is possible. -/
  unwrapError : Callback.Run Aux (Bool × IoError) Empty (Panic ⊕ Unwind) (Panic ⊕ Terminal)
  /-- Drop the same error in the actual state reached by the unwind of unwrap. -/
  dropError : Callback.Run Aux IoError Unit (Panic ⊕ Unwind) (Panic ⊕ Terminal)
  doubleUnwind : Owned.DoubleUnwind Aux (Panic ⊕ Unwind) (Panic ⊕ Terminal)

abbrev Unwind (types : Types) := Panic ⊕ types.Unwind
abbrev Terminal (types : Types) := Panic ⊕ types.Terminal
abbrev Result (types : Types) := Except types.toBase.Error Unit

structure Args (types : Types) where
  profile : AccountInfo.Profile
  loader : AnchorLoader.Value types.Payload
  programId : Solanalib.Runtime.Pubkey

def Args.info {types : Types} (args : Args types) : AccountInfo.Args :=
  ⟨args.profile, args.loader.account.info⟩

/-- Retain the exact common helper outcome while naming its borrow panic in
the exit vocabulary. This changes neither values nor state. -/
def widen {types : Types} {Value : Type} :
    Outcome (AnchorAccount.World types.Aux) Value types.toBase.Unw types.toBase.Term →
      Outcome (AnchorAccount.World types.Aux) Value (Unwind types) (Terminal types)
  | .returned value after => .returned value after
  | .unwound (.inl _) after => .unwound (.inl .borrowFailed) after
  | .unwound (.inr reason) after => .unwound (.inr reason) after
  | .terminated (.inl _) => .terminated (.inl .borrowFailed)
  | .terminated (.inr reason) => .terminated (.inr reason)

def lift {types : Types} {Args Value : Type} (run : types.toBase.Run Args Value) :
    Callback.Run (AnchorAccount.World types.Aux) Args Value (Unwind types) (Terminal types) :=
  fun before args outcome => ∃ produced, run before args produced ∧ widen produced = outcome

/-- BpfWriter starts at offset zero, writes as much as fits, then write_all
reports WriteZero if the source discriminator was longer than the destination.
The existing BpfWriter step supplies the exact partial-copy bytes at cursor
zero; the subsequent error/unwrap composition is explicit below. -/
def writtenBytes (discriminator bytes : Solanalib.Runtime.Bytes) : Solanalib.Runtime.Bytes :=
  (AnchorCodec.writeStep ⟨bytes, 0⟩ discriminator).writer.bytes

theorem writtenBytes_length (discriminator bytes : Solanalib.Runtime.Bytes) :
    (writtenBytes discriminator bytes).length = bytes.length :=
  AnchorCodec.writeStep_length ⟨bytes, 0⟩ discriminator

/-- `write_all` constructs its actual WriteZero owner before `unwrap` borrows
it for formatting/panic. An unwind drops that owner before the data
guard of the caller can be released. A destructor unwind uses the explicit double-unwind
policy; a terminal exit runs no later cleanup and carries no after-state.
An empty reached callback relation has no fabricated finite outcome. -/
def writeZero (types : Types) :
    Callback.Run types.Aux Bool Empty (Unwind types) (Terminal types) :=
  fun before aborts outcome =>
    ∃ made, types.makeError before Borsh.writeZeroError made ∧
      match made with
      | .returned error after =>
        Owned.scope types.doubleUnwind [fun state result => types.dropError state error result]
          types.unwrapError after (aborts, error) outcome
      | .unwound impossible _ => nomatch impossible
      | .terminated reason => outcome = .terminated (.inr reason)

/-- The local copy happens first, while the exclusive guard is held. Short writes then run the
reached diagnostic dependencies with that same borrow state. Only an actual completed unwind
releases the guard, retaining the actual auxiliary state of the callbacks. Success invokes no
diagnostic callback. -/
def writeDiscriminator (types : Types) (args : Args types)
    (before : AnchorAccount.World types.Aux) (guard : Borrow.Guard) (bytes :
      Solanalib.Runtime.Bytes) :
    Outcome (AnchorAccount.World types.Aux) (Result types) (Unwind types) (Terminal types) → Prop :=
  fun outcome =>
    match Borrow.write before.1 guard (.data (writtenBytes types.discriminator bytes)) with
    | (.error _, _) => False
    | (.ok (), written) =>
      if bytes.length < types.discriminator.length then
        ∃ failed, (Owned.Focus.snd.lift (writeZero types))
          (written, before.2) args.profile.aborts failed ∧
          match failed with
          | .returned impossible _ => nomatch impossible
          | .unwound reason during =>
            match Borrow.release during.1 guard with
            | (.error _, _) => False
            | (.ok (), after) => outcome = .unwound reason (after, during.2)
          | .terminated reason => outcome = .terminated reason
      else match Borrow.release written guard with
        | (.error _, _) => False
        | (.ok (), after) => outcome = .returned (.ok ()) (after, before.2)

/-- Only the nonshort local writer has unconditional finite completion.
This hypothesis is local to this theorem, not a source or contract admission
gate. Short-path retention below uses actual diagnostic callback outcomes. -/
theorem write_complete {types : Types} (args : Args types)
    {before : AnchorAccount.World types.Aux} {guard : Borrow.Guard} {handle : Borrow.Handle}
    {generation : Nat} {policy : Borrow.Policy} {bytes : Solanalib.Runtime.Bytes}
    (live : before.1.resolve guard = some ⟨handle, .exclusive, generation, .whole⟩)
    (present : before.1.lookupCell handle = some ⟨.data bytes, policy⟩)
    (enough : types.discriminator.length ≤ bytes.length) :
    ∃ outcome, writeDiscriminator types args before guard bytes outcome := by
  let value := AccountInfo.Content.data (writtenBytes types.discriminator bytes)
  let written := (Borrow.write before.1 guard value).2
  have wrote : Borrow.write before.1 guard value = (.ok (), written) := by
    simp only [Borrow.write, live, ↓reduceIte, Borrow.replaceCell, present, written]
  have held : written.resolve guard = some ⟨handle, .exclusive, generation, .whole⟩ := by
    change (Borrow.write before.1 guard value).2.resolve guard = _
    rw [Borrow.write, live]
    simp only [↓reduceIte]
    simpa only [Borrow.State.resolve, Borrow.State.lookupSlot, Borrow.replaceCell_slots] using live
  dsimp only [value] at wrote
  have notShort : ¬ bytes.length < types.discriminator.length := by omega
  simp only [writeDiscriminator, wrote, notShort, ↓reduceIte, Borrow.release_live held]
  exact ⟨_, rfl⟩

/-- Every actual short diagnostic unwind retains its exact reason and Aux;
the caller releases the held guard only after the cleanup of the diagnostic error. -/
theorem write_short_unwound {types : Types} {args : Args types}
    {before : AnchorAccount.World types.Aux} {guard : Borrow.Guard} {bytes :
      Solanalib.Runtime.Bytes}
    {written after : AccountInfo.State} {reason : Unwind types} {aux : types.Aux}
    (copied : Borrow.write before.1 guard (.data (writtenBytes types.discriminator bytes)) =
      (.ok (), written))
    (short : bytes.length < types.discriminator.length)
    (called : writeZero types before.2 args.profile.aborts (.unwound reason aux))
    (released : Borrow.release written guard = (.ok (), after)) :
    writeDiscriminator types args before guard bytes (.unwound reason (after, aux)) := by
  simp only [writeDiscriminator, copied, short, ↓reduceIte]
  refine ⟨.unwound reason (written, aux), ⟨.unwound reason aux, called, rfl⟩, ?_⟩
  simp only [released]

/-- A reached diagnostic terminal is preserved without inventing a final
state or a guard/error destructor after that terminal. -/
theorem write_short_terminal {types : Types} {args : Args types}
    {before : AnchorAccount.World types.Aux} {guard : Borrow.Guard} {bytes :
      Solanalib.Runtime.Bytes}
    {written : AccountInfo.State} {reason : Terminal types}
    (copied : Borrow.write before.1 guard (.data (writtenBytes types.discriminator bytes)) =
      (.ok (), written))
    (short : bytes.length < types.discriminator.length)
    (called : writeZero types before.2 args.profile.aborts (.terminated reason)) :
    writeDiscriminator types args before guard bytes (.terminated reason) := by
  simp only [writeDiscriminator, copied, short, ↓reduceIte]
  exact ⟨.terminated reason, ⟨.terminated reason, called, rfl⟩, rfl⟩

/-- A short writer cannot return an ordinary Result error: unwrap never
returns. The separate checked-borrow error remains the ProgramError path. -/
theorem write_no_error {types : Types} {args : Args types}
    {before after : AnchorAccount.World types.Aux} {guard : Borrow.Guard}
    {bytes : Solanalib.Runtime.Bytes} {error : types.toBase.Error}
    (called : writeDiscriminator types args before guard bytes (.returned (.error error) after)) :
    False := by
  unfold writeDiscriminator at called
  split at called
  · exact called
  · split at called
    · obtain ⟨failed, _, continued⟩ := called
      cases failed with
      | returned impossible _ => nomatch impossible
      | unwound _ _ =>
        dsimp only at continued
        split at continued <;> cases continued
      | terminated _ => cases continued
    · split at called <;> cases called

/-- Checked mutable borrowing for the non-closed branch of the source. A normal
borrow error is boxed as ProgramError; an acquired guard reaches the writer. -/
def persist (types : Types) (before : AnchorAccount.World types.Aux) (args : Args types) :
    Outcome (AnchorAccount.World types.Aux) (Result types) (Unwind types) (Terminal types) → Prop :=
  fun outcome =>
    let (borrowed, during) := AccountInfo.tryBorrow .exclusive args.loader.account.info.data
      before.1
    match borrowed with
    | .error failure => lift (Callback.map Except.error
        (AnchorLifecycle.programError types.toBase failure)) (during, before.2) () outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) => writeDiscriminator types args (during, before.2) guard bytes outcome

/-- Exit first calls the Owner of the type. Only a matching program proceeds to
is_closed; only a non-closed account borrows and writes the discriminator.
Nothing writes the payload or checks its value. -/
def run (types : Types) :
    Callback.Run (AnchorAccount.World types.Aux) (Args types) (Result types)
      (Unwind types) (Terminal types) :=
  fun before args => Callback.bind
    (lift (AnchorAccount.widenCallback types.owner))
    (fun owner afterOwner outcome =>
      if owner = args.programId then
        Callback.bind (lift (AnchorLifecycle.isClosed types.ownerAt))
          (fun closed afterRead outcome => if closed then outcome = .returned (.ok ()) afterRead
            else persist types afterRead args outcome) afterOwner args.info outcome
      else outcome = .returned (.ok ()) afterOwner)
    before ()

/-- The two real reads are checked only at their source-reached prefixes.
Owner mismatch and already-closed accounts do not require an unused data read. -/
def Ready (types : Types) (before : AnchorAccount.World types.Aux) (args : Args types) : Prop :=
  ∀ owner afterOwner, types.owner before () (.returned owner afterOwner) →
    owner = args.programId →
      AnchorLifecycle.IsClosedReady types.ownerAt afterOwner args.info ∧
        ∀ afterRead, AnchorLifecycle.isClosed (Unwind := types.Unwind) (Terminal := types.Terminal)
          types.ownerAt afterOwner args.info (.returned false afterRead) →
            AccountInfo.DataBorrow.Ready .exclusive afterRead.1 args.loader.account.info.data

/-- A reached owner match has an actual is_closed return or panic outcome;
the field is used before a complete exit execution is assumed. -/
theorem isClosed_complete {types : Types} {before afterOwner : AnchorAccount.World types.Aux}
    {args : Args types} (ready : Ready types before args) {owner : Solanalib.Runtime.Pubkey}
    (called : types.owner before () (.returned owner afterOwner)) (same : owner = args.programId) :
    ∃ outcome, AnchorLifecycle.isClosed (Unwind := types.Unwind) (Terminal := types.Terminal)
      types.ownerAt afterOwner args.info outcome :=
  AnchorLifecycle.isClosed_exists types.ownerAt afterOwner args.info (ready owner afterOwner called
    same).1

/-- An actual writer outcome is retained through the reached Owner,
is_closed and acquisition prefixes. This does not assert termination of
arbitrary diagnostic callbacks and adds no readiness requirement on skips. -/
theorem write_retain {types : Types} {before afterOwner afterRead : AnchorAccount.World types.Aux}
    {args : Args types} {owner : Solanalib.Runtime.Pubkey}
    (owned : types.owner before () (.returned owner afterOwner)) (same : owner = args.programId)
    (read : AnchorLifecycle.isClosed (Unwind := types.Unwind) (Terminal := types.Terminal)
      types.ownerAt afterOwner args.info (.returned false afterRead))
    {guard : Borrow.Guard} {during : AccountInfo.State} {view : AccountInfo.View}
    {bytes : Solanalib.Runtime.Bytes}
    {outcome : Outcome (AnchorAccount.World types.Aux) (Result types) (Unwind types) (Terminal
      types)}
    (acquired : AccountInfo.tryBorrow .exclusive args.loader.account.info.data afterRead.1 =
      (.ok guard, during))
    (current : Borrow.current during guard = .ok (view, .data bytes))
    (wrote : writeDiscriminator types args (during, afterRead.2) guard bytes outcome) :
    run types before args outcome := by
  refine ⟨.returned owner afterOwner,
    ⟨.returned owner afterOwner, ⟨.returned owner afterOwner, owned, rfl⟩, rfl⟩, ?_⟩
  simp only [same, ↓reduceIte]
  refine ⟨.returned false afterRead, ⟨.returned false afterRead, read, rfl⟩, ?_⟩
  simpa only [Bool.false_eq_true, ↓reduceIte, persist, acquired, current] using wrote

/-- Owner mismatch returns without consulting the owner storage or data. -/
theorem owner_mismatch {types : Types} {before after : AnchorAccount.World types.Aux}
    {args : Args types} {owner : Solanalib.Runtime.Pubkey}
    (called : types.owner before () (.returned owner after)) (different : owner ≠ args.programId) :
    run types before args (.returned (.ok ()) after) := by
  refine ⟨.returned owner after,
    ⟨.returned owner after, ⟨.returned owner after, called, rfl⟩, rfl⟩, ?_⟩
  simp only [different, ↓reduceIte]

def family : Family where
  Index := Types
  State := fun types => AnchorAccount.World types.Aux
  Args := Args
  Value := Result
  Unwind := Unwind
  Terminal := Terminal
  contract := fun types => { requires := Ready types, post := run types }

def reference : FamilyRun family := run
theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ step
  exact step

/-- A concrete inhabited index; its no-op diagnostic observations are not
an assertion that source allocators or destructors have no effects. -/
def sample : Types where
  toConstructorTypes := AnchorLoader.constructorSample
  discriminator := [10]
  IoError := Borsh.IoError
  makeError := Callback.ofFunction fun before error => .returned error before
  unwrapError := Callback.ofFunction fun before (aborts, _) =>
    if aborts then .terminated (.inl .writeZero) else .unwound (.inl .writeZero) before
  dropError := Callback.ofFunction fun before _ => .returned () before
  doubleUnwind := fun _ _ _ reason => reason = .inl .writeZero
def sampleArgs : Args sample := ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩

theorem has_execution : FamilyHasExecution family reference sample := by
  let afterRead := (AccountInfo.observe .dataLen AccountInfo.sampleState AccountInfo.sampleInfo).2
  let during := (AccountInfo.tryBorrow .exclusive AccountInfo.sampleInfo.data afterRead).2
  let written := (Borrow.write during ⟨1, 0⟩ (.data [10, 20, 30])).2
  let after := (Borrow.release written ⟨1, 0⟩).2
  refine ⟨(AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), sampleArgs,
    .returned (.ok ()) (after, AnchorOwnedSamples.auxiliary), ?_, ?_⟩
  · intro owner afterOwner called same
    cases called
    refine ⟨?_, ?_⟩
    · intro _
      intro bad
      cases bad
    · intro afterRead called
      change (∃ produced, _ ∧ Outcome.map (fun length : Nat => length == 0) produced =
        .returned false afterRead) at called
      obtain ⟨produced, observed, mapped⟩ := called
      cases observed
      cases mapped
      trivial
  · refine ⟨.returned .zero _, ⟨.returned .zero _, ⟨.returned .zero _, rfl, rfl⟩, rfl⟩, ?_⟩
    refine ⟨.returned false (afterRead, AnchorOwnedSamples.auxiliary), ?_, rfl⟩
    exact ⟨.returned false _, ⟨.returned 3 _, rfl, rfl⟩, rfl⟩

end Solanalib.Specs.Core.AnchorLoaderExit
