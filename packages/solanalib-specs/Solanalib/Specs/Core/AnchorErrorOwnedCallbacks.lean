/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedContracts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

/-- Owned receiver and the two operands of the consumed tuple. Their mathematical
types may themselves be stable resource handles in the ambient state. -/
structure ValuesArgs (BoxResource Left Right : Type) where
  /-- Receiver moves into the return value or into unwind cleanup. -/
  error : Error BoxResource
  /-- First tuple field: converted first and dropped first. -/
  left : Left
  /-- Second tuple field: converted second and dropped second. -/
  right : Right

/-- The two actual ToString calls and individual operand destructors.
Conversions return owned String identities, not snapshots of their text.
All state-bearing outcomes retain their actual ambient effects. -/
structure ValuesCallbacks (State StringResource Left Right Unwind Terminal : Type) where
  /-- First borrowed ToString invocation. -/
  left : Callback.Run State Left StringResource Unwind Terminal
  /-- Second borrowed ToString invocation. -/
  right : Callback.Run State Right StringResource Unwind Terminal
  /-- The destructor of the first tuple field, including its own finite unwind effects. -/
  dropLeft : Callback.Run State Left Unit Unwind Terminal
  /-- The destructor of the second tuple field, after the first field has been consumed. -/
  dropRight : Callback.Run State Right Unit Unwind Terminal
  /-- Explicit terminal-only policy for an unwind during unwind cleanup. -/
  double : Owned.DoubleUnwind State Unwind Terminal

variable {State StringResource BoxResource Left Right Unwind Terminal : Type}

/-- The held Box and explicitly retained Strings keep their current contents.
Other String/Box resources and the rest of the ambient state may change. -/
def HeldFrame (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) (strings : List StringResource) (before after : State) : Prop :=
  ops.currentBox after error.resource = ops.currentBox before error.resource ∧
    ∀ resource ∈ strings, ops.currentString after resource = ops.currentString before resource

/-- Frame on the actual state-bearing outcome of a callback. A returned String is
live and disjoint from the held Strings of the caller. It may have been transferred
from captured storage; liveness does not itself establish that ownership
transfer. Terminal exits carry no invented final state. -/
def StringFrame (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) (strings : List StringResource) (before : State) :
    Outcome State StringResource Unwind Terminal → Prop
  | .returned resource after => HeldFrame ops error strings before after ∧
      (∃ text, ops.currentString after resource = some text) ∧
      resource ∉ strings
  | .unwound _ after => HeldFrame ops error strings before after
  | .terminated _ => True

/-- Operand cleanup must respect the still-owned error. This says nothing
about other captured state or about whether the destructor returns. -/
def DropFrame (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) (strings : List StringResource) (before : State) :
    Outcome State Unit Unwind Terminal → Prop
  | .returned _ after | .unwound _ after => HeldFrame ops error strings before after
  | .terminated _ => True

/-- A fixed-source String destructor in the enclosing callback vocabulary. -/
def dropStringLift (ops : Ops State StringResource BoxResource Terminal)
    (resource : StringResource) : Owned.DropAction State Unwind Terminal :=
  fun before outcome => lift ops.dropString before resource outcome

/-- Replacing a comparison moves the two new String identities into the
existing Box, after dropping the owned fields of the old comparison. -/
def Payload.withValues (left right : StringResource) :
    Payload StringResource → Payload StringResource
  | .anchor value => .anchor { value with compared := some (.values left right) }
  | .program value => .program { value with compared := some (.values left right) }

/-- Source assignment once both conversions have returned. Its post-drop
payload lookup observes the actual state, and it never allocates another Box. -/
def replaceValues (ops : Ops State StringResource BoxResource Terminal) :
    Callback.Run State (Error BoxResource × StringResource × StringResource)
      (Error BoxResource) Empty Terminal :=
  fun before (error, left, right) outcome =>
    ∃ payload, ops.currentBox before error.resource = some payload ∧
      Callback.bind (dropStrings ops (comparedStrings payload.compared))
        (fun _ afterDrops final => ∃ actual,
          ops.currentBox afterDrops error.resource = some actual ∧
          ∃ after, ops.writeBox afterDrops error.resource (actual.withValues left right) = some
            after ∧
            final = .returned error after) before () outcome

/-- Evaluate the tuple RHS left to right. A second-conversion unwind first
drops the completed first String. A terminal conversion performs no cleanup. -/
def valuesBody (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right) :
    Callback.Run State Unit (Error BoxResource) Unwind Terminal :=
  fun before _ => Callback.bind callbacks.left
    (fun left middle => Callback.bind
      (Owned.protect callbacks.double [dropStringLift ops left] callbacks.right)
      (fun right actual => lift (replaceValues ops) actual (args.error, left, right))
      middle args.right)
    before args.left

/-- An operand destructor is checked only at an actual cleanup entry reached
from this call. The prefix is empty for the left operand and contains its drop
for the right operand. Partial-RHS cleanup is already included in valuesBody.
An unwind during unwind cleanup, a terminal exit or a divergent prefix supplies
no later destructor entry. This predicate does not restrict the run relation. -/
def valuesDropEntry (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right)
    (priorDrops : List (Owned.DropAction State Unwind Terminal)) (initial before : State) : Prop :=
  ∃ pending entry, valuesBody ops callbacks args initial () pending ∧
    Owned.cleanup callbacks.double priorDrops pending entry ∧
    match entry with
    | .returned _ actual | .unwound _ actual => before = actual
    | .terminated _ => False

/-- Source ownership interpretation for one admitted initial state. Borrowed
conversions and operand destructors frame the error only at their reachable
call sites. This permits operands to own disjoint String resources that their
destructors retire; impossible aliasing states are not additional obligations.
Every outcome at a reached site must satisfy the frame, including unwinding
effects. The raw callback and cleanup relations retain all their outcomes. -/
structure ValuesCallbacks.Admissible
    (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right) (initial : State) : Prop where
  /-- First conversion preserves the resources of the receiver of this call. -/
  left : ∀ payload outcome,
    ops.currentBox initial args.error.resource = some payload → payload.Ready ops initial →
    callbacks.left initial args.left outcome → StringFrame ops args.error payload.strings initial
      outcome
  /-- The second conversion preserves the result of each actual first return. -/
  right : ∀ payload retained afterLeft outcome,
    ops.currentBox initial args.error.resource = some payload → payload.Ready ops initial →
    callbacks.left initial args.left (.returned retained afterLeft) →
    callbacks.right afterLeft args.right outcome →
      StringFrame ops args.error (retained :: payload.strings) afterLeft outcome
  /-- The first operand frames the held error when its scope cleanup begins. -/
  dropLeft : ∀ before payload outcome,
    valuesDropEntry ops callbacks args [] initial before →
    ops.currentBox before args.error.resource = some payload → payload.Ready ops before →
    callbacks.dropLeft before args.left outcome → DropFrame ops args.error payload.strings before
      outcome
  /-- The second operand is checked after an actual first-operand drop,
  including its unwind state when no earlier unwind was pending. -/
  dropRight : ∀ before payload outcome,
    valuesDropEntry ops callbacks args
      [fun state result => callbacks.dropLeft state args.left result] initial before →
    ops.currentBox before args.error.resource = some payload → payload.Ready ops before →
    callbacks.dropRight before args.right outcome → DropFrame ops args.error payload.strings before
      outcome

/-- A normal body return followed by the actual returned destructor prefix.
An unwinding body or earlier unwinding destructor supplies no entry here. This
selects proof obligations only; it does not restrict callback or cleanup runs. -/
def valuesReturnedDropEntry (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right)
    (priorDrops : List (Owned.DropAction State Unwind Terminal)) (initial before : State) : Prop :=
  ∃ result afterBody, valuesBody ops callbacks args initial () (.returned result afterBody) ∧
    Owned.DropReturns priorDrops afterBody before

/-- Exactly the callback frames used by the normal returned-Ready
postcondition of the family. No frame is required for an unwind, terminal exit, or destructor
reached from an unwinding body. Broader source ownership obligations are
separate from this condition on actual returned calls. -/
structure ValuesCallbacks.ReturnedAdmissible
    (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right) (initial : State) : Prop where
  /-- A returned first conversion preserves the receiver resources of this call. -/
  left : ∀ payload resource after,
    ops.currentBox initial args.error.resource = some payload → payload.Ready ops initial →
    callbacks.left initial args.left (.returned resource after) →
      StringFrame (Unwind := Unwind) ops args.error payload.strings initial (.returned resource
        after)
  /-- A returned second conversion also preserves the actual first result. -/
  right : ∀ payload retained afterLeft resource after,
    ops.currentBox initial args.error.resource = some payload → payload.Ready ops initial →
    callbacks.left initial args.left (.returned retained afterLeft) →
    callbacks.right afterLeft args.right (.returned resource after) →
      StringFrame (Unwind := Unwind) ops args.error (retained :: payload.strings)
        afterLeft (.returned resource after)
  /-- The first returned operand drop frames the current error of the normal body. -/
  dropLeft : ∀ before payload after,
    valuesReturnedDropEntry ops callbacks args [] initial before →
    ops.currentBox before args.error.resource = some payload → payload.Ready ops before →
    callbacks.dropLeft before args.left (.returned () after) →
      HeldFrame ops args.error payload.strings before after
  /-- The second returned operand drop follows the actual first normal drop. -/
  dropRight : ∀ before payload after,
    valuesReturnedDropEntry ops callbacks args
      [fun state result => callbacks.dropLeft state args.left result] initial before →
    ops.currentBox before args.error.resource = some payload → payload.Ready ops before →
    callbacks.dropRight before args.right (.returned () after) →
      HeldFrame ops args.error payload.strings before after

/-- An independently established all-outcome source frame supplies the smaller
returned-path condition used by the owned family. -/
theorem ValuesCallbacks.Admissible.returned
    {ops : Ops State StringResource BoxResource Terminal}
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial : State}
    (frames : callbacks.Admissible ops args initial) :
    callbacks.ReturnedAdmissible ops args initial := by
  have entry : ∀ priorDrops before,
      valuesReturnedDropEntry ops callbacks args priorDrops initial before →
      valuesDropEntry ops callbacks args priorDrops initial before := by
    rintro priorDrops before ⟨result, afterBody, body, trace⟩
    exact ⟨.returned result afterBody, .returned result before, body,
      trace.cleanup_returned callbacks.double result, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro payload resource after present ready run
    exact frames.left payload (.returned resource after) present ready run
  · intro payload retained afterLeft resource after present ready first run
    exact frames.right payload retained afterLeft (.returned resource after) present ready first run
  · intro before payload after reached present ready run
    exact frames.dropLeft before payload (.returned () after)
      (entry _ _ reached) present ready run
  · intro before payload after reached present ready run
    exact frames.dropRight before payload (.returned () after)
      (entry _ _ reached) present ready run

/-- The scope of a function body whose normal result has been moved into the
return place before the remaining locals of the scope (`locals`) drop, `retained`
being the resources the result owns. Unwind protection releases `retained`
when the body itself unwinds. If, after a normal body result, one of the destructors of the
locals unwinds, the drop semantics of the language also release the
return place, but rustc does not drop it (rust-lang/rust#47949, observed with
rustc 1.97.0-nightly 2026-04-30 at every optimization level): its resources
are then left live. On exactly that path both outcomes are admitted; every
other path is `protect retained (scope locals body)`. -/
def protectReturnPlace {Args Value : Type} (double : Owned.DoubleUnwind State Unwind Terminal)
    (retained locals : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal) :
    Callback.Run State Args Value Unwind Terminal :=
  fun before args final =>
    Owned.protect double retained (Owned.scope double locals body) before args final ∨
    ∃ value returned, body before args (.returned value returned) ∧
      ∃ reason after, Owned.cleanup double locals (.returned value returned) (.unwound reason
        after) ∧
        final = .unwound reason after

/-- Every protected-scope outcome remains admitted. -/
theorem protectReturnPlace_of_protect {Args Value : Type}
    {double : Owned.DoubleUnwind State Unwind Terminal}
    {retained locals : List (Owned.DropAction State Unwind Terminal)}
    {body : Callback.Run State Args Value Unwind Terminal} {before : State} {args : Args}
    {final : Outcome State Value Unwind Terminal}
    (run : Owned.protect double retained (Owned.scope double locals body) before args final) :
    protectReturnPlace double retained locals body before args final := Or.inl run

/-- The rust-lang/rust#47949 outcome: after a normal body result, a locals
cleanup that unwinds leaves the retained resources live, in its actual state. -/
theorem protectReturnPlace_leak {Args Value : Type}
    {double : Owned.DoubleUnwind State Unwind Terminal}
    {retained locals : List (Owned.DropAction State Unwind Terminal)}
    {body : Callback.Run State Args Value Unwind Terminal} {before returned after : State} {args :
      Args}
    {value : Value} {reason : Unwind}
    (called : body before args (.returned value returned))
    (cleaned : Owned.cleanup double locals (.returned value returned) (.unwound reason after)) :
    protectReturnPlace double retained locals body before args (.unwound reason after) :=
  Or.inr ⟨value, returned, called, reason, after, cleaned, rfl⟩

/-- Normal returns are exactly those of the protected scope. -/
theorem protectReturnPlace_returned_iff {Args Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (retained locals : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal) (before after : State) (args : Args)
    (value : Value) :
    protectReturnPlace double retained locals body before args (.returned value after) ↔
      Owned.protect double retained (Owned.scope double locals body) before args (.returned value
        after) := by
  constructor
  · rintro (run | ⟨_, _, _, _, _, _, impossible⟩)
    · exact run
    · cases impossible
  · exact Or.inl

/-- Terminal exits are exactly those of the protected scope. -/
theorem protectReturnPlace_terminated_iff {Args Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (retained locals : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal) (before : State) (args : Args)
    (reason : Terminal) :
    protectReturnPlace (Value := Value) double retained locals body before args (.terminated
      reason) ↔
      Owned.protect double retained (Owned.scope double locals body) before args (.terminated
        reason) := by
  constructor
  · rintro (run | ⟨_, _, _, _, _, _, impossible⟩)
    · exact run
    · cases impossible
  · exact Or.inl

/-- Without a normal body result the return-place alternative is unreachable:
every outcome is exactly one of the protected scope. -/
theorem protectReturnPlace_iff_of_no_return {Args Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (retained locals : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal) (before : State) (args : Args)
    (never : ∀ value returned, ¬ body before args (.returned value returned))
    (final : Outcome State Value Unwind Terminal) :
    protectReturnPlace double retained locals body before args final ↔
      Owned.protect double retained (Owned.scope double locals body) before args final := by
  constructor
  · rintro (run | ⟨value, returned, called, _⟩)
    · exact run
    · exact absurd called (never value returned)
  · exact Or.inl

/-- Complete with_values: returned Strings enter the current Box, tuple fields
drop left then right, and the same Box moves out. During conversion unwind the
incomplete RHS is cleaned before the tuple parameters, then self. The receiver
moves into the return place before the operand tuple drops: if an operand drop
starts unwinding after assignment, self cleanup either sees the updated payload
or, as rustc compiles it (rust-lang/rust#47949), never runs, leaving the Box
and its Strings live (`protectReturnPlace`). Double unwind is terminal through
the supplied policy; no terminal runs later cleanup. These are model steps,
not Rust permission or body proofs. -/
def withValues (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal) :
    Callback.Run State (ValuesArgs BoxResource Left Right) (Error BoxResource) Unwind Terminal :=
  fun before args outcome => ∃ payload, ops.currentBox before args.error.resource = some payload ∧
    protectReturnPlace callbacks.double [dropErrorLift ops args.error]
      [fun state result => callbacks.dropLeft state args.left result,
       fun state result => callbacks.dropRight state args.right result]
      (valuesBody ops callbacks args) before () outcome

/-- A cleanup returning normally must have started with that exact return
value, and every retained destructor must have returned in the given order. -/
theorem cleanup_returned_origin {Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    {drops : List (Owned.DropAction State Unwind Terminal)}
    {pending : Outcome State Value Unwind Terminal} {value : Value} {after : State}
    (run : Owned.cleanup double drops pending (.returned value after)) :
    ∃ before, pending = .returned value before ∧ Owned.DropReturns drops before after := by
  induction drops generalizing pending with
  | nil =>
    cases run
    exact ⟨_, rfl, .nil _⟩
  | cons action rest induction =>
    cases pending with
    | terminated _ =>
      have impossible := (Owned.cleanup_terminated double (action :: rest) _ _).mp run
      cases impossible
    | returned original before =>
      obtain ⟨intermediate, dropped, remaining⟩ := run
      cases intermediate with
      | terminated _ => cases remaining
      | unwound _ _ =>
        obtain ⟨_, impossible, _⟩ := induction remaining
        cases impossible
      | returned acknowledgement middle =>
        cases acknowledgement
        obtain ⟨actual, equal, tail⟩ := induction remaining
        cases equal
        exact ⟨before, rfl, .cons action rest before middle after dropped tail⟩
    | unwound reason before =>
      obtain ⟨intermediate, _, remaining⟩ := run
      cases intermediate with
      | terminated _ => cases remaining
      | unwound _ _ =>
        obtain ⟨_, _, impossible⟩ := remaining
        cases impossible
      | returned acknowledgement _ =>
        cases acknowledgement
        obtain ⟨_, impossible, _⟩ := induction remaining
        cases impossible

/-- Unwind protection cannot convert any unwinding or terminal body into a
normal return. A normal body transfers its value without running those drops. -/
theorem protect_returned_iff {Args Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal)
    (before after : State) (args : Args) (value : Value) :
    Owned.protect double drops body before args (.returned value after) ↔
      body before args (.returned value after) := by
  constructor
  · rintro ⟨pending, called, finished⟩
    cases pending with
    | returned actual final => cases finished; exact called
    | unwound _ _ =>
      obtain ⟨_, impossible, _⟩ := cleanup_returned_origin double finished
      cases impossible
    | terminated _ =>
      have impossible := (Owned.onUnwind_terminated double drops _ _).mp finished
      cases impossible
  · intro called
    exact ⟨.returned value after, called, rfl⟩

/-- Scope cleanup keeps the exact body return value and records a normal
destructor trace; it never silently discards an unwind. -/
theorem scope_returned_iff {Args Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal)
    (before after : State) (args : Args) (value : Value) :
    Owned.scope double drops body before args (.returned value after) ↔
      ∃ middle, body before args (.returned value middle) ∧ Owned.DropReturns drops middle after :=
        by
  constructor
  · rintro ⟨pending, called, finished⟩
    obtain ⟨middle, equal, trace⟩ := cleanup_returned_origin double finished
    cases equal
    exact ⟨middle, called, trace⟩
  · rintro ⟨middle, called, trace⟩
    exact ⟨.returned value middle, called, trace.cleanup_returned double value⟩

/-- Assignment returns precisely the consumed receiver identity. -/
theorem replaceValues_identity (ops : Ops State StringResource BoxResource Terminal)
    {before after : State} {error result : Error BoxResource} {left right : StringResource}
    (run : replaceValues ops before (error, left, right) (.returned result after)) :
    result = error := by
  obtain ⟨_, _, intermediate, _, remaining⟩ := run
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned _ _ =>
    obtain ⟨_, _, _, _, returned⟩ := remaining
    cases returned
    rfl

/-- Every normally completed with_values execution returns the same Box
identity, after both actual conversions and both operand destructors. -/
theorem withValues_identity (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    {before after : State} {args : ValuesArgs BoxResource Left Right} {result : Error BoxResource}
    (run : withValues ops callbacks before args (.returned result after)) :
    result = args.error := by
  obtain ⟨_, _, guarded⟩ := run
  have cleaned := (protect_returned_iff _ _ _ _ _ _ _).mp
    ((protectReturnPlace_returned_iff _ _ _ _ _ _ _ _).mp guarded)
  obtain ⟨middle, body, _⟩ := (scope_returned_iff _ _ _ _ _ _ _).mp cleaned
  obtain ⟨first, _, next⟩ := body
  cases first with
  | unwound _ _ | terminated _ => cases next
  | returned left actual =>
    obtain ⟨second, _, assignment⟩ := next
    cases second with
    | unwound _ _ | terminated _ => cases assignment
    | returned right final =>
      obtain ⟨exit, assigned, equal⟩ := assignment
      cases exit with
      | unwound impossible _ => nomatch impossible
      | terminated _ => cases equal
      | returned value state =>
        cases equal
        exact replaceValues_identity ops assigned


/-- A normally returning assignment preserves the variant and all noncomparison
resource descriptors of the actual Box, for Anchor and Program errors alike. -/
theorem replaceValues_payload (ops : Ops State StringResource BoxResource Terminal)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    (store_current : ∀ before resource payload after,
      ops.writeBox before resource payload = some after →
        ops.currentBox after resource = some payload)
    {before after : State} {error result : Error BoxResource}
    {left right : StringResource} {payload : Payload StringResource}
    (present : ops.currentBox before error.resource = some payload)
    (run : replaceValues ops before (error, left, right) (.returned result after)) :
    result = error ∧ ops.currentBox after error.resource = some (payload.withValues left right) :=
      by
  obtain ⟨actual, observed, intermediate, dropped, remaining⟩ := run
  have same : actual = payload := Option.some.inj (observed.symm.trans present)
  subst actual
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned acknowledgement middle =>
    cases acknowledgement
    obtain ⟨next, readable, final, stored, returned⟩ := remaining
    have boxes := dropStrings_boxes drop_boxes dropped error.resource
    have same : next = payload := Option.some.inj (readable.symm.trans (boxes.trans present))
    subst next
    cases returned
    exact ⟨rfl, store_current _ _ _ _ stored⟩

/-- A normal with_values result has two real normal ToString calls, a real
same-Box assignment, and both normal operand drops in source order. The retained
intermediate states make the sequencing available to downstream model proofs. -/
theorem withValues_returned_trace (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    {before after : State} {args : ValuesArgs BoxResource Left Right} {result : Error BoxResource}
    (run : withValues ops callbacks before args (.returned result after)) :
    ∃ left afterLeft right afterRight afterAssignment,
      callbacks.left before args.left (.returned left afterLeft) ∧
      callbacks.right afterLeft args.right (.returned right afterRight) ∧
      replaceValues ops afterRight (args.error, left, right) (.returned result afterAssignment) ∧
      Owned.DropReturns
        [fun state outcome => callbacks.dropLeft state args.left outcome,
         fun state outcome => callbacks.dropRight state args.right outcome] afterAssignment after
           := by
  obtain ⟨_, _, guarded⟩ := run
  have cleaned := (protect_returned_iff _ _ _ _ _ _ _).mp
    ((protectReturnPlace_returned_iff _ _ _ _ _ _ _ _).mp guarded)
  obtain ⟨middle, body, drops⟩ := (scope_returned_iff _ _ _ _ _ _ _).mp cleaned
  obtain ⟨first, firstCalled, next⟩ := body
  cases first with
  | unwound _ _ | terminated _ => cases next
  | returned left actual =>
    obtain ⟨second, secondCalled, assignment⟩ := next
    cases second with
    | unwound _ _ | terminated _ => cases assignment
    | returned right final =>
      have rightCalled := (protect_returned_iff _ _ _ _ _ _ _).mp secondCalled
      obtain ⟨exit, assigned, equal⟩ := assignment
      cases exit with
      | unwound impossible _ => nomatch impossible
      | terminated _ => cases equal
      | returned value state =>
        cases equal
        exact ⟨left, actual, right, final, _, firstCalled, rightCalled, assigned, drops⟩

/-- Replacing comparison values retains the noncomparison descriptors and
appends the two newly owned Strings in tuple order. -/
theorem Payload.withValues_strings (payload : Payload StringResource) (left right : StringResource)
  :
    (payload.withValues left right).strings = payload.retainedStrings ++ [left, right] := by
  cases payload <;>
    simp [Payload.withValues, Payload.strings, Payload.retainedStrings, comparedStrings]

/-- The held footprint transports initialized, distinct String fields through
an actual callback state without constraining unrelated resources. -/
theorem HeldFrame.payloadReady (ops : Ops State StringResource BoxResource Terminal)
    {error : Error BoxResource} {payload : Payload StringResource} {before after : State}
    (ready : payload.Ready ops before)
    (frame : HeldFrame ops error payload.strings before after) : payload.Ready ops after := by
  refine ⟨ready.1, ?_⟩
  intro resource member
  obtain ⟨text, present⟩ := ready.2 resource member
  exact ⟨text, (frame.2 resource member).trans present⟩

/-- Initial distinct fields and fresh, live conversion results make the
replacement ready. Old comparison cleanup cannot retire a retained field or
either new String; the existing primitive laws establish those facts. -/
theorem replaceValues_ready (ops : Ops State StringResource BoxResource Terminal)
    (laws : ops.ComparisonLaws) {before after : State} {error result : Error BoxResource}
    {left right : StringResource} {payload : Payload StringResource}
    (present : ops.currentBox before error.resource = some payload)
    (ready : payload.Ready ops before)
    (leftLive : ∃ text, ops.currentString before left = some text)
    (rightLive : ∃ text, ops.currentString before right = some text)
    (leftApart : left ∉ payload.strings) (rightApart : right ∉ left :: payload.strings)
    (run : replaceValues ops before (error, left, right) (.returned result after)) :
    Ready ops after result := by
  obtain ⟨actual, observed, intermediate, dropped, remaining⟩ := run
  have same : actual = payload := Option.some.inj (observed.symm.trans present)
  subst actual
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned acknowledgement middle =>
    cases acknowledgement
    obtain ⟨next, readable, final, stored, returned⟩ := remaining
    have same : next = payload :=
      Option.some.inj (readable.symm.trans ((dropStrings_boxes laws.drop_boxes dropped
        error.resource).trans present))
    subst next
    cases returned
    have split : payload.retainedStrings.Nodup ∧ (comparedStrings payload.compared).Nodup ∧
        ∀ a ∈ payload.retainedStrings, ∀ b ∈ comparedStrings payload.compared, a ≠ b := by
      apply List.nodup_append.mp
      rw [← Payload.strings_eq_append]
      exact ready.1
    have retainedMember : ∀ resource ∈ payload.retainedStrings, resource ∈ payload.strings := by
      intro resource member
      rw [Payload.strings_eq_append]
      exact List.mem_append_left _ member
    have oldMember : ∀ resource ∈ comparedStrings payload.compared, resource ∈ payload.strings := by
      intro resource member
      rw [Payload.strings_eq_append]
      exact List.mem_append_right _ member
    have rightOld : right ∉ payload.strings := fun member =>
      rightApart (List.mem_cons_of_mem left member)
    have different : left ≠ right := by
      intro same
      exact rightApart (List.mem_cons.mpr (Or.inl same.symm))
    refine ⟨payload.withValues left right, laws.store_current _ _ _ _ stored, ?_, ?_⟩
    · rw [Payload.withValues_strings]
      refine List.nodup_append.mpr ⟨split.1, by simp [different], ?_⟩
      intro held member other otherMember
      rcases List.mem_cons.mp otherMember with rfl | last
      · intro same
        exact leftApart (same ▸ retainedMember held member)
      · have same : other = right := List.mem_singleton.mp last
        subst other
        intro same
        exact rightOld (same ▸ retainedMember held member)
    · intro held member
      rw [Payload.withValues_strings] at member
      have facts : held ∉ comparedStrings payload.compared ∧
          ∃ text, ops.currentString before held = some text := by
        rcases List.mem_append.mp member with retained | added
        · exact ⟨fun old => split.2.2 held retained held old rfl,
            ready.2 held (retainedMember held retained)⟩
        · rcases List.mem_cons.mp added with rfl | last
          · exact ⟨fun old => leftApart (oldMember held old), leftLive⟩
          · have same : held = right := List.mem_singleton.mp last
            subst held
            exact ⟨fun old => rightOld (oldMember right old), rightLive⟩
      obtain ⟨text, live⟩ := facts.2
      exact ⟨text, (laws.store_strings _ _ _ _ stored held).trans
        ((dropStrings_other laws.string_other dropped held facts.1).trans live)⟩

/-- A normal call returns a ready owned error. The proof uses initial
readiness, both actual conversion frames and both reached destructor frames;
it neither filters callbacks nor assumes an independent final-state fact. -/
theorem withValues_ready (ops : Ops State StringResource BoxResource Terminal)
    (laws : ops.ComparisonLaws) (callbacks : ValuesCallbacks State StringResource Left Right Unwind
      Terminal)
    {before after : State} {args : ValuesArgs BoxResource Left Right} {result : Error BoxResource}
    (ready : Ready ops before args.error)
    (admissible : callbacks.ReturnedAdmissible ops args before)
    (run : withValues ops callbacks before args (.returned result after)) : Ready ops after result
      := by
  obtain ⟨payload, present, payloadReady⟩ := ready
  obtain ⟨left, afterLeft, right, afterRight, afterAssignment, leftRun, rightRun, assigned, drops⟩
    :=
    withValues_returned_trace ops callbacks run
  have same := replaceValues_identity ops assigned
  subst result
  have leftFrame := admissible.left payload left afterLeft present payloadReady leftRun
  have rightFrame := admissible.right payload left afterLeft right afterRight
    present payloadReady leftRun rightRun
  have firstReady := HeldFrame.payloadReady ops payloadReady leftFrame.1
  have secondFrame : HeldFrame ops args.error payload.strings afterLeft afterRight :=
    ⟨rightFrame.1.1, fun held member => rightFrame.1.2 held (List.mem_cons_of_mem left member)⟩
  have leftLive : ∃ text, ops.currentString afterRight left = some text := by
    obtain ⟨text, live⟩ := leftFrame.2.1
    exact ⟨text, (rightFrame.1.2 left (by simp)).trans live⟩
  have replaced := replaceValues_ready ops laws
    (rightFrame.1.1.trans (leftFrame.1.1.trans present))
    (HeldFrame.payloadReady ops firstReady secondFrame) leftLive rightFrame.2.1
    leftFrame.2.2 rightFrame.2.2 assigned
  obtain ⟨updated, updatedPresent, updatedReady⟩ := replaced
  have body : valuesBody ops callbacks args before () (.returned args.error afterAssignment) :=
    ⟨.returned left afterLeft, leftRun,
      .returned right afterRight, ⟨.returned right afterRight, rightRun, rfl⟩,
      .returned args.error afterAssignment, assigned, rfl⟩
  cases drops with
  | cons _ _ _ afterFirstDrop _ firstDrop tail =>
    cases tail with
    | cons _ _ _ afterSecondDrop _ secondDrop finish =>
      cases finish
      have leftEntry : valuesReturnedDropEntry ops callbacks args [] before afterAssignment :=
        ⟨args.error, afterAssignment, body, .nil _⟩
      have firstFrame := admissible.dropLeft afterAssignment updated afterFirstDrop
        leftEntry updatedPresent updatedReady firstDrop
      have firstPresent := firstFrame.1.trans updatedPresent
      have firstReady := HeldFrame.payloadReady ops updatedReady firstFrame
      have rightEntry : valuesReturnedDropEntry ops callbacks args
          [fun state outcome => callbacks.dropLeft state args.left outcome] before afterFirstDrop :=
        ⟨args.error, afterAssignment, body, .cons _ _ _ _ _ firstDrop (.nil _)⟩
      have secondFrame := admissible.dropRight afterFirstDrop updated after
        rightEntry firstPresent firstReady secondDrop
      exact ⟨updated, secondFrame.1.trans firstPresent,
        HeldFrame.payloadReady ops firstReady secondFrame⟩

end Solanalib.Specs.Core.AnchorErrorOwned
