/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuard
public import Solanalib.Specs.Core.TokenRequestAllocatedTypes
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

/-- A provider retains the type and target bounds of a source cell. Unborrowed
balances, data contents and data lengths may change. Held contents have the
separate, stronger guard law. No addressable byte slice becomes a non-slice. -/
def CellKind (wordBits : Nat) : AccountInfo.Content → AccountInfo.Content → Prop
  | .lamports _, .lamports _ => True
  | .data before, .data after =>
    (before.length < 2^wordBits → after.length < 2^wordBits) ∧
      (before.length < 2^(wordBits - 1) → after.length < 2^(wordBits - 1))
  | _, _ => False

/-- AccountInfo representation before the first borrow is protected too.
Primitive calls keep current cell identities, policies and types and cannot
invalidate the borrow protocol. Data values are not frozen by this law. -/
structure InputFrame (wordBits : Nat) (before after : AccountInfo.State) : Prop where
  /-- A later local acquisition sees a valid borrow store. -/
  valid : after.Valid
  /-- Primitive effects do not reuse consumed guard generations. -/
  history : Borrow.History before after
  /-- Every previously represented typed cell remains represented. -/
  cells : ∀ handle old, before.lookupCell handle = some old →
    ∃ next, after.lookupCell handle = some next ∧ next.policy = old.policy ∧
      CellKind wordBits old.value next.value

/-- An unchanged borrow store satisfies representation admission independently
of whether it contains any live guards. -/
theorem InputFrame.refl (wordBits : Nat) (state : AccountInfo.State) (valid : state.Valid) :
    InputFrame wordBits state state := by
  refine ⟨valid, Borrow.History.refl state, ?_⟩
  intro handle old present
  refine ⟨old, present, rfl, ?_⟩
  cases old.value with
  | lamports _ => trivial
  | data _ => exact ⟨fun bound => bound, fun bound => bound⟩

/-- An actual one-cell replacement may change an unborrowed value or length
while keeping source typing and bounds. Its authorization relative to held
guards is deliberately the separate guard-frame obligation. -/
theorem InputFrame.replace {wordBits : Nat} {state : AccountInfo.State}
    {handle : Borrow.Handle} {cell : Borrow.Cell AccountInfo.Content}
    (valid : state.Valid) (present : state.lookupCell handle = some cell)
    (value : AccountInfo.Content) (kind : CellKind wordBits cell.value value) :
    InputFrame wordBits state (Borrow.replaceCell state handle value).2 := by
  refine ⟨Borrow.replaceCell_valid valid handle value,
    Borrow.replaceCell_history state handle value, ?_⟩
  intro query old found
  by_cases equal : query = handle
  · subst query
    have same : old = cell := Option.some.inj (found.symm.trans present)
    cases same
    exact ⟨{ cell with value := value }, Borrow.replaceCell_lookup present value, rfl, kind⟩
  · have different : query.cell ≠ handle.cell := by
      intro same
      apply equal
      cases query
      cases handle
      cases same
      rfl
    refine ⟨old, (Borrow.replaceCell_other state handle query value different).trans found, rfl, ?_⟩
    cases old.value with
    | lamports _ => trivial
    | data _ => exact ⟨fun bound => bound, fun bound => bound⟩

/-- Cell typing and both target length bounds compose across actual calls. -/
theorem CellKind.trans {wordBits : Nat} {first middle last : AccountInfo.Content}
    (one : CellKind wordBits first middle) (two : CellKind wordBits middle last) :
    CellKind wordBits first last := by
  cases first <;> cases middle <;> cases last
  all_goals first
    | exact False.elim one
    | exact False.elim two
    | exact True.intro
    | exact ⟨fun bound => two.1 (one.1 bound), fun bound => two.2 (one.2 bound)⟩

/-- Sequential primitive representation changes preserve the same source
identities and the values and bounds of the actual last state. -/
theorem InputFrame.trans {wordBits : Nat} {first middle last : AccountInfo.State}
    (one : InputFrame wordBits first middle) (two : InputFrame wordBits middle last) :
    InputFrame wordBits first last := by
  refine ⟨two.valid, one.history.trans two.history, ?_⟩
  intro handle old present
  obtain ⟨intermediate, found, policy, shape⟩ := one.cells handle old present
  obtain ⟨next, nextFound, nextPolicy, nextShape⟩ := two.cells handle intermediate found
  exact ⟨next, nextFound, nextPolicy.trans policy, shape.trans nextShape⟩

/-- A reached primitive exit retains the precise AccountInfo input type and
policy required by the next acquisition, including when no guard was live. -/
theorem InputFrame.accountInfo {wordBits : Nat} {before after : AccountInfo.State}
    (frame : InputFrame wordBits before after) {profile : AccountInfo.Profile}
    {info : AccountInfo.Value} (width : profile.wordBits = wordBits)
    (ready : AccountInfo.Valid profile before info) : AccountInfo.Valid profile after info := by
  obtain ⟨widthBound, _, separate, ⟨balance, balanceFound⟩, ⟨bytes, dataFound, dataBound⟩⟩ := ready
  refine ⟨widthBound, frame.valid, separate, ?_, ?_⟩
  · obtain ⟨⟨value, policy⟩, found, samePolicy, shape⟩ := frame.cells info.lamports _ balanceFound
    cases value with
    | data _ => exact False.elim shape
    | lamports actual =>
      cases samePolicy
      exact ⟨actual, found⟩
  · obtain ⟨⟨value, policy⟩, found, samePolicy, shape⟩ := frame.cells info.data _ dataFound
    cases value with
    | lamports _ => exact False.elim shape
    | data actual =>
      cases samePolicy
      exact ⟨actual, found, by simpa only [width] using shape.1 (by simpa only [width] using
        dataBound)⟩

/-- Addressable source slices remain addressable before the next decoder or
borrow, while their unborrowed current bytes and length may have changed. -/
theorem InputFrame.addressable {wordBits : Nat} {before after : AccountInfo.State}
    (frame : InputFrame wordBits before after) {profile : AccountInfo.Profile}
    {info : AccountInfo.Value} (width : profile.wordBits = wordBits)
    (ready : Onchain.dataAddressable profile before info) :
    Onchain.dataAddressable profile after info := by
  obtain ⟨bytes, found, bound⟩ := ready
  obtain ⟨⟨value, policy⟩, nextFound, samePolicy, shape⟩ := frame.cells info.data _ found
  cases value with
  | lamports _ => exact False.elim shape
  | data actual =>
    cases samePolicy
    exact ⟨actual, nextFound,
      by simpa only [width] using shape.2 (by simpa only [width] using bound)⟩

/-- The complete fixed source argument set remains ready at a reached call
state. This is a consequence of primitive representation preservation. -/
theorem InputFrame.args {wordBits : Nat} {before after : AccountInfo.State}
    (frame : InputFrame wordBits before after) {args : Onchain.Args}
    (width : args.profile.wordBits = wordBits) (ready : args.Valid before) : args.Valid after := by
  refine ⟨ready.1, ready.2.1, ready.2.2.1, ready.2.2.2.1, ?_⟩
  intro info member
  exact ⟨frame.accountInfo width (ready.2.2.2.2 info member).1,
    frame.addressable width (ready.2.2.2.2 info member).2⟩

/-- The representation frame of the actual finite outcome, with no terminal state. -/
def InputOutcome {Extra Value Unwind Terminal : Type} (wordBits : Nat) (before : World Extra) :
    Outcome (World Extra) Value Unwind Terminal → Prop
  | .returned _ after | .unwound _ after => InputFrame wordBits before.1 after.1
  | .terminated _ => True

/-- Universal primitive admission also applies before the first data guard is
acquired. It does not condition an earlier exit on a later body/read outcome. -/
def InputPreserves {Extra Args Value Unwind Terminal : Type} (wordBits : Nat)
    (run : Callback.Run (World Extra) Args Value Unwind Terminal) : Prop :=
  ∀ before args, before.1.Valid → ∀ outcome, run before args outcome →
    InputOutcome wordBits before outcome

/-- A partial provider supplies no fictitious finite exit. -/
theorem InputPreserves.empty {Extra Args Value Unwind Terminal : Type} (wordBits : Nat) :
    InputPreserves wordBits (fun (_ : World Extra) (_ : Args)
      (_ : Outcome (World Extra) Value Unwind Terminal) => False) := by
  intro _ _ _ _ impossible
  exact False.elim impossible

/-- Auxiliary-only effects preserve source input representation on all exits. -/
theorem InputPreserves.of_accounts {Extra Args Value Unwind Terminal : Type} (wordBits : Nat)
    {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (unchanged : ∀ before args outcome, run before args outcome →
      match outcome with
      | .returned _ after | .unwound _ after => after.1 = before.1
      | .terminated _ => True) : InputPreserves wordBits run := by
  intro before args valid outcome called
  have same := unchanged before args outcome called
  cases outcome with
  | returned _ after =>
    change InputFrame wordBits before.1 after.1
    rw [same]
    exact InputFrame.refl _ _ valid
  | unwound _ after =>
    change InputFrame wordBits before.1 after.1
    rw [same]
    exact InputFrame.refl _ _ valid
  | terminated _ => trivial

/-- A mathematical focus into auxiliary storage leaves all typed cells intact. -/
theorem InputPreserves.focus {Extra Inner Args Value Unwind Terminal : Type} (wordBits : Nat)
    (part : Owned.Focus (World Extra) Inner)
    (outside : ∀ before inner, (part.set before inner).1 = before.1)
    (run : Callback.Run Inner Args Value Unwind Terminal) :
    InputPreserves wordBits (part.lift run) := by
  apply InputPreserves.of_accounts
  rintro before _ _ ⟨produced, _, rfl⟩
  cases produced with
  | returned _ _ => exact outside _ _
  | unwound _ _ => exact outside _ _
  | terminated _ => trivial

/-- Return-value mapping preserves the exact actual input-representation frame. -/
theorem InputPreserves.map {Extra Args Value Next Unwind Terminal : Type} {wordBits : Nat}
    (f : Value → Next) {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : InputPreserves wordBits run) : InputPreserves wordBits (Callback.map f run) := by
  rintro before args valid outcome ⟨produced, called, rfl⟩
  have frame := law before args valid produced called
  cases produced <;> exact frame

/-- Actual sequential provider inputs inherit representation validity from
each prior exit, independently of whether a later call has any outcome. -/
theorem InputPreserves.bind {Extra Args Value Next Unwind Terminal : Type} {wordBits : Nat}
    {first : Callback.Run (World Extra) Args Value Unwind Terminal}
    {next : Value → World Extra → Outcome (World Extra) Next Unwind Terminal → Prop}
    (firstLaw : InputPreserves wordBits first)
    (nextLaw : ∀ value, InputPreserves wordBits (fun state (_ : Unit) => next value state)) :
    InputPreserves wordBits (Callback.bind first next) := by
  rintro before args valid outcome ⟨produced, called, continued⟩
  have frame := firstLaw before args valid produced called
  cases produced with
  | returned value after =>
    have last := nextLaw value after () frame.valid outcome continued
    cases outcome with
    | returned _ _ => exact frame.trans last
    | unwound _ _ => exact frame.trans last
    | terminated _ => trivial
  | unwound _ _ => cases continued; exact frame
  | terminated _ => cases continued; trivial

/-- Selecting actual primitive arguments leaves its outcome law unchanged. -/
theorem InputPreserves.arguments {Extra Args Selected Value Unwind Terminal : Type}
    {wordBits : Nat} {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : InputPreserves wordBits run) (select : Selected → Args) :
    InputPreserves wordBits (fun state selected => run state (select selected)) := by
  intro before args valid
  exact law before (select args) valid

/-- No-unwind Rc lifting preserves all current typed input cells. -/
theorem InputPreserves.rcLift {Extra Args Value Unwind Terminal : Type} {wordBits : Nat}
    {run : Callback.Run (World Extra) Args Value Empty Terminal}
    (law : InputPreserves wordBits run) :
    InputPreserves wordBits (AccountInfoRc.lift (Unwind := Unwind) run) := by
  rintro before args valid outcome ⟨produced, called, same⟩
  have frame := law before args valid produced called
  cases produced with
  | returned _ _ => cases same; exact frame
  | unwound impossible _ => exact nomatch impossible
  | terminated _ => cases same; trivial

/-- Primitive vector representation laws. These concern input cells, rather
than the allocation, contents or element ownership of the vector. -/
structure VectorInputs {Extra Element Resource Unwind Terminal : Type} (wordBits : Nat)
    (ops : Owned.VectorOps (World Extra) Element Resource Unwind Terminal) : Prop where
  /-- Infallible construction keeps the input representation. -/
  empty : ∀ before, before.1.Valid → InputFrame wordBits before.1 (ops.empty before).2.1
  /-- The actual outcomes of capacity allocation keep typed input cells. -/
  capacity : InputPreserves wordBits ops.withCapacity
  /-- Actual from-array outcomes keep typed input cells. -/
  fromList : InputPreserves wordBits ops.fromList
  /-- Actual push outcomes keep typed input cells. -/
  push : InputPreserves wordBits ops.push
  /-- Actual extension outcomes keep typed input cells. -/
  extend : InputPreserves wordBits ops.extend
  /-- Destructor outcomes retain the representation of the borrowed payloads. -/
  drop : InputPreserves wordBits ops.drop

/-- Focused vector models have input laws without an allocator-success premise. -/
theorem VectorInputs.focus {Extra Inner Element Resource Unwind Terminal : Type}
    (wordBits : Nat) (ops : Owned.VectorOps Inner Element Resource Unwind Terminal)
    (part : Owned.Focus (World Extra) Inner)
    (outside : ∀ before inner, (part.set before inner).1 = before.1) :
    VectorInputs wordBits (ops.focus part) where
  empty := by
    intro before valid
    change InputFrame wordBits before.1 (part.set before (ops.empty (part.get before)).2).1
    rw [outside]
    exact InputFrame.refl _ _ valid
  capacity := InputPreserves.focus wordBits part outside ops.withCapacity
  fromList := InputPreserves.focus wordBits part outside ops.fromList
  push := InputPreserves.focus wordBits part outside ops.push
  extend := InputPreserves.focus wordBits part outside ops.extend
  drop := InputPreserves.focus wordBits part outside ops.drop

end Solanalib.Specs.Core.Token.AllocatedGuard
