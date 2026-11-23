/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.FixedLoggerAppend

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.FixedLogger

abbrev WriteFn (index : AppendIndex) := (List (Option UInt8) × index.Aux) → index.Value →
  Outcome (List (Option UInt8) × index.Aux) Nat index.Unwind index.Terminal
abbrev DropFn (index : AppendIndex) := index.Aux → index.Value →
  Outcome index.Aux Unit index.Unwind index.Terminal
abbrev DoubleFn (index : AppendIndex) := index.Aux → index.Unwind → index.Unwind → index.Terminal

def bodyComputed (index : AppendIndex) (write : WriteFn index)
    (before : index.World) (args : index.Ref × index.Value) :
    Outcome index.World index.Ref index.Unwind index.Terminal :=
  if before.1.len = index.capacity then .returned args.1 (before.1.markFull index.capacity,
    before.2)
  else finishWriter index args.1 before.1 (write (before.1.storage.drop before.1.len, before.2)
    args.2)

theorem body_graph (index : AppendIndex) (write : WriteFn index)
    (bound : index.write = Callback.ofFunction write) (before : index.World)
    (args : index.Ref × index.Value) (outcome : Outcome index.World index.Ref index.Unwind
      index.Terminal) :
    appendBody index before args outcome ↔ outcome = bodyComputed index write before args := by
  simp only [appendBody, bodyComputed]
  split
  · rfl
  · simp [bound, Callback.ofFunction]

/-- A single by-value argument is dropped after the body. The function form
retains the exact second-unwind state passed to the terminal policy. -/
def cleanupComputed (index : AppendIndex) (drop : DropFn index) (double : DoubleFn index)
    (value : index.Value) :
    Outcome index.World index.Ref index.Unwind index.Terminal →
    Outcome index.World index.Ref index.Unwind index.Terminal
  | .returned result before => Outcome.map (fun _ => result) (liftDrop index before.1 (drop
    before.2 value))
  | .unwound original before =>
    match drop before.2 value with
    | .returned () after => .unwound original (before.1, after)
    | .unwound reason after => .terminated (double after original reason)
    | .terminated reason => .terminated reason
  | .terminated reason => .terminated reason

theorem cleanup_graph (index : AppendIndex) (drop : DropFn index) (double : DoubleFn index)
    (dropBound : index.drop = Callback.ofFunction drop)
    (doubleBound : ∀ before first later terminal, index.double before first later terminal ↔
      terminal = double before first later) (value : index.Value)
    (pending outcome : Outcome index.World index.Ref index.Unwind index.Terminal) :
    Owned.cleanup (doubleUnwind index) [dropAction index value] pending outcome ↔
      outcome = cleanupComputed index drop double value pending := by
  cases pending with
  | returned result before =>
    simp only [Owned.cleanup, dropAction, dropBound, Callback.ofFunction,
      cleanupComputed]
    cases drop before.2 value with
    | returned value after => cases value; simp [liftDrop, Outcome.map]
    | unwound reason after => simp [liftDrop, Outcome.map]
    | terminated reason => simp [liftDrop, Outcome.map]
  | unwound original before =>
    simp only [Owned.cleanup, dropAction, dropBound, Callback.ofFunction,
      cleanupComputed]
    cases drop before.2 value with
    | returned value after => cases value; simp [liftDrop]
    | unwound reason after => simp [liftDrop, doubleUnwind, doubleBound]
    | terminated reason => simp [liftDrop]
  | terminated reason => rfl

def appendComputed (index : AppendIndex) (write : WriteFn index) (drop : DropFn index)
    (double : DoubleFn index) (before : index.World) (args : index.Ref × index.Value) :
    Outcome index.World index.Ref index.Unwind index.Terminal :=
  cleanupComputed index drop double args.2 (bodyComputed index write before args)

/-- The computed interpreter decides the complete registered operational
relation at function-valued primitive interpretations. -/
theorem append_graph (index : AppendIndex) (write : WriteFn index) (drop : DropFn index)
    (double : DoubleFn index) (writeBound : index.write = Callback.ofFunction write)
    (dropBound : index.drop = Callback.ofFunction drop)
    (doubleBound : ∀ before first later terminal, index.double before first later terminal ↔
      terminal = double before first later)
    (before : index.World) (args : index.Ref × index.Value)
    (outcome : Outcome index.World index.Ref index.Unwind index.Terminal) :
    appendAt index before args outcome ↔ outcome = appendComputed index write drop double before
      args := by
  simp only [appendAt, body_graph index write writeBound, exists_eq_left]
  exact cleanup_graph index drop double dropBound doubleBound args.2 _ outcome

def renderedComputed {Value : Type} (capacity : Nat) (render : Value → Solanalib.Runtime.Bytes)
    (before : Buffer × Unit) (args : Nat × Value) : Outcome (Buffer × Unit) Nat Empty Unit :=
  appendComputed (renderedIndex capacity render) (renderedWrite render)
    (fun before _ => .returned () before) (fun _ reason _ => nomatch reason) before args

theorem rendered_graph {Value : Type} (capacity : Nat) (render : Value → Solanalib.Runtime.Bytes)
    (before : Buffer × Unit) (args : Nat × Value) (outcome : Outcome (Buffer × Unit) Nat Empty
      Unit) :
    appendAt (renderedIndex capacity render) before args outcome ↔
      outcome = renderedComputed capacity render before args :=
  append_graph (renderedIndex capacity render) (renderedWrite render)
    (fun before _ => .returned () before) (fun _ reason _ => nomatch reason)
    rfl rfl (by intro _ reason; cases reason) before args outcome

end Solanalib.Specs.Core.FixedLogger
