/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Values

/-! The native scripted implementations, including their source-reference
arguments. Each is an explicit family index; no callback is replaced by an
assumption that it returns the cached value. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

def bump (retain : Bool) (s : Effects) (h : Borrow.Handle) : Effects :=
  { s with counts := s.counts.modify h.cell fun n => if retain then n + 1 else n - 1 }

def rcFn (retain : Bool) (s : Effects) (arg : AccountInfoRc.Field × Borrow.Handle) :
    Outcome Effects Unit Empty String := .returned () (bump retain s arg.2)

def rc : AccountInfoRc.Ops Effects String :=
  ⟨Callback.ofFunction (rcFn true), Callback.ofFunction (rcFn false)⟩

def infoDeps : (storage : InfoStorage) → InfoDeps storage Effects String
  | .owned => rc
  | .borrowed => ()

def cloneInfoFn {U : Type} (storage : InfoStorage) (s : Effects) (info : AccountInfo.Value) :
    Outcome Effects AccountInfo.Value U String :=
  .returned info (match storage with
    | .owned => bump true (bump true s info.lamports) info.data
    | .borrowed => s)

def dropInfoFn {U : Type} (storage : InfoStorage) (s : Effects) (info : AccountInfo.Value) :
    Outcome Effects Unit U String :=
  .returned () (match storage with
    | .owned => bump false (bump false s info.lamports) info.data
    | .borrowed => s)

theorem cloneInfo_graph {U : Type} (storage : InfoStorage) (s : Effects) (info : AccountInfo.Value)
  :
    PGraph (cloneInfo (Unwind := U) storage (infoDeps storage) s info)
      (some (cloneInfoFn storage s info)) := by
  cases storage with
  | borrowed => exact PGraph.eq_right _
  | owned =>
    have h : PGraph (AccountInfoRc.cloneCall rc s info)
        (some (.returned info (bump true (bump true s info.lamports) info.data))) :=
      PGraph.bind (PGraph.ofFunction (rcFn true) s (.lamports, info.lamports))
        fun _ mid => PGraph.map (fun _ => AccountInfo.clone info)
          (PGraph.ofFunction (rcFn true) mid (.data, info.data))
    exact PGraph.exists_eq _ h

theorem dropInfo_graph {U : Type} (storage : InfoStorage) (s : Effects) (info : AccountInfo.Value) :
    PGraph (dropInfo (Unwind := U) storage (infoDeps storage) s info)
      (some (dropInfoFn storage s info)) := by
  cases storage with
  | borrowed => exact PGraph.eq_right _
  | owned =>
    have h : PGraph (AccountInfoRc.dropCall rc s info)
        (some (.returned () (bump false (bump false s info.lamports) info.data))) :=
      PGraph.bind (PGraph.ofFunction (rcFn false) s (.lamports, info.lamports))
        fun _ mid => PGraph.ofFunction (rcFn false) mid (.data, info.data)
    exact PGraph.exists_eq _ h

def callbackPointer (mutable : Bool) (a : PayloadArg Nat) : Bool :=
  decide (a.location = handle ∧ a.reference.guard = guard ∧ a.reference.mutable = mutable)

def clonePayloadFn (mode : Nat) (s : Effects) (arg : PayloadArg Nat) :
    Outcome Effects Nat String String :=
  let after := { s with trace := s.trace ++ [s!"clone:{arg.value}:\
    {callbackPointer false arg}"] }
  if mode = 1 then .unwound "script clone" after
  else if mode = 2 then .terminated "abort"
  else .returned (arg.value + 10) after

def cloneTypes (storage : InfoStorage) (mode : Nat) : CloneTypes storage :=
  ⟨Nat, Effects, String, String, Callback.ofFunction (clonePayloadFn mode), infoDeps storage⟩

def infoCloneTypes (storage : InfoStorage) : InfoCloneTypes storage :=
  ⟨Effects, String, infoDeps storage⟩

def moveTypes (storage : InfoStorage) : MoveTypes storage :=
  ⟨Nat, Effects, String, infoDeps storage⟩

def dropPayloadFn (mode : Nat) (s : Effects) (arg : PayloadArg Nat) :
    Outcome Effects Unit String String :=
  let after := { s with trace := s.trace ++ [s!"drop:{arg.value}:{callbackPointer true arg}"] }
  if mode = 1 then .unwound "script drop" after
  else if mode = 2 then .terminated "abort"
  else .returned () after

def setTypes (mode : Nat) : SetTypes :=
  ⟨Nat, Effects, String, String, Callback.ofFunction (dropPayloadFn mode)⟩

def logFn (s : Effects) (message : String) : Outcome Effects Unit String String :=
  .returned () { s with messages := s.messages ++ [message.toUTF8.toList] }

def panicFn (s : Effects) (_ : Unit) : Outcome Effects Empty String String :=
  .unwound "explicit panic" s

def mutableTypes (debug : Bool) : MutableTypes :=
  ⟨Nat, Effects, String, String, debug, Callback.ofFunction logFn, Callback.ofFunction panicFn⟩

def sysvarPointer (storage : InfoStorage) (arg : InfoArg) : Bool :=
  decide (arg.reference = ⟨guard, match storage with
    | .owned => .field handle
    | .borrowed => .external 19⟩)

/-- Here the error index is its complete Debug text. The old owned String
payload is retained in that text and passed to the consuming unwrap callback. -/
def fromInfoFn (storage : InfoStorage) (mode : Nat) (s : Effects) (arg : InfoArg) :
    Outcome Effects (Except String Nat) String String :=
  let after := { s with trace := s.trace ++
    [s!"from_info:{s.counts.getD arg.value.lamports.cell 0}:\
      {s.counts.getD arg.value.data.cell 0}:{sysvarPointer storage arg}"] }
  if mode = 1 then .returned (.error "Custom(81)") after
  else if mode = 2 then .unwound "script decode" after
  else if mode = 3 then .terminated "abort"
  else if mode = 4 then .returned (.error "BorshIoError(\"owned sysvar error\")") after
  else .returned (.ok 23) after

def unwrapFn (s : Effects) (error : String) : Outcome Effects Empty String String :=
  .unwound ("called `Result::unwrap()` on an `Err` value: " ++ error) s

def sysvarTypes (storage : InfoStorage) (mode : Nat) : SysvarCloneTypes storage :=
  ⟨Nat, String, Effects, String, String, infoDeps storage,
    Callback.ofFunction (fromInfoFn storage mode), Callback.ofFunction unwrapFn⟩

end SolanalibTest.Conformance.Library.Families.AnchorViews
