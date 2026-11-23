/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV2.Projection

/-!
# solana-account-view 2.0.0: scripted `try_map` callbacks

`Ref::try_map` and `RefMut::try_map` are generic over their closure. The driver
instantiates the closure with a script, recorded in the arguments: a list of
effects, then an ending. Effects are `set_lamports(cell, value)` through a
captured `AccountView` of any account (the setter of the library) and, for
`RefMut`, a write of bytes through the `&mut [u8]` of the closure at an offset of its
input. The ending returns a sub-reference `[offset, length]` of the input (for
`U = u8`, length 1), returns `Err(e)` with `e : u8`, or panics with a message.
The closures index the slice they receive, so a write or a target outside it
panics natively with the message of the standard library, and so does the interpretation of the
script (`runScript`).

On the Lean side the same script is the callback `scriptCallback`, the graph
of `runScript`, at the family index `mapProfile`: byte-range targets
(`sliceProfile`), `Failure := Nat` (the `u8` error), `Unwind := String` (the
panic message) and no terminal exit. The registered relation is decided through
`tryMap_function_iff`, a graph lemma for every function-defined callback of the
common mapping protocol, proved here from the definitions in `specs/solana`.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.AccountsV2

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The index of the `try_map` families exercised by the driver. -/
abbrev mapProfile : AccountView.TryMapProfile := ⟨AccountView.sliceProfile, Nat, String, Empty⟩

abbrev World := PoolState × Unit
abbrev MapResult := AccountView.TryMapResult mapProfile
abbrev MapOutcome := Outcome World MapResult String Empty
abbrev ProtocolOutcome := Outcome World (Borrow.TryMapResult Nat) String Empty

inductive Effect where
  /-- `set_lamports` through the captured view of an instruction account, which
  denotes `cell`; `none` if the driver has no view at that position (`entries`
  views). -/
  | setLamports (cell : Option Nat) (entry entries : Nat) (value : Nat)
  /-- A write of `bytes` through the `&mut [u8]` of the closure at `offset`. -/
  | write (offset : Nat) (bytes : Solanalib.Runtime.Bytes)

inductive Ending where
  | ok (offset length : Nat)
  | err (code : Nat)
  | panic (message : String)

/-- A recorded script, with the shape of the closure at the instantiation of the checker:
whether its input is `&mut [u8]` (`RefMut`) and whether its target is `u8`. -/
structure Script where
  effects : List Effect
  ending : Ending
  mutable : Bool
  byte : Bool

/-! The closures of the driver index the slice they receive, so a target or a write
outside it panics natively with the slice-index message of the standard library; the
script interpretation below gives the same unwind, with the state reached so far
(the failing effect writes nothing). Messages are those of the repository
toolchain: a range checks its start, then its end. -/

/-- The panic of `&d[start..end]` on a slice of length `len`, if any. -/
def rangePanic (start stop len : Nat) : Option String :=
  if len < start then some s!"range start index {start} out of range for slice of length \
    {len}"
  else if len < stop then some s!"range end index {stop} out of range for slice of length \
    {len}"
  else none

/-- The panic of `&d[index]` on a slice of length `len`, if any. -/
def indexPanic (index len : Nat) : Option String :=
  if index < len then none else some
    s!"index out of bounds: the len is {len} but the index is {index}"

/-- One effect at the held account `held`, whose current target is `view`: the
state after it, or the panic it raises. A captured setter is the registered
`set_lamports` model; a write through the `&mut [u8]` of the closure changes the bytes of the
held account immediately. -/
def applyEffect (script : Script) (held : Handle) (view : Slice) (state : PoolState) :
    Effect → Except String PoolState
  | .setLamports (some cell) _ _ value =>
    .ok (Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_model state (⟨cell⟩,
      value)).2
  | .setLamports none entry entries _ =>
    .error ((indexPanic entry entries).getD s!"instruction account {entry} denotes no \
      account")
  | .write offset bytes =>
    if !script.mutable then .error "a shared closure cannot write"
    else match rangePanic offset (offset + bytes.length) view.length with
      | some message => .error message
      | none => .ok (Borrow.modifyCell state held fun account =>
          account.write ⟨view.offset + offset, bytes.length⟩ bytes).2

/-- The effects in order: the state reached and the panic that stopped them, if any. -/
def runEffects (script : Script) (held : Handle) (view : Slice) :
    List Effect → PoolState → PoolState × Option String
  | [], state => (state, none)
  | effect :: rest, state => match applyEffect script held view state effect with
    | .ok next => runEffects script held view rest next
    | .error message => (state, some message)

/-- The panic of the ending, if its target leaves the input slice of the closure. -/
def endingPanic (script : Script) (view : Slice) (offset length : Nat) : Option String :=
  if script.byte then
    if length = 1 then indexPanic offset view.length else some "a u8 target has length 1"
  else rangePanic offset (offset + length) view.length

/-- The callback outcome of the script on the world, held account and target it receives. -/
def runScript (script : Script) (world : World) (held : Handle) (view : Slice) :
    Outcome World (Except Nat Slice) String Empty :=
  let (state, stopped) := runEffects script held view script.effects world.1
  let after : World := (state, world.2)
  match stopped with
  | some message => .unwound message after
  | none => match script.ending with
    | .ok offset length => match endingPanic script view offset length with
      | some message => .unwound message after
      | none => .returned (.ok ⟨view.offset + offset, length⟩) after
    | .err code => .returned (.error code) after
    | .panic message => .unwound message after

/-- The script as a mapping callback: the graph of `runScript`. -/
def scriptCallback (script : Script) : Borrow.MapCallback Account Slice Unit Nat String Empty :=
  fun world held view outcome => runScript script world held view = outcome

/-- The outcome of the common mapping protocol for a function-defined callback. -/
def tryMapComputed {Content View Aux Failure Unwind Terminal : Type}
    (policy : Borrow.UnwindPolicy)
    (f : Borrow.World Content View Aux → Handle → View →
      Outcome (Borrow.World Content View Aux) (Except Failure View) Unwind Terminal)
    (before : Borrow.World Content View Aux) (guard : Guard) :
    Outcome (Borrow.World Content View Aux) (Borrow.TryMapResult Failure) Unwind Terminal :=
  match before.1.resolve guard with
  | none => .returned (.error .invalidGuard) before
  | some slot => match before.1.lookupCell slot.cell with
    | none => .returned (.error .missingCell) before
    | some _ => Borrow.finishTryMap policy guard slot.view (f before slot.cell slot.view)

/-- Graph lemma: with a function-defined callback, the common mapping relation
admits exactly the outcome `tryMapComputed` computes. -/
theorem tryMap_function_iff {Content View Aux Failure Unwind Terminal : Type}
    (policy : Borrow.UnwindPolicy)
    (f : Borrow.World Content View Aux → Handle → View →
      Outcome (Borrow.World Content View Aux) (Except Failure View) Unwind Terminal)
    (before : Borrow.World Content View Aux) (guard : Guard)
    (o : Outcome (Borrow.World Content View Aux) (Borrow.TryMapResult Failure) Unwind Terminal) :
    Borrow.tryMap policy (fun world held view out => f world held view = out) before guard o ↔
      tryMapComputed policy f before guard = o := by
  unfold Borrow.tryMap tryMapComputed
  cases before.1.resolve guard with
  | none => exact eq_comm
  | some slot =>
    dsimp only
    cases before.1.lookupCell slot.cell with
    | none => exact eq_comm
    | some cell =>
      dsimp only
      constructor
      · rintro ⟨produced, rfl, equal⟩
        exact equal.symm
      · intro equal
        exact ⟨_, rfl, equal.symm⟩

/-- `Ref::try_map` at `mapProfile` with a scripted callback, through the graph lemma. -/
theorem ref_try_map_evaluated (script : Script) (before : World) (guard : Guard) (o : MapOutcome) :
    Solanalib.Specs.SolanaAccountView.Ref.try_map_model mapProfile before ⟨guard, scriptCallback
      script⟩ o ↔
      (tryMapComputed .retainLease (runScript script) before guard : ProtocolOutcome) =
        AccountView.protocolOutcome mapProfile o :=
  tryMap_function_iff .retainLease (runScript script) before guard _

/-- `RefMut::try_map` at `mapProfile` with a scripted callback, through the graph lemma. -/
theorem ref_mut_try_map_evaluated (script : Script) (before : World) (guard : Guard) (o :
  MapOutcome) :
    Solanalib.Specs.SolanaAccountView.RefMut.try_map_model mapProfile before ⟨guard, scriptCallback
      script⟩ o ↔
      (tryMapComputed .retainLease (runScript script) before guard : ProtocolOutcome) =
        AccountView.protocolOutcome mapProfile o :=
  tryMap_function_iff .retainLease (runScript script) before guard _

/-! ## Records -/

/-- An effect; `set_lamports` names the captured `AccountView` by its
instruction account, which denotes the cell of its first occurrence. -/
def parseEffect (before : Native) (j : Json) : Result Effect := do
  match j.getObjVal? "set_lamports", j.getObjVal? "write" with
  | .ok v, .error _ =>
    match (← v.getArr?).toList with
    | [i, n] =>
      let entry ← i.getNat?
      return .setLamports (cellOf before.region entry) entry before.region.entries.length (← asUInt
        64 n)
    | _ => throw s!"set_lamports effect must be [account, value], got {j.compress}"
  | .error _, .ok v =>
    match (← v.getArr?).toList with
    | [o, b] => return .write (← o.getNat?) (← asBytes b)
    | _ => throw s!"write effect must be [offset, bytes], got {j.compress}"
  | _, _ => throw s!"unknown callback effect {j.compress}"

def parseEnding (j : Json) : Result Ending := do
  match j.getObjVal? "ok", j.getObjVal? "err", j.getObjVal? "panic" with
  | .ok v, .error _, .error _ =>
    match (← v.getArr?).toList with
    | [o, l] => return .ok (← o.getNat?) (← l.getNat?)
    | _ => throw s!"callback result must be [offset, length], got {j.compress}"
  | .error _, .ok e, .error _ => return .err (← asUInt 8 e)
  | .error _, .error _, .ok m => return .panic (← m.getStr?)
  | _, _, _ => throw s!"unknown callback ending {j.compress}"

/-- A recorded script, interpreted with the closure shape of the instantiation of the checker
(`RefMut` input; `u8` target). -/
def parseScript (before : Native) (mutable byte : Bool) (j : Json) : Result Script := do
  return ⟨← (← (← field j "effects").getArr?).toList.mapM (parseEffect before),
    ← parseEnding (← field j "result"), mutable, byte⟩

def parseWorld (before : Native) (j : Json) : Result (Option World) := do
  return (← parseAfter before j).map ((·, ()))

def worldJson (w : World) : Json := stateJson w.1

def parseMapResult (j : Json) : Result MapResult :=
  match j.getObjVal? "ok", j.getObjVal? "err" with
  | .ok g, .error _ => return .ok (← parseGuard g)
  | .error _, .ok e => do
    match (← e.getArr?).toList with
    | [g, code] => return .error (← parseGuard g, ← asUInt 8 code)
    | _ => throw s!"try_map error must be [guard, error], got {j.compress}"
  | _, _ => throw s!"expected {"{"}\"ok\": …} or {"{"}\"err\": …}, got {j.compress}"

def mapResultJson : MapResult → Json
  | .ok g => okJson (guardJson g)
  | .error (g, code) => errJson (Json.arr #[guardJson g, toJson (code : Nat)])

/-- A recorded `try_map` outcome; `none` if its state is not denoted. -/
def parseMapOutcome (before : Native) (j : Json) : Result (Option MapOutcome) := do
  match ← (← field j "exit").getStr? with
  | "returned" =>
    let r ← parseMapResult (← field j "result")
    return (← parseWorld before (← field j "state")).map (.returned r)
  | "unwound" =>
    let reason ← (← field j "reason").getStr?
    return (← parseWorld before (← field j "state")).map (.unwound reason)
  | "terminated" => return none
  | other => throw s!"unknown exit {other}"

def mapOutcomeJson : MapOutcome → Json
  | .returned r w => returnedJson (mapResultJson r) (worldJson w)
  | .unwound reason w =>
    Json.mkObj [("exit", "unwound"), ("reason", Json.str reason), ("state", worldJson w)]

/-- The source outcome the reference gives, for the report. -/
def expectedMap (script : Script) (before : World) (guard : Guard) : Json :=
  match before.1.resolve guard with
  | none => "no outcome: the guard does not resolve"
  | some slot => match before.1.lookupCell slot.cell with
    | none => "no outcome: the account referenced by the guard is missing"
    | some _ => mapOutcomeJson (AccountView.finishSourceMap mapProfile guard slot.view
        (runScript script before slot.cell slot.view))

/-- Decide a `try_map` reference: first the precondition of its contract, then its
relation through its graph lemma. -/
def decideTryMap (mutable byte : Bool) (pre : Script → Pre World Guard)
    (relation : Script → World → Guard → MapOutcome → Prop)
    (graph : ∀ script before guard o, relation script before guard o ↔
      (tryMapComputed .retainLease (runScript script) before guard : ProtocolOutcome) =
        AccountView.protocolOutcome mapProfile o)
    (c : Case) : Result Verdict := do
  let native ← parseBefore c.state
  let before : World := (native.state, ())
  let guard ← guardArg c.args
  let script ← parseScript native mutable byte (← field c.args "callback")
  (pre script).check before guard
  let expected := expectedMap script before guard
  match ← parseMapOutcome native c.outcome with
  | some o =>
    have : Decidable (relation script before guard o) :=
      @decidable_of_iff _ _ (graph script before guard o).symm
        ((inferInstance : DecidableEq ProtocolOutcome) _ _)
    return ⟨decide (relation script before guard o), expected⟩
  | none => return ⟨false, expected⟩

end SolanalibTest.Conformance.Library.Families.AccountsV2
