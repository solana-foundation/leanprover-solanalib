/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Instructions.Cpi

/-!
# Family `Instructions`: InstructionView 2.1.0 `invoke_signed` at a recording `AsRef`

The generic v2 family is indexed by the account type `A` and its `AsRef<AccountView>`
implementation, which the source calls separately for the address check, the writable borrow
check and the descriptor initialization. The `A` of the driver is `Recording { index }`: each
`as_ref` call logs the source index and answers of the element from the script of the case,
either with the view of a chosen entry, or by panicking; once the script is exhausted it returns
the view of the element.

## The checked index

`RWorld` adds that script and call log to the CPI `World`; the pool, raw headers and the
invocation provider are those of `Cpi`, read from and acting on its `World`. `Account` is the
source index and `asRef` is the graph of `asRefFn`. The registered relation (`innerV2` with this
`asRef`) is decided through `inner_iff`, proved below from the definitions of the model of
`initializeV2`, `checkV2`, `prepareV2` and `innerV2` for any function-form `asRef` and
invocation. -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Instructions.CpiAsRef

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.CpiRequest
  Solanalib.Specs.Core.CpiRequest.Checked
open SolanalibTest.Conformance.Library.Borsh

/-! ## Callback combinators at relations with a graph -/

section Graph

variable {S X V W U T : Type}

/-- What `Callback.bind` admits after its first callback returned `g`. -/
def bindRes (g : Outcome S V U T) (k : V → S → Outcome S W U T → Prop) (o : Outcome S W U T) : Prop
  :=
  match g with
  | .returned v s' => k v s' o
  | .unwound r s' => o = .unwound r s'
  | .terminated t => o = .terminated t

theorem bind_graph {R : Callback.Run S X V U T} {k : V → S → Outcome S W U T → Prop}
    {s : S} {x : X} {g : Outcome S V U T} (hR : ∀ i, R s x i ↔ g = i) (o : Outcome S W U T) :
    Callback.bind R k s x o ↔ bindRes g k o := by
  constructor
  · rintro ⟨i, hi, hm⟩
    rw [← (hR i).mp hi] at hm
    exact hm
  · intro h
    exact ⟨g, (hR g).mpr rfl, h⟩

theorem map_graph {R : Callback.Run S X V U T} (f : V → W) {s : S} {x : X} {g : Outcome S V U T}
    (hR : ∀ i, R s x i ↔ g = i) (o : Outcome S W U T) :
    Callback.map f R s x o ↔ Outcome.map f g = o := by
  constructor
  · rintro ⟨i, hi, hm⟩
    rw [← (hR i).mp hi] at hm
    exact hm
  · intro h
    exact ⟨g, (hR g).mpr rfl, h⟩

end Graph

/-! ## The checked v2 path at a function-form `AsRef` -/

section Fn

variable {State Acc U T : Type} (pool : State → AccountView.State)
  (raw : State → AccountView.Handle → RawHeader) (a : State → Acc → Outcome State
    AccountView.Handle U T)

def initFn (s : State) (src : Acc) : Outcome State (Except Error Descriptor) U T :=
  match a s src with
  | .returned account s1 => .returned (.ok (captureV2 (pool s1) (raw s1) account)) s1
  | .unwound r s1 => .unwound r s1
  | .terminated t => .terminated t

theorem init_iff (s : State) (src : Acc) (o : Outcome State (Except Error Descriptor) U T) :
    initializeV2 pool raw (Callback.ofFunction a) s src o ↔ initFn pool raw a s src = o := by
  unfold initializeV2
  rw [bind_graph (g := a s src) (fun _ => Iff.rfl)]
  unfold initFn
  cases a s src <;> exact eq_comm

def checkFn (item : Solanalib.Runtime.CpiMeta) (s : State) (src : Acc) : Outcome State (Except
  Error Descriptor) U T :=
  match a s src with
  | .returned account s1 =>
    if ((pool s1).account account).metadata.address ≠ item.key then .returned (.error
      .InvalidArgument) s1
    else if item.writableByte != 0 then
      match a s1 src with
      | .returned borrowed s2 =>
        if AccountView.isBorrowed (pool s2) borrowed then .returned (.error .AccountBorrowFailed) s2
        else initFn pool raw a s2 src
      | .unwound r s2 => .unwound r s2
      | .terminated t => .terminated t
    else initFn pool raw a s1 src
  | .unwound r s1 => .unwound r s1
  | .terminated t => .terminated t

theorem check_iff (item : Solanalib.Runtime.CpiMeta) (s : State) (src : Acc)
    (o : Outcome State (Except Error Descriptor) U T) :
    checkV2 pool raw (Callback.ofFunction a) item s src o ↔ checkFn pool raw a item s src = o := by
  unfold checkV2
  rw [bind_graph (g := a s src) (fun _ => Iff.rfl)]
  unfold checkFn
  cases a s src with
  | returned account s1 =>
    dsimp only [bindRes]
    by_cases h1 : ((pool s1).account account).metadata.address ≠ item.key
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1)]; exact
      eq_comm
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : (item.writableByte != 0) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
        rw [bind_graph (g := a s1 src) (fun _ => Iff.rfl)]
        cases a s1 src with
        | returned borrowed s2 =>
          dsimp only [bindRes]
          by_cases h3 : AccountView.isBorrowed (pool s2) borrowed = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_left_of_eq_true _ _ (eq_true h3)];
            exact eq_comm
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_right_of_eq_false _ _ (eq_false
            h3)]; exact init_iff pool raw a s2 src o
        | unwound r s2 => exact eq_comm
        | terminated t => exact eq_comm
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false
        h2)]; exact init_iff pool raw a s1 src o
  | unwound r s1 => exact eq_comm
  | terminated t => exact eq_comm

def prepareFn : List Solanalib.Runtime.CpiMeta → List Acc → State →
    Outcome State (Except Error (List Descriptor)) U T
  | [], _, s => .returned (.ok []) s
  | _ :: _, [], s => .returned (.error .NotEnoughAccountKeys) s
  | item :: metas, account :: accounts, s =>
    match checkFn pool raw a item s account with
    | .returned (.error e) s1 => .returned (.error e) s1
    | .returned (.ok d) s1 => Outcome.map (Except.map (d :: ·)) (prepareFn metas accounts s1)
    | .unwound r s1 => .unwound r s1
    | .terminated t => .terminated t

theorem prepare_iff (metas : List Solanalib.Runtime.CpiMeta) (accounts : List Acc) (s : State)
    (o : Outcome State (Except Error (List Descriptor)) U T) :
    prepareV2 pool raw (Callback.ofFunction a) metas accounts s o ↔
      prepareFn pool raw a metas accounts s = o := by
  induction metas generalizing accounts s o with
  | nil => exact eq_comm
  | cons item metas ih =>
    cases accounts with
    | nil => exact eq_comm
    | cons account accounts =>
      simp only [prepareV2, prepareFn]
      rw [bind_graph (check_iff pool raw a item s account) o]
      cases checkFn pool raw a item s account with
      | returned r s1 =>
        cases r with
        | error e => exact eq_comm
        | ok d =>
          dsimp only [bindRes]
          exact map_graph (R := fun next (_ : Unit) => prepareV2 pool raw (Callback.ofFunction a)
            metas accounts next)
            (s := s1) (x := ()) _ (fun i => ih accounts s1 i) o
      | unwound r s1 => exact eq_comm
      | terminated t => exact eq_comm

def innerFn (f : State → Request Descriptor → Outcome State Unit U T) (before : State)
    (request : Request Acc) : Outcome State (Except Error Unit) U T :=
  if request.accounts.length < request.instruction.metas.length then
    .returned (.error .NotEnoughAccountKeys) before
  else match prepareFn pool raw a request.instruction.metas request.accounts before with
    | .returned (.error e) s => .returned (.error e) s
    | .returned (.ok prepared) s =>
      Outcome.map (fun _ => .ok ()) (f s ⟨request.instruction, prepared, request.signers⟩)
    | .unwound r s => .unwound r s
    | .terminated t => .terminated t

/-- The registered v2 inner path, at a function-form `AsRef` and invocation, is `innerFn`. -/
theorem inner_iff (f : State → Request Descriptor → Outcome State Unit U T) (before : State)
    (request : Request Acc) (o : Outcome State (Except Error Unit) U T) :
    innerV2 pool raw (Callback.ofFunction a) (Callback.ofFunction f) before request o ↔
      innerFn pool raw a f before request = o := by
  unfold innerV2 innerFn
  by_cases h : request.accounts.length < request.instruction.metas.length
  · simp only [h, ↓reduceIte]; exact eq_comm
  · simp only [h, ↓reduceIte]
    rw [bind_graph (g := prepareFn pool raw a request.instruction.metas request.accounts before)
      (fun i => prepare_iff pool raw a _ _ before i) o]
    cases prepareFn pool raw a request.instruction.metas request.accounts before with
    | returned r s =>
      cases r with
      | error e => exact eq_comm
      | ok prepared => dsimp only [bindRes]; exact Callback.map_ofFunction _ f s _ o
    | unwound r s => exact eq_comm
    | terminated t => exact eq_comm

end Fn

/-! ## The recording `AsRef` index -/

inductive Step where
  /-- Return the view of this input entry. -/
  | ret (index : Nat)
  /-- Panic with this message. -/
  | panic (message : String)
  deriving DecidableEq

structure RWorld where
  base : Cpi.World
  /-- The unconsumed `as_ref` script. -/
  script : List Step
  /-- The source index of every `as_ref` call so far. -/
  calls : List Nat
  deriving DecidableEq

def rpool (w : RWorld) : AccountView.State := Cpi.pool w.base
def rraw (w : RWorld) : AccountView.Handle → RawHeader := Cpi.rawHeader w.base

/-- `Recording::as_ref`: log the index of the element, then follow the script or return its own
view. -/
def asRefFn (w : RWorld) (src : Nat) : Outcome RWorld AccountView.Handle String Cpi.Terminal :=
  let logged := { w with calls := w.calls ++ [src] }
  match w.script with
  | .ret j :: rest => .returned (Cpi.handleOf w.base.region.entries j) { logged with script := rest
    }
  | .panic m :: rest => .unwound m { logged with script := rest }
  | [] => .returned (Cpi.handleOf w.base.region.entries src) logged

/-- The invocation of the shim, acting on the CPI world. -/
def invokeFn (w : RWorld) (req : Request Descriptor) : Outcome RWorld Unit String Cpi.Terminal :=
  match Cpi.invokeFn w.base req with
  | .returned () b => .returned () { w with base := b }
  | .unwound r b => .unwound r { w with base := b }
  | .terminated t => .terminated t

def arrayTypes : ArrayTypes := ⟨⟨⟨RWorld, rpool, String, Cpi.Terminal⟩, rraw⟩, Nat,
  Callback.ofFunction asRefFn⟩

abbrev Out := Outcome RWorld (Except Error Unit) String Cpi.Terminal

theorem invoke_signed_evaluated (before : RWorld) (args : ArrayCall arrayTypes)
    (h : args.invoke = Callback.ofFunction invokeFn) (o : Out) :
    Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_run arrayTypes before args o ↔
      innerFn rpool rraw asRefFn invokeFn before ⟨args.instruction, args.accounts.values,
        args.signers⟩ = o := by
  show innerV2 rpool rraw (Callback.ofFunction asRefFn) args.invoke before _ o ↔ _
  rw [h]
  exact inner_iff rpool rraw asRefFn invokeFn before _ o

/-! ## Records -/

def step (j : Json) : Result Step :=
  match j.getObjVal? "ret", j.getObjVal? "panic" with
  | .ok i, _ => do pure (.ret (← i.getNat?))
  | _, .ok m => do pure (.panic (← m.getStr?))
  | _, _ => throw s!"unknown as_ref step {j.compress}"

def rworld (state : Json) : Result RWorld := do
  let base ← Cpi.world state
  let r ← field state "as_ref"
  pure ⟨base, ← asList step (← field r "script"), ← asList Json.getNat? (← field r "calls")⟩

def recorded (j : Json) : Result (Option Out) := Cpi.recordedWith (asExcept Cpi.errorOf asUnit)
  rworld j

def outJson : Out → Json
  | .returned r w => returnedJson (exceptJson (fun e => Json.str (Cpi.errorName e)) (fun _ =>
    Json.null) r)
      (Json.mkObj [("cpi_calls", toJson w.base.log.length), ("as_ref_calls", toJson w.calls)])
  | .unwound reason w => Json.mkObj [("exit", "unwound"), ("reason", Json.str reason),
      ("state", Json.mkObj [("cpi_calls", toJson w.base.log.length), ("as_ref_calls", toJson
        w.calls)])]
  | .terminated t => Cpi.terminalJson t

def checker (size : Nat) : Checker where
  function := "solana_instruction_view::cpi::invoke_signed"
  generics := [("ACCOUNTS", toString size), ("A", "conformance_instruction_view_2_1_0_cpi::cpi::Rec\
    ording")]
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_run"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_run"]
  check := fun c => do
    let before ← rworld c.state
    let instruction ← Instructions.instructionOf (← field c.args "instruction")
    let sources ← asList Json.getNat? (← field c.args "accounts")
    let accounts ← Cpi.V2.staticAccounts size sources
    let args : ArrayCall arrayTypes := ⟨instruction, accounts, ← Cpi.signersOf c.args,
      Callback.ofFunction invokeFn⟩
    pure (decideGraph _ _ (invoke_signed_evaluated before args rfl) (← recorded c.outcome) outJson)

end SolanalibTest.Conformance.Library.Families.Instructions.CpiAsRef
