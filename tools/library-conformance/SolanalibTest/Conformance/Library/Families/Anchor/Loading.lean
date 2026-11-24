/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Construct
import Solanalib.Specs.AnchorLang.loading

/-!
# `AccountLoader::load` and `load_mut`

Decided against the primary owned model (`AnchorLoadingOwned.run`, errors in
the registered reference heap) and the observation model (`AnchorAccount.load`,
an executable function), at the layouts of the zero-copy types of the driver:
`Zc` (8-byte discriminator `[1..8]`, 16 bytes, alignment 8) and `Zc16` (32
bytes, alignment 16, misaligned after the discriminator in a loader region).
The data address enters the model only through its residue modulo the
alignment; the record gives it modulo 16.

Observation: cell contents and leases after the call (a returned guard is
still alive), and for a returned guard its view (offset and length in the
data) and the bytes it currently denotes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.Anchor.Loading

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
  SolanalibTest.Conformance.Library.Runtime
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (resultK pgraph_ite
  withGuard_graph Heap BoxId StringId Failure)

def disc : Solanalib.Runtime.Bytes := [1, 2, 3, 4, 5, 6, 7, 8]

def layout (size alignment : Nat) : LoadIndex := ⟨Unit, disc, size, alignment, true⟩

/-! ## Owned model -/

def heapFocus : Owned.Focus (World Heap) Heap := Owned.Focus.snd

def ownedOps : AnchorErrorOwned.Ops (World Heap) StringId BoxId Failure :=
  AnchorErrorOwned.Reference.ops.focus heapFocus

def ownedFn : OpsFn (World Heap) StringId BoxId Failure := RefFn.fn.focus heapFocus

theorem ownedGraph : OpsGraph ownedOps ownedFn := RefFn.graph.focus heapFocus

def types (l : LoadIndex) : AnchorLoadingOwned.Types :=
  ⟨Heap, Failure, StringId, BoxId, ownedOps, l⟩

abbrev W := World Heap
abbrev OErr := AnchorErrorOwned.Error BoxId
abbrev Out (l : LoadIndex) := Outcome W (Except OErr (Mapped l.Payload)) LoadPanic (LoadPanic ⊕
  Failure)

def depFn {V : Type} (x : Option (Outcome W V Empty Failure)) : Option (Outcome W V LoadPanic
  (LoadPanic ⊕ Failure)) :=
  x.map fun
    | .returned v s => .returned v s
    | .unwound e _ => nomatch e
    | .terminated r => .terminated (.inr r)

theorem dep_graph (l : LoadIndex) {A V : Type} {run : Callback.Run W A V Empty Failure}
    {x : Option (Outcome W V Empty Failure)} {b : W} {a : A} (h : PGraph (run b a) x) :
    PGraph (AnchorLoadingOwned.dependency (types l) run b a) (depFn x) := by
  have e : depFn x = x.bind (fun p => depFn (some p)) := by cases x <;> rfl
  rw [e]
  apply PGraph.congr (PGraph.exists_step h fun produced => PGraph.ofOption (depFn (some produced)))
  intro o
  apply exists_congr; intro p
  apply and_congr_right; intro _
  cases p with
  | returned v s => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩
  | unwound e _ => exact nomatch e
  | terminated r => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩

def codeFn (before : W) (failure : Code) : Option (Outcome W OErr LoadPanic (LoadPanic ⊕ Failure))
  :=
  depFn (OwnedFn.buildCodeFn ownedFn before ⟨failure.payload.name, failure.payload.code,
    failure.payload.message⟩)

theorem code_graph (l : LoadIndex) (before : W) (failure : Code) :
    PGraph (AnchorLoadingOwned.code (types l) failure before ()) (codeFn before failure) :=
  dep_graph l (OwnedFn.buildCode_graph ownedGraph before _)

def programFn (before : W) (failure : ProgramError.Value) : Option (Outcome W OErr LoadPanic
  (LoadPanic ⊕ Failure)) :=
  depFn (OwnedFn.fromProgramFn ownedFn before failure)

theorem program_graph (l : LoadIndex) (before : W) (failure : ProgramError.Value) :
    PGraph (AnchorLoadingOwned.program (types l) failure before ()) (programFn before failure) :=
  dep_graph l (OwnedFn.fromProgram_graph ownedGraph before _)

def mapLoadedFn (l : LoadIndex) (args : LoadArgs l) (before : W) (guard : Borrow.Guard) (bytes :
  Solanalib.Runtime.Bytes) :
    Option (Out l) :=
  match AnchorAccount.mapLoaded l args before.1 guard bytes with
  | none => none
  | some (.returned (.error _) _) => none
  | some (.returned (.ok mapped) after) => some (.returned (.ok mapped) (after, before.2))
  | some (.unwound reason after) => some (.unwound reason (after, before.2))
  | some (.terminated reason) => some (.terminated (.inl reason))

theorem mapLoaded_graph (l : LoadIndex) (args : LoadArgs l) (before : W) (guard : Borrow.Guard)
    (bytes : Solanalib.Runtime.Bytes) :
    PGraph (AnchorLoadingOwned.mapLoaded (types l) args before guard bytes) (mapLoadedFn l args
      before guard bytes) := by
  unfold AnchorLoadingOwned.mapLoaded mapLoadedFn
  dsimp only [types]
  rcases AnchorAccount.mapLoaded l args before.1 guard bytes with _ | o
  · exact PGraph.false
  · rcases o with ⟨v, s⟩ | ⟨r, s⟩ | r
    · rcases v with e | m
      · exact PGraph.false
      · exact PGraph.eq_left _
    · exact PGraph.eq_left _
    · exact PGraph.eq_left _

def runFn (mode : Borrow.Mode) (l : LoadIndex) (before : W) (args : LoadArgs l) : Option (Out l) :=
  if mode = .exclusive ∧ args.loader.info.isWritable = false then
    (codeFn before .notMutable).map (Outcome.map Except.error)
  else
    match AccountInfo.tryBorrow mode args.loader.info.data before.1 with
    | (.error failure, during) => (programFn (during, before.2) failure).map (Outcome.map
      Except.error)
    | (.ok guard, during) =>
      match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => none
      | .ok (_, .data bytes) =>
        match AnchorConstructOwned.discriminatorFailure l.discriminator bytes with
        | some failure => ((codeFn (during, before.2) failure).map (Outcome.map Except.error)).bind
            (AccountInfo.GuardCallback.releaseOutcome guard)
        | none => mapLoadedFn l args (during, before.2) guard bytes

theorem run_graph (mode : Borrow.Mode) (l : LoadIndex) (before : W) (args : LoadArgs l) :
    PGraph (AnchorLoadingOwned.run mode (types l) before args) (runFn mode l before args) := by
  unfold AnchorLoadingOwned.run runFn
  apply pgraph_ite
  · exact PGraph.map _ (code_graph l before _)
  · rcases AccountInfo.tryBorrow mode args.loader.info.data before.1 with ⟨borrowed, during⟩
    rcases borrowed with failure | guard
    · exact PGraph.map _ (program_graph l _ _)
    · dsimp only
      rcases Borrow.current during guard with e | ⟨view, content⟩
      · exact PGraph.false
      · rcases content with x | bytes
        · exact PGraph.false
        · dsimp only [types]
          rcases AnchorConstructOwned.discriminatorFailure l.discriminator bytes with _ | failure
          · exact mapLoaded_graph l args _ guard bytes
          · exact withGuard_graph guard (PGraph.map _ (code_graph l _ _))

/-! ## Observation -/

structure MappedObs where
  offset : Nat
  length : Nat
  bytes : Solanalib.Runtime.Bytes
  deriving DecidableEq

/-- The view and current bytes of a returned guard. -/
def mappedObs (s : AccountInfo.State) (guard : Borrow.Guard) : Option MappedObs :=
  match s.resolve guard with
  | some slot =>
    match slot.view, (Borrow.deref AccountInfo.projectBytes s guard).1 with
    | .bytesRange offset length, .ok (.ok bytes) => some ⟨offset, length, bytes⟩
    | _, _ => none
  | none => none

abbrev LoadObs := Outcome WorldObs (Except (Option ErrorValue) (Option MappedObs)) LoadPanic Unit

/-- `load`/`load_mut` slice `data[8..8 + size_of::<T>()]` after checking the
discriminator: the one slice-bounds message Rust gives for data of this length
(`sliceFailMessage`). -/
def asLoadPanic (size dataLength : Nat) (r : String) : Option LoadPanic :=
  if r = sliceFailMessage 8 (8 + size) dataLength then
    some .sliceBounds
  else if r = "from_bytes>TargetAlignmentGreaterAndInputNotAligned" ||
      r = "from_bytes_mut>TargetAlignmentGreaterAndInputNotAligned" then some .castAlignment
  else if r = "attempt to add with overflow" then some .lengthOverflow
  else none

def loadPanicJson : LoadPanic → Json
  | .sliceBounds => "slice bounds"
  | .castAlignment => "cast alignment"
  | .lengthOverflow => "length overflow"

def asMappedObs (j : Json) : Result (Option MappedObs) := do
  pure (some ⟨← natField j "offset", ← natField j "length", ← asBytes (← field j "bytes")⟩)

def mappedJson : Option MappedObs → Json
  | none => "<no view>"
  | some m => Json.mkObj [("offset", toJson m.offset), ("length", toJson m.length), ("bytes",
    bytesJson m.bytes)]

def asLoadObs (size dataLength : Nat) (j : Json) : Result (Option LoadObs) :=
  parseOutcome (asExcept (fun e => do pure (some (← asErrorValue e))) asMappedObs) asWorldObs
    (asLoadPanic size dataLength) noReason j

def loadObsJson : Option LoadObs → Json
  | none => "<no outcome>"
  | some (.returned v s) => returnedJson (match v with
      | .ok m => okJson (mappedJson m)
      | .error e => errJson (optionJson errorValueJson e)) (worldObsJson s)
  | some (.unwound r s) => Json.mkObj [("exit", "unwound"), ("reason", loadPanicJson r), (
    "state",
    worldObsJson s)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def project {S E P T : Type} (input : LoaderInput) (cells : S → AccountInfo.State)
    (err : S → E → Option ErrorValue) : Outcome S (Except E (Mapped P)) LoadPanic T → LoadObs
  | .returned v s => .returned (match v with
      | .ok m => .ok (mappedObs (cells s) m.guard)
      | .error e => .error (err s e)) (observeWorld input (inputOwners input) (cells s))
  | .unwound r s => .unwound r (observeWorld input (inputOwners input) (cells s))
  | .terminated _ => .terminated ()

/-! ## Checkers -/

def both (owned observation : Verdict) : Verdict :=
  ⟨owned.admitted && observation.admitted,
    Json.mkObj [("model", owned.expected), ("observation_model", observation.expected)]⟩

def heap0 : Heap := ⟨[], [], Owned.budget, []⟩

def loadChecker (mutable : Bool) (ty : String) (size alignment : Nat) : Checker :=
  let mode : Borrow.Mode := if mutable then .exclusive else .shared
  let name := if mutable then "load_mut" else "load"
  ofModels s!"anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::{name}" [(
    "T", ty)]
    (s!"Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.{name}_run \
      (reference heap) " ++
      s!"+ \
        Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.{name}_observation\
        _run")
    [s!"Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.{name}_run",
      s!"Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.{name}_observatio\
        n_run"]
    fun c => do
      let (input, world) ← asWorld c.state
      let info ← infoAt input (← natField c.args "account")
      let l := layout size alignment
      let args : LoadArgs l := ⟨profile, ⟨info⟩, ← natField c.args "data_address"⟩
      let recorded ← asLoadObs size (dataLength world info.data) c.outcome
      let ownedRel : Out l → Prop := fun o =>
        if mutable then
          accounts.account_loader.AccountLoader.load_mut_run (types l)
          (world, heap0) args o
        else accounts.account_loader.AccountLoader.load_run (types l)
          (world, heap0) args o
      have ownedGraph : PGraph ownedRel (runFn mode l (world, heap0) args) := by
        cases mutable
        · exact run_graph .shared l (world, heap0) args
        · exact run_graph .exclusive l (world, heap0) args
      let owned := decideProjected ownedRel _ ownedGraph
        (project input Prod.fst (fun s e => AnchorErrorOwned.current ownedOps s e)) recorded
          loadObsJson
      let obsRel : LoadOutcome l → Prop := fun o =>
        if mutable then
          accounts.account_loader.AccountLoader.load_mut_observation_run
          l world args o
        else accounts.account_loader.AccountLoader.load_observation_run
          l world args o
      have obsGraph : PGraph obsRel (load mode l world args) := by
        cases mutable
        · exact PGraph.ofOption _
        · exact PGraph.ofOption _
      let observation := decideProjected obsRel _ obsGraph (project input id (fun _ e => some e))
        recorded loadObsJson
      return [owned, observation]

def checkers : List Checker := [
  loadChecker false "conformance_anchor::script::Zc" 16 8,
  loadChecker false "conformance_anchor::script::Zc16" 32 16,
  loadChecker true "conformance_anchor::script::Zc" 16 8,
  loadChecker true "conformance_anchor::script::Zc16" 32 16].map (withFrame [("no syscalls",
    noSyscalls)])

end SolanalibTest.Conformance.Library.Families.Anchor.Loading
