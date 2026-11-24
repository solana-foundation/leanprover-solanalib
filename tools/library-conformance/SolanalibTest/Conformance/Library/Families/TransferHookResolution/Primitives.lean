/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.Core.TransferHookResolutionFacts
import Solanalib.Specs.Core.TransferHookResolutionSample
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainCollect
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainLiteral

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TransferHookResolution

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.TransferHookResolution
open Solanalib.Specs.Core.Token (Error Bytes)
open Solanalib.Specs.Core.Token.AllocatedControl (DataRef)
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims (VecPrims RcPrims
  ArrayPrims NoAgain)
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc
  (liftCloneF liftClone_fn liftDropF liftDrop_fn)
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv (eq_iff_some)

abbrev RunF (types : Types) (Value : Type) :=
  RRun (World types.Extra) Value types.Unwind types.Terminal

abbrev DropF (types : Types) :=
  World types.Extra → Option (Outcome (World types.Extra) Unit types.Unwind types.Terminal)

/-- Executable primitive interpretations with exact relation/function proofs.
No whole-helper answer is supplied. Collection and literal scheduling are
restricted only for this executable checker, not the registered model. -/
structure Prims (types : Types) where
  bytes : VecPrims types.bytes
  metas : VecPrims types.metas
  infos : VecPrims types.infos
  discriminators : VecPrims types.discriminators
  seedBytes : VecPrims types.seedOps.bytes
  seeds : VecPrims types.seedOps.seeds
  seedRefs : VecPrims types.seedOps.refs
  rc : RcPrims types.rc
  array : ArrayPrims types.literalProvider
  noAgain : NoAgain types.literalProvider
  pdaF : World types.Extra → Address.Syscall.PdaRequest →
    Option (Outcome (World types.Extra) Address.Operations.ZeroFindReply types.Unwind
      types.Terminal)
  pda_fn : Fn types.pdaSyscall pdaF
  raiseF : World types.Extra → Panic →
    Option (Outcome (World types.Extra) Empty types.Unwind types.Terminal)
  raise_fn : Fn types.raise raiseF
  dbl : World types.Extra → types.Unwind → types.Unwind → types.Terminal
  double_fn : ∀ s o l t, types.doubleUnwind s o l t ↔ t = dbl s o l
  collectFinishF : World types.Extra → List GuardElement →
    Option (Outcome (World types.Extra) types.GuardResource types.Unwind types.Terminal)
  collectFinish_fn : Fn types.collection.finish collectFinishF
  collectRetireF : Option types.GuardResource → List GuardElement → DropF types
  collectRetire_fn : ∀ resource acquired,
    DFn (types.collection.retire resource acquired) (collectRetireF resource acquired)
  collect_no_internal : ∀ index acquired before outcome,
    ¬ types.collection.internal index acquired before outcome
  collect_order : ∀ before acquired, types.collection.partialOrder before acquired = acquired

variable {types : Types}

def findPdaF (P : Prims types) (before : World types.Extra) (inputs : Address.Syscall.PdaInputs) :=
  ((P.pdaF before (Address.Operations.zeroFindRequest inputs)).map
    (Outcome.map Address.Operations.zeroFindDecode)).bind (thenOpt · fun value after =>
      match value with
      | some pair => some (.returned pair after)
      | none => (P.raiseF after .noViableProgramAddress).map
          (Outcome.map (fun impossible : Empty => nomatch impossible)))

theorem findPda_fn (P : Prims types) : Fn types.findPda (findPdaF P) := by
  intro before inputs outcome
  apply bind_fn (map_fn P.pda_fn Address.Operations.zeroFindDecode)
  intro value after result
  cases value with
  | some pair => exact eq_iff_some _ _
  | none => exact map_fn (fun s _ o => P.raise_fn s .noViableProgramAddress o) _ after () result

def borrowDataF (types : Types) (info : AccountInfo.Value) : RunF types DataRef :=
  fun before =>
    let (step, after) := Token.Onchain.borrowData true before.1 info
    match step with
    | .success reference =>
      some (.returned (.ok ⟨reference.guard, reference.bytes.length⟩) (after, before.2))
    | .error error => some (.returned (.error error) (after, before.2))
    | .panic _ | .malformed => none

theorem borrowData_fn (types : Types) (info : AccountInfo.Value) :
    RFn (borrowData types info) (borrowDataF types info) := by
  intro before outcome
  unfold borrowData borrowDataF
  rcases Token.Onchain.borrowData true before.1 info with ⟨step, after⟩
  cases step <;> first | exact eq_iff_some _ _ | exact ⟨False.elim, fun h => by cases h⟩

def withDataF {Value : Type} (P : Prims types) (info : AccountInfo.Value)
    (body : DataRef → RunF types Value) : RunF types Value :=
  bindR (borrowDataF types info) fun reference =>
    scopeR P.dbl [DataRef.dropF reference] (body reference)

theorem withData_fn {Value : Type} (P : Prims types) (info : AccountInfo.Value)
    (body : DataRef → Run types Value) (bodyF : DataRef → RunF types Value)
    (correct : ∀ reference, RFn (body reference) (bodyF reference)) :
    RFn (withData types info body) (withDataF P info bodyF) :=
  bindR_fn (borrowData_fn types info) fun reference =>
    scopeR_fn P.double_fn (.cons (DataRef.drop_fn reference) .nil) (correct reference)

/-- `cloneInfo`, computed. -/
def cloneInfoF (P : Prims types) (info : AccountInfo.Value) : RunF types AccountInfo.Value :=
  performR fun s => liftCloneF P.rc s info

/-- `cloneInfo types info` admits exactly `cloneInfoF P info`. -/
theorem cloneInfo_fn (P : Prims types) (info : AccountInfo.Value) :
    RFn (cloneInfo types info) (cloneInfoF P info) :=
  performCall_fn (liftClone_fn P.rc) info

/-- `pushClonedInfo`, computed: clone, then push the clone. -/
def pushClonedInfoF (P : Prims types) (resource : types.InfoResource) (info : AccountInfo.Value) :
    RunF types Unit :=
  bindR (cloneInfoF P info) fun cloned => performR fun s => P.infos.pushF s (resource, cloned)

/-- `pushClonedInfo types resource info` admits exactly `pushClonedInfoF P resource info`. -/
theorem pushClonedInfo_fn (P : Prims types) (resource : types.InfoResource)
    (info : AccountInfo.Value) :
    RFn (pushClonedInfo types resource info) (pushClonedInfoF P resource info) :=
  bindR_fn (cloneInfo_fn P info) fun cloned => performCall_fn P.infos.push_fn (resource, cloned)

/-- `dropInfo`, computed. -/
def dropInfoF (P : Prims types) (info : AccountInfo.Value) : DropF types :=
  fun s => liftDropF P.rc s info

/-- `dropInfo types info` admits exactly `dropInfoF P info`. -/
theorem dropInfo_fn (P : Prims types) (info : AccountInfo.Value) :
    DFn (dropInfo types info) (dropInfoF P info) :=
  fun s o => liftDrop_fn P.rc s info o

/-- `argumentDrops`, computed: authority, destination, mint, source. -/
def argumentDropsF (P : Prims types) (args : Args types) : List (DropF types) :=
  [dropInfoF P args.authority, dropInfoF P args.destination, dropInfoF P args.mint,
    dropInfoF P args.source]

/-- Each of `argumentDrops types args` admits exactly the computed drop. -/
theorem argumentDrops_fn (P : Prims types) (args : Args types) :
    All2 DFn (argumentDrops types args) (argumentDropsF P args) :=
  .cons (dropInfo_fn P _) (.cons (dropInfo_fn P _) (.cons (dropInfo_fn P _)
    (.cons (dropInfo_fn P _) .nil)))

/-- `instructionDrops`, computed: metadata, then bytes. -/
def instructionDropsF (P : Prims types)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    List (DropF types) :=
  [P.metas.dropActionF instruction.metas, P.bytes.dropActionF instruction.data]

/-- Each of `instructionDrops types instruction` admits exactly the computed drop. -/
theorem instructionDrops_fn (P : Prims types)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    All2 DFn (instructionDrops types instruction) (instructionDropsF P instruction) :=
  .cons (P.metas.dropAction_fn _) (.cons (P.bytes.dropAction_fn _) .nil)

/-- `executeRemainder`, computed: the arguments not yet moved, in reverse order. -/
def executeRemainderF (P : Prims types) (args : Args types) (completed : Nat) :
    List (DropF types) :=
  ([args.source, args.mint, args.destination, args.authority].drop completed).reverse.map
    (dropInfoF P)

/-- Each of `executeRemainder types args completed` admits exactly the computed drop. -/
theorem executeRemainder_fn (P : Prims types) (args : Args types) (completed : Nat) :
    All2 DFn (executeRemainder types args completed) (executeRemainderF P args completed) :=
  All2.map (dropInfo types) (dropInfoF P) (dropInfo_fn P) _

/-- `executeInfoAt`, computed: the four moved arguments, then the clone of the
validation account; no outcome for an index out of range. -/
def executeInfoAtF (P : Prims types) (args : Args types) (validation : AccountInfo.Value) :
    World types.Extra → Nat →
      Option (Outcome (World types.Extra) AccountInfo.Value types.Unwind types.Terminal) :=
  fun s index =>
    match index with
    | 0 => some (.returned args.source s)
    | 1 => some (.returned args.mint s)
    | 2 => some (.returned args.destination s)
    | 3 => some (.returned args.authority s)
    | 4 => liftCloneF P.rc s validation
    | _ + 5 => none

/-- `executeInfoAt types args validation` admits exactly
`executeInfoAtF P args validation`. -/
theorem executeInfoAt_fn (P : Prims types) (args : Args types) (validation : AccountInfo.Value) :
    Fn (executeInfoAt types args validation) (executeInfoAtF P args validation) := by
  intro s index o
  unfold executeInfoAt executeInfoAtF
  match index with
  | 0 => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | 1 => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | 2 => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | 3 => exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | 4 => exact liftClone_fn P.rc s validation o
  | _ + 5 => exact ⟨False.elim, fun h => by cases h⟩


end SolanalibTest.Conformance.Library.Families.TransferHookResolution
