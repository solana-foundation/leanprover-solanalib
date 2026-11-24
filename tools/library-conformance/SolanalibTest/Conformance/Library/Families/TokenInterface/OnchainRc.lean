/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

/-!
# AccountInfo clones, drops and drop lists, computed

The derived `Clone` and the destructor of AccountInfo run two Rc dependency calls, lamports first
(`AccountInfoRc.cloneCall`, `dropCall`). This module computes
them from an `RcPrims` bundle, and from them every AccountInfo clone and drop
of the onchain model: `cloneInfo`, `dropInfo`, the argument drops, the literal
expressions of the two account arrays (`initialInfoAt`, `executeInfoAt`) and
the bundle of the literal provider (`literalPrims`). It also computes the drop
lists that several components share (`instructionDrops`, `Prepared.drops`,
`executeRemainder`) and `pushClonedInfo`, which the multisig and hook
components both use.

For the closed index, `cloneInfos` and `rcInfosOps` give the
AccountInfo vector of `Witness.infosOps` over any base vector and any Rc
dependency: `extend` clones each appended element, and `dropEachOps` drops
each current element before the base destructor. `rcInfosPrims` bundles it.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

/-! ## The two Rc calls of a clone and a drop -/

section Rc

variable {S U T : Type} {rc : AccountInfoRc.Ops S T}

/-- `AccountInfoRc.cloneCall`, computed: clone the lamports Rc, then the data Rc. -/
def cloneCallF (R : RcPrims rc) :
    S → AccountInfo.Value → Option (Outcome S AccountInfo.Value Empty T) :=
  fun s info => (R.cloneRcF s (.lamports, info.lamports)).bind (thenOpt · fun _ after =>
    (R.cloneRcF after (.data, info.data)).map (Outcome.map fun _ => AccountInfo.clone info))

/-- `AccountInfoRc.cloneCall rc` admits exactly `cloneCallF R`. -/
theorem cloneCall_fn (R : RcPrims rc) : Fn (AccountInfoRc.cloneCall rc) (cloneCallF R) :=
  fun s info o =>
    bind_fn (fun s _ o => R.cloneRc_fn s (.lamports, info.lamports) o)
      (fun _ after o => map_fn (fun s _ o => R.cloneRc_fn s (.data, info.data) o) _ after () o)
      s () o

/-- `AccountInfoRc.dropCall`, computed: drop the lamports Rc, then the data Rc. -/
def dropCallF (R : RcPrims rc) : S → AccountInfo.Value → Option (Outcome S Unit Empty T) :=
  fun s info => (R.dropRcF s (.lamports, info.lamports)).bind (thenOpt · fun _ after =>
    R.dropRcF after (.data, info.data))

/-- `AccountInfoRc.dropCall rc` admits exactly `dropCallF R`. -/
theorem dropCall_fn (R : RcPrims rc) : Fn (AccountInfoRc.dropCall rc) (dropCallF R) :=
  fun s info o =>
    bind_fn (fun s _ o => R.dropRc_fn s (.lamports, info.lamports) o)
      (fun _ after o => R.dropRc_fn after (.data, info.data) o) s () o

/-- The lifted clone, a Callback-level run with any unwind type. -/
def liftCloneF (R : RcPrims rc) :
    S → AccountInfo.Value → Option (Outcome S AccountInfo.Value U T) :=
  AccountInfoRc.liftF (cloneCallF R)

/-- `AccountInfoRc.lift (cloneCall rc)` admits exactly `liftCloneF R`. -/
theorem liftClone_fn (R : RcPrims rc) :
    Fn (AccountInfoRc.lift (Unwind := U) (AccountInfoRc.cloneCall rc)) (liftCloneF R) :=
  AccountInfoRc.lift_fn (cloneCall_fn R)

/-- The lifted drop, a Callback-level run with any unwind type. -/
def liftDropF (R : RcPrims rc) : S → AccountInfo.Value → Option (Outcome S Unit U T) :=
  AccountInfoRc.liftF (dropCallF R)

/-- `AccountInfoRc.lift (dropCall rc)` admits exactly `liftDropF R`. -/
theorem liftDrop_fn (R : RcPrims rc) :
    Fn (AccountInfoRc.lift (Unwind := U) (AccountInfoRc.dropCall rc)) (liftDropF R) :=
  AccountInfoRc.lift_fn (dropCall_fn R)

/-! ## AccountInfo vectors over a base vector -/

/-- Clone each AccountInfo of a list, in order (as `Witness.cloneInfos`). -/
def cloneInfos (rc : AccountInfoRc.Ops S T) :
    List AccountInfo.Value → Callback.Run S Unit Unit U T :=
  forEach (AccountInfoRc.lift (AccountInfoRc.cloneCall rc))

/-- `cloneInfos`, computed. -/
def cloneInfosF (R : RcPrims rc) :
    List AccountInfo.Value → S → Unit → Option (Outcome S Unit U T) :=
  forEachF (liftCloneF R)

/-- `cloneInfos rc values` admits exactly `cloneInfosF R values`. -/
theorem cloneInfos_fn (R : RcPrims rc) :
    ∀ values, Fn (cloneInfos (U := U) rc values) (cloneInfosF R values) :=
  forEach_fn (liftClone_fn R)

/-- The AccountInfo vector of `Witness.infosOps` over a base vector: `extend`
clones each appended element (`cloneInfos`) before the base `extend`, and
`dropEachOps` drops each current element before the base destructor.
The other operations are those of `base`; in particular `fromList` moves
elements that the literal constructor has already cloned. -/
def rcInfosOps {Res : Type} (base : Owned.VectorOps S AccountInfo.Value Res U T)
    (rc : AccountInfoRc.Ops S T) : Owned.VectorOps S AccountInfo.Value Res U T :=
  { dropEachOps base (AccountInfoRc.lift (AccountInfoRc.dropCall rc)) with
    extend := fun before (resource, values) outcome =>
      Callback.bind (cloneInfos rc values)
        (fun _ state result => base.extend state (resource, values) result) before () outcome }

/-- `rcInfosOps base rc` is bundled from a bundle of `base` and of `rc`. -/
def rcInfosPrims {Res : Type} {base : Owned.VectorOps S AccountInfo.Value Res U T}
    (hb : VecPrims base) (R : RcPrims rc) : VecPrims (rcInfosOps base rc) where
  withCapacityF := hb.withCapacityF
  withCapacity_fn := hb.withCapacity_fn
  fromListF := hb.fromListF
  fromList_fn := hb.fromList_fn
  pushF := hb.pushF
  push_fn := hb.push_fn
  extendF := fun s a => (cloneInfosF R a.2 s ()).bind (thenOpt · fun _ st => hb.extendF st a)
  extend_fn := by
    rintro s ⟨resource, values⟩ o
    exact bind_fn (cloneInfos_fn R values)
      (fun _ st o => hb.extend_fn st (resource, values) o) s () o
  dropF := dropEachF hb (liftDropF R)
  drop_fn := dropEach_fn hb (liftDrop_fn R)

end Rc

/-! ## Clones and drops of the model -/

section Model

variable {types : Types}

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
def argumentDropsF (P : Prims types) (args : Onchain.Args) : List (DropF types) :=
  [dropInfoF P args.authority, dropInfoF P args.destination, dropInfoF P args.mint,
    dropInfoF P args.source]

/-- Each of `argumentDrops types args` admits exactly the computed drop. -/
theorem argumentDrops_fn (P : Prims types) (args : Onchain.Args) :
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

/-- `Prepared.drops`, computed: the info vector, then the instruction. -/
def preparedDropsF (P : Prims types) (prepared : Prepared types) : List (DropF types) :=
  P.infos.dropActionF prepared.infos :: instructionDropsF P prepared.instruction

/-- Each of `prepared.drops types` admits exactly the computed drop. -/
theorem preparedDrops_fn (P : Prims types) (prepared : Prepared types) :
    All2 DFn (prepared.drops types) (preparedDropsF P prepared) :=
  .cons (P.infos.dropAction_fn _) (instructionDrops_fn P _)

/-- `executeRemainder`, computed: the arguments not yet moved, in reverse order. -/
def executeRemainderF (P : Prims types) (args : Onchain.Args) (completed : Nat) :
    List (DropF types) :=
  ([args.source, args.mint, args.destination, args.authority].drop completed).reverse.map
    (dropInfoF P)

/-- Each of `executeRemainder types args completed` admits exactly the computed drop. -/
theorem executeRemainder_fn (P : Prims types) (args : Onchain.Args) (completed : Nat) :
    All2 DFn (executeRemainder types args completed) (executeRemainderF P args completed) :=
  All2.map (dropInfo types) (dropInfoF P) (dropInfo_fn P) _

/-- `initialInfoAt`, computed: the clone of source, mint, destination or
authority; no outcome for an index out of range. -/
def initialInfoAtF (P : Prims types) (args : Onchain.Args) :
    World types.Extra → Nat →
      Option (Outcome (World types.Extra) AccountInfo.Value types.Unwind types.Terminal) :=
  fun s index =>
    match [args.source, args.mint, args.destination, args.authority][index]? with
    | some info => liftCloneF P.rc s info
    | none => none

/-- `initialInfoAt types args` admits exactly `initialInfoAtF P args`. -/
theorem initialInfoAt_fn (P : Prims types) (args : Onchain.Args) :
    Fn (initialInfoAt types args) (initialInfoAtF P args) := by
  intro s index o
  unfold initialInfoAt initialInfoAtF
  cases [args.source, args.mint, args.destination, args.authority][index]? with
  | some info => exact liftClone_fn P.rc s info o
  | none => exact ⟨False.elim, fun h => by cases h⟩

/-- `executeInfoAt`, computed: the four moved arguments, then the clone of the
validation account; no outcome for an index out of range. -/
def executeInfoAtF (P : Prims types) (args : Onchain.Args) (validation : AccountInfo.Value) :
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
theorem executeInfoAt_fn (P : Prims types) (args : Onchain.Args) (validation : AccountInfo.Value) :
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

/-- The literal provider `types.literalProvider` is bundled: its `work`,
`finish` and `retire` from `P`, its element drop the Rc drop, and its
double-unwind policy `doubleUnwind`. -/
def literalPrims (P : Prims types) : ArrayPrims types.literalProvider where
  workF := P.literalWorkF
  work_fn := P.literalWork_fn
  finishF := P.literalFinishF
  finish_fn := P.literalFinish_fn
  dropF := liftDropF P.rc
  drop_fn := liftDrop_fn P.rc
  retireF := P.literalRetireF
  retire_fn := P.literalRetire_fn
  dbl := P.dbl
  double_fn := P.double_fn

end Model

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc
