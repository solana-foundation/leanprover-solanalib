/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
import Solanalib.Specs.Core.TokenRequestAllocatedHooks

/-!
# Computed primitives of the Token-2022 onchain model

`Token.OnchainAllocated.Types` supplies the primitive dependencies of the
operational model as relations: vector operations, the literal-array
constructor, the two Rc calls, the PDA syscall, the panic dependency, the
double-unwind policy and the metadata write. `Prims types` bundles, for each
of them, a computed function and the proof that the relation admits exactly
the computed outcome. The two `Dependencies` (collection and CPI) have their
own bundle, `DepPrims`.

The components of `invokeF` prove their lemmas over any `types` with a
`Prims types`, so that they do not depend on the closed index; the closed index
supplies one bundle. `current`, `empty`, `ownerAt`, `wordBits`,
`tokenEnumSize` and the `cleanupOrder` of the literal are already functions and
have no field here. The `drop` of the literal and `double` are replaced in
`Types.literalProvider` by the Rc drop and `doubleUnwind`, so only its `work`,
`finish` and `retire` are fields; `OnchainRc.literalPrims` assembles the bundle of the
provider.

The section on vectors also builds bundles for common vector instances: the
reference ledger `Owned.vectorReference`, a focus of any bundled vector, and a
vector whose destructor drops each element (`dropEachOps`). The last section
computes `Types.findPda`, which two components use.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl

/-- A computed run of the model at `types`: the computed form of
`OnchainAllocated.Run types V`. -/
abbrev RunF (types : Types) (V : Type) := RRun (World types.Extra) V types.Unwind types.Terminal

/-- A computed drop action at `types`: the computed form of an
`Owned.DropAction (World types.Extra) types.Unwind types.Terminal`. -/
abbrev DropF (types : Types) :=
  World types.Extra → Option (Outcome (World types.Extra) Unit types.Unwind types.Terminal)

/-! ## Vector dependencies -/

section Vector

variable {S E Res U T : Type}

/-- Computed forms of the five relational operations of a vector dependency,
each with its `Fn` proof. -/
structure VecPrims (ops : Owned.VectorOps S E Res U T) where
  /-- Computed `withCapacity`. -/
  withCapacityF : S → Nat → Option (Outcome S Res U T)
  /-- `ops.withCapacity` admits exactly `withCapacityF`. -/
  withCapacity_fn : Fn ops.withCapacity withCapacityF
  /-- Computed `fromList`. -/
  fromListF : S → List E → Option (Outcome S Res U T)
  /-- `ops.fromList` admits exactly `fromListF`. -/
  fromList_fn : Fn ops.fromList fromListF
  /-- Computed `push`. -/
  pushF : S → Res × E → Option (Outcome S Unit U T)
  /-- `ops.push` admits exactly `pushF`. -/
  push_fn : Fn ops.push pushF
  /-- Computed `extend`. -/
  extendF : S → Res × List E → Option (Outcome S Unit U T)
  /-- `ops.extend` admits exactly `extendF`. -/
  extend_fn : Fn ops.extend extendF
  /-- Computed `drop`. -/
  dropF : S → Res → Option (Outcome S Unit U T)
  /-- `ops.drop` admits exactly `dropF`. -/
  drop_fn : Fn ops.drop dropF

/-- The computed form of `ops.dropAction resource`. -/
def VecPrims.dropActionF {ops : Owned.VectorOps S E Res U T} (h : VecPrims ops) (resource : Res) :
    S → Option (Outcome S Unit U T) :=
  fun s => h.dropF s resource

/-- `ops.dropAction resource` admits exactly `h.dropActionF resource`. -/
theorem VecPrims.dropAction_fn {ops : Owned.VectorOps S E Res U T} (h : VecPrims ops)
    (resource : Res) : DFn (ops.dropAction resource) (h.dropActionF resource) :=
  fun s o => h.drop_fn s resource o

/-- The reference ledger `Owned.vectorReference` is computed by `modifyF`,
`retireF` and `VectorState.allocate`. -/
def VecPrims.reference :
    VecPrims (Owned.vectorReference (Element := E) (Unwind := U) (Terminal := T)) where
  withCapacityF := fun s _ => some (.returned (s.allocate []).1 (s.allocate []).2)
  withCapacity_fn := returnsOf_fn (fun (s : Owned.VectorState E) (_ : Nat) => s.allocate [])
  fromListF := fun s values => some (.returned (s.allocate values).1 (s.allocate values).2)
  fromList_fn := returnsOf_fn Owned.VectorState.allocate
  pushF := fun s a => modifyF s a.1 (· ++ [a.2])
  push_fn := vpush_fn
  extendF := fun s a => modifyF s a.1 (· ++ a.2)
  extend_fn := vextend_fn
  dropF := fun s r => retireF s r
  drop_fn := vdrop_fn

/-- A bundled vector, focused into a larger state (`VectorOps.focus`). -/
def VecPrims.focus {Outer Inner : Type} {ops : Owned.VectorOps Inner E Res U T}
    (h : VecPrims ops) (part : Owned.Focus Outer Inner) : VecPrims (ops.focus part) where
  withCapacityF := fun s a => (h.withCapacityF (part.get s) a).map (part.liftOutcome s)
  withCapacity_fn := lift_fn part h.withCapacity_fn
  fromListF := fun s a => (h.fromListF (part.get s) a).map (part.liftOutcome s)
  fromList_fn := lift_fn part h.fromList_fn
  pushF := fun s a => (h.pushF (part.get s) a).map (part.liftOutcome s)
  push_fn := lift_fn part h.push_fn
  extendF := fun s a => (h.extendF (part.get s) a).map (part.liftOutcome s)
  extend_fn := lift_fn part h.extend_fn
  dropF := fun s a => (h.dropF (part.get s) a).map (part.liftOutcome s)
  drop_fn := lift_fn part h.drop_fn

/-- A vector whose destructor first drops each current element in order with
`dropElement`, then runs the destructor of `base`. A missing resource has no
destructor outcome. The infos vector (`OnchainRc.rcInfosOps`) and the guards
vector of the closed index follow this pattern. -/
def dropEachOps (base : Owned.VectorOps S E Res U T) (dropElement : Callback.Run S E Unit U T) :
    Owned.VectorOps S E Res U T :=
  { base with
    drop := fun before resource outcome =>
      ∃ values, base.current before resource = some values ∧
        Callback.bind (forEach dropElement values)
          (fun _ state result => base.drop state resource result) before () outcome }

/-- The computed destructor of `dropEachOps`. -/
def dropEachF {base : Owned.VectorOps S E Res U T} (hb : VecPrims base)
    (dropElementF : S → E → Option (Outcome S Unit U T)) (s : S) (resource : Res) :
    Option (Outcome S Unit U T) :=
  (base.current s resource).bind fun values =>
    (forEachF dropElementF values s ()).bind (thenOpt · fun _ st => hb.dropF st resource)

/-- The destructor of `dropEachOps base dropElement` admits exactly `dropEachF`. -/
theorem dropEach_fn {base : Owned.VectorOps S E Res U T} (hb : VecPrims base)
    {dropElement : Callback.Run S E Unit U T} {dropElementF : S → E → Option (Outcome S Unit U T)}
    (hd : Fn dropElement dropElementF) :
    Fn (dropEachOps base dropElement).drop (dropEachF hb dropElementF) := by
  intro s resource o
  have step := fun values => bind_fn (forEach_fn hd values)
    (fun _ st o => hb.drop_fn st resource o) s () o
  constructor
  · rintro ⟨values, hv, hrun⟩
    show (base.current s resource).bind _ = _
    rw [hv, Option.bind_some]
    exact (step values).1 hrun
  · intro h
    change (base.current s resource).bind _ = _ at h
    cases hv : base.current s resource with
    | none => rw [hv] at h; cases h
    | some values =>
      rw [hv, Option.bind_some] at h
      exact ⟨values, hv, (step values).2 h⟩

/-- `dropEachOps base dropElement` is bundled: all operations but `drop` are
those of `base`. -/
def dropEachPrims {base : Owned.VectorOps S E Res U T} (hb : VecPrims base)
    {dropElement : Callback.Run S E Unit U T} {dropElementF : S → E → Option (Outcome S Unit U T)}
    (hd : Fn dropElement dropElementF) : VecPrims (dropEachOps base dropElement) where
  withCapacityF := hb.withCapacityF
  withCapacity_fn := hb.withCapacity_fn
  fromListF := hb.fromListF
  fromList_fn := hb.fromList_fn
  pushF := hb.pushF
  push_fn := hb.push_fn
  extendF := hb.extendF
  extend_fn := hb.extend_fn
  dropF := dropEachF hb dropElementF
  drop_fn := dropEach_fn hb hd

end Vector

/-! ## Other generic dependencies -/

section Generic

variable {S E Res U T : Type}

/-- Computed forms of the two AccountInfo Rc dependencies. -/
structure RcPrims (rc : AccountInfoRc.Ops S T) where
  /-- Computed Rc clone of one field of a cell. -/
  cloneRcF : S → AccountInfoRc.Field × Borrow.Handle → Option (Outcome S Unit Empty T)
  /-- `rc.cloneRc` admits exactly `cloneRcF`. -/
  cloneRc_fn : Fn rc.cloneRc cloneRcF
  /-- Computed Rc drop of one field of a cell. -/
  dropRcF : S → AccountInfoRc.Field × Borrow.Handle → Option (Outcome S Unit Empty T)
  /-- `rc.dropRc` admits exactly `dropRcF`. -/
  dropRc_fn : Fn rc.dropRc dropRcF

/-- Computed forms of every relational field of an array-literal provider.
`cleanupOrder` is already a function. -/
structure ArrayPrims (provider : Owned.Array.Provider S E Res U T) where
  /-- Computed construction work. -/
  workF : S → Nat × List E → Option (Outcome S Owned.Array.Command U T)
  /-- `provider.work` admits exactly `workF`. -/
  work_fn : Fn provider.work workF
  /-- Computed completion. -/
  finishF : S → List E → Option (Outcome S Res U T)
  /-- `provider.finish` admits exactly `finishF`. -/
  finish_fn : Fn provider.finish finishF
  /-- Computed element drop. -/
  dropF : S → E → Option (Outcome S Unit U T)
  /-- `provider.drop` admits exactly `dropF`. -/
  drop_fn : Fn provider.drop dropF
  /-- Computed storage retirement. -/
  retireF : S → List E → Option (Outcome S Unit U T)
  /-- `provider.retire` admits exactly `retireF`. -/
  retire_fn : Fn provider.retire retireF
  /-- The terminal reason chosen by the double-unwind policy. -/
  dbl : S → U → U → T
  /-- `provider.double` is the graph of `dbl`. -/
  double_fn : ∀ s o l t, provider.double s o l t ↔ t = dbl s o l

/-- The work of the provider never asks for another internal chunk (`.again`). The
literal trace is then finite and has at most one outcome. -/
def NoAgain (provider : Owned.Array.Provider S E Res U T) : Prop :=
  ∀ before input after, ¬ provider.work before input (.returned .again after)

end Generic

/-! ## The bundle -/

/-- A computed function and its proof for each primitive field of `types`.
Every component proves its lemmas over an arbitrary `P : Prims types`. -/
structure Prims (types : Types) where
  /-- Instruction byte vectors. -/
  bytes : VecPrims types.bytes
  /-- Instruction metadata vectors. -/
  metas : VecPrims types.metas
  /-- AccountInfo vectors. -/
  infos : VecPrims types.infos
  /-- Vectors of collected data Refs. -/
  guards : VecPrims types.guards
  /-- The discriminator vectors of the TLV validator. -/
  discriminators : VecPrims types.discriminators
  /-- The 3.0.0 zero-padding vector. -/
  paddingBytes : VecPrims types.paddingBytes
  /-- Literal seed byte vectors (`types.seedOps.bytes`). -/
  seedBytes : VecPrims types.seedOps.bytes
  /-- Unpacked seed vectors (`types.seedOps.seeds`). -/
  seeds : VecPrims types.seedOps.seeds
  /-- Borrowed seed-view vectors (`types.seedOps.refs`). -/
  seedRefs : VecPrims types.seedOps.refs
  /-- Computed literal construction work. -/
  literalWorkF : World types.Extra → Nat × List AccountInfo.Value →
    Option (Outcome (World types.Extra) Owned.Array.Command types.Unwind types.Terminal)
  /-- `types.infoLiteral.work` admits exactly `literalWorkF`. -/
  literalWork_fn : Fn types.infoLiteral.work literalWorkF
  /-- Computed literal completion. -/
  literalFinishF : World types.Extra → List AccountInfo.Value →
    Option (Outcome (World types.Extra) types.InfoResource types.Unwind types.Terminal)
  /-- `types.infoLiteral.finish` admits exactly `literalFinishF`. -/
  literalFinish_fn : Fn types.infoLiteral.finish literalFinishF
  /-- Computed literal storage retirement. -/
  literalRetireF : World types.Extra → List AccountInfo.Value →
    Option (Outcome (World types.Extra) Unit types.Unwind types.Terminal)
  /-- `types.infoLiteral.retire` admits exactly `literalRetireF`. -/
  literalRetire_fn : Fn types.infoLiteral.retire literalRetireF
  /-- The AccountInfo Rc clone and drop. -/
  rc : RcPrims types.rc
  /-- Computed PDA syscall. -/
  pdaSyscallF : World types.Extra → Address.Syscall.PdaRequest →
    Option (Outcome (World types.Extra) Address.Syscall.PdaReply types.Unwind types.Terminal)
  /-- `types.pdaSyscall` admits exactly `pdaSyscallF`. -/
  pdaSyscall_fn : Fn types.pdaSyscall pdaSyscallF
  /-- Computed panic dependency. -/
  raiseF : World types.Extra → Onchain.Panic →
    Option (Outcome (World types.Extra) Empty types.Unwind types.Terminal)
  /-- `types.raise` admits exactly `raiseF`. -/
  raise_fn : Fn types.raise raiseF
  /-- The terminal reason chosen by the double-unwind policy. -/
  dbl : World types.Extra → types.Unwind → types.Unwind → types.Terminal
  /-- `types.doubleUnwind` is the graph of `dbl`. -/
  double_fn : ∀ s o l t, types.doubleUnwind s o l t ↔ t = dbl s o l
  /-- Computed metadata write: the state after the write, if any. -/
  writeMetaF : World types.Extra → types.MetaResource → Nat → Solanalib.Runtime.CpiMeta →
    Option (World types.Extra)
  /-- `types.writeMeta` is the graph of `writeMetaF`. -/
  writeMeta_fn : ∀ before resource index item after,
    types.writeMeta before resource index item after ↔
      writeMetaF before resource index item = some after

/-- Computed forms of the two explicit dependencies. Collection is
higher-order: its computed form takes the computed callback, and `collect_fn`
holds for every callback computed by a function. -/
structure DepPrims (types : Types) (deps : Dependencies types) where
  /-- Computed collection, given the iterator and the computed callback. -/
  collectF : AllocatedCollect.Iterator types.Extra →
    (World types.Extra → AccountInfo.Value →
      Option (Outcome (World types.Extra) (Except Token.Error AllocatedCollect.Element)
        types.Unwind types.Terminal)) →
    RunF types types.GuardResource
  /-- `deps.collect.run iterator callback` admits exactly
  `collectF iterator callbackF` when `callback` admits exactly `callbackF`. -/
  collect_fn : ∀ iterator callback callbackF, Fn callback callbackF →
    RFn (deps.collect.run iterator callback) (collectF iterator callbackF)
  /-- Computed CPI invocation. -/
  invokeF : World types.Extra → CpiRequest.Request AccountInfo.Value →
    Option (Outcome (World types.Extra) (Except Token.Error Unit) types.Unwind types.Terminal)
  /-- `deps.invoke` admits exactly `invokeF`. -/
  invoke_fn : Fn deps.invoke invokeF

/-! ## The PDA search `Types.findPda` -/

section Pda

open Address.Syscall

variable {S U T : Type}

/-- The 64-bit slice profile of the source is decidable. -/
instance (inputs : PdaInputs) : Decidable inputs.Bounded :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `decodePda` as a function: the decoded result is unique, and a successful
status with an uninitialized address output has none. -/
def decodePdaF (reply : PdaReply) : Option (Option (Address.Value × UInt8)) :=
  if reply.status = 0 then reply.addressOutput.map fun address => some (address, reply.bumpOutput)
  else some none

/-- `decodePda reply` is the graph of `decodePdaF reply`. -/
theorem decodePda_fn (reply : PdaReply) (result : Option (Address.Value × UInt8)) :
    decodePda reply result ↔ decodePdaF reply = some result := by
  unfold decodePda decodePdaF
  by_cases zero : reply.status = 0
  · simp only [zero, ↓reduceIte]
    cases reply.addressOutput with
    | none => simp
    | some address => simp [eq_comm]
  · simp only [zero, ↓reduceIte, Option.some.injEq]
    exact eq_comm

/-- `tryRun`, computed. -/
def tryRunF (syscallF : S → PdaRequest → Option (Outcome S PdaReply U T)) :
    S → PdaInputs → Option (Outcome S (Option (Address.Value × UInt8)) U T) :=
  fun s inputs => (syscallF s (pdaRequest inputs)).bind (thenOpt · fun reply after =>
    (decodePdaF reply).map fun result => .returned result after)

/-- `tryRun syscall` admits exactly `tryRunF syscallF`. -/
theorem tryRun_fn {syscall : Callback.Run S PdaRequest PdaReply U T}
    {syscallF : S → PdaRequest → Option (Outcome S PdaReply U T)} (h : Fn syscall syscallF) :
    Fn (tryRun syscall) (tryRunF syscallF) := by
  intro s inputs o
  refine bind_fn h (fun reply after o => ?_) s (pdaRequest inputs) o
  constructor
  · rintro ⟨result, hd, rfl⟩
    rw [(decodePda_fn reply result).1 hd]; rfl
  · intro e
    cases hd : decodePdaF reply with
    | none => rw [hd] at e; cases e
    | some result =>
      rw [hd] at e
      exact ⟨result, (decodePda_fn reply result).2 hd, (Option.some.inj e).symm⟩

/-- `finishFind`, computed from the computed form of the panic dependency. -/
def finishFindF (panicF : S → Address.SearchPanic → Option (Outcome S Empty U T))
    (result : Option (Address.Value × UInt8)) (after : S) :
    Option (Outcome S (Address.Value × UInt8) U T) :=
  match result with
  | some value => some (.returned value after)
  | none => (panicF after .noViableProgramAddress).map (Outcome.map Empty.elim)

/-- `finishFind panic result after` admits exactly `finishFindF panicF result after`. -/
theorem finishFind_fn {panic : Callback.Run S Address.SearchPanic Empty U T}
    {panicF : S → Address.SearchPanic → Option (Outcome S Empty U T)} (h : Fn panic panicF)
    (result : Option (Address.Value × UInt8)) (after : S) :
    OFn (finishFind panic result after) (finishFindF panicF result after) := by
  intro o
  cases result with
  | some value => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩
  | none =>
    refine (map_fn h _ after .noViableProgramAddress o).trans ?_
    show (panicF after .noViableProgramAddress).map _ = some o ↔
      (panicF after .noViableProgramAddress).map _ = some o
    cases panicF after .noViableProgramAddress with
    | none => exact Iff.rfl
    | some i => rw [Option.map_some, Option.map_some, outcome_map_empty _ Empty.elim i]

/-- `Types.findPda`, computed: no outcome outside the slice profile. -/
def findPdaF {types : Types} (P : Prims types) :
    World types.Extra → PdaInputs →
      Option (Outcome (World types.Extra) (Solanalib.Runtime.Pubkey × UInt8) types.Unwind
        types.Terminal) :=
  fun s inputs =>
    if inputs.Bounded then
      (tryRunF P.pdaSyscallF s inputs).bind
        (thenOpt · (finishFindF fun st _ => P.raiseF st .noViableProgramAddress))
    else none

/-- `types.findPda` admits exactly `findPdaF P`. -/
theorem findPda_fn {types : Types} (P : Prims types) : Fn types.findPda (findPdaF P) := by
  intro s inputs o
  unfold Types.findPda findPdaF
  by_cases bounded : inputs.Bounded
  · simp only [bounded, true_and, ↓reduceIte]
    exact bind_fn (tryRun_fn P.pdaSyscall_fn)
      (finishFind_fn fun st _ o => P.raise_fn st .noViableProgramAddress o) s inputs o
  · simp only [bounded, false_and, ↓reduceIte, false_iff]
    exact fun h => by cases h

end Pda

section Helpers

variable {S : Type}

/-- An existential over the value of a computed option, followed by a
condition, is the bind of that option. -/
theorem exists_bind_iff {α β : Type} {P : α → Prop} {o : Option α}
    (hP : ∀ x, P x ↔ o = some x) {Q : α → Prop} {g : α → Option β} {r : β}
    (hQ : ∀ x, P x → (Q x ↔ g x = some r)) :
    (∃ x, P x ∧ Q x) ↔ o.bind g = some r := by
  cases ho : o with
  | none =>
    simp only [Option.bind_none, reduceCtorEq, iff_false, not_exists, not_and]
    intro x hx
    have hx' := (hP x).1 hx
    rw [ho] at hx'
    cases hx'
  | some a =>
    rw [Option.bind_some]
    have ha : P a := (hP a).2 ho
    constructor
    · rintro ⟨x, hx, hq⟩
      have hxa : x = a := Option.some.inj (((hP x).1 hx).symm.trans ho)
      subst hxa
      exact (hQ x hx).1 hq
    · exact fun h => ⟨a, ha, (hQ a ha).2 h⟩

/-- `exists_bind_iff` where the condition of the continuation does not depend on the condition of
the first value. -/
theorem exists_bind_iff' {X Y : Type} {P : X → Prop} {x : Option X}
    (hx : ∀ v, P v ↔ x = some v) {M : X → Prop} {g : X → Option Y} {y : Y}
    (hg : ∀ v, M v ↔ g v = some y) : (∃ v, P v ∧ M v) ↔ x.bind g = some y :=
  exists_bind_iff hx fun v _ => hg v

/-- `AllocatedTlv.sliceAt`, computed: the current observation if it is
present with the fixed length. -/
def AllocatedTlv.sliceAtF (observe : S → Option Bytes) (byteLength : Nat) (state : S) :
    Option Bytes :=
  (observe state).bind fun bytes => if bytes.length = byteLength then some bytes else none

/-- `AllocatedTlv.sliceAt observe byteLength state` is the graph of
`AllocatedTlv.sliceAtF observe byteLength state`. -/
theorem AllocatedTlv.sliceAt_fn (observe : S → Option Bytes) (byteLength : Nat) (state : S)
    (bytes : Bytes) :
    AllocatedTlv.sliceAt observe byteLength state bytes ↔
      AllocatedTlv.sliceAtF observe byteLength state = some bytes := by
  unfold AllocatedTlv.sliceAt AllocatedTlv.sliceAtF
  cases observe state with
  | none => simp
  | some current =>
    by_cases hl : current.length = byteLength
    · simp only [hl, Option.bind_some, ↓reduceIte, Option.some.injEq]
      exact ⟨And.left, fun h => ⟨h, h ▸ hl⟩⟩
    · simp only [Option.bind_some, hl, ↓reduceIte, reduceCtorEq, iff_false, not_and,
        Option.some.injEq]
      exact fun h => by subst h; exact hl

end Helpers

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
