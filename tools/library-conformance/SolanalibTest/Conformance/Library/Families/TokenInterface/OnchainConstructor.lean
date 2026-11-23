/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
import Solanalib.Specs.Core.TokenInstructionAllocated
import Solanalib.Specs.Core.TokenRequestAllocatedTypes

/-!
# The allocated instruction constructor, computed over a primitive bundle

`InstructionAllocated.run types state plan` is the operational relation of the
allocated instruction constructors. Its only relational dependencies are the
byte and metadata vectors and the double-unwind policy of `types`. Given a
`ConstructorPrims types`, which bundles a computed form of each with its proof,
the relation admits exactly the outcome computed by `runF`; `run_fn` proves
this. `Allocated.runF`/`Allocated.run_fn` are this development at the
registered sample index (`Allocated.samplePrims`).

The onchain model builds its instruction with
`InstructionAllocated.run types.constructor`. `Types.constructor` reuses the
onchain `bytes`, `metas` and `doubleUnwind`, so `constructorPrims P` builds the
bundle from any `P : OnchainPrims.Prims types`, and `runR`/`runR_fn` give the
computed Result-aware run of the first step of the model in `base`.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainConstructor

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open Solanalib.Specs.Core.Token.InstructionAllocated (DataStep MetaPlan Plan)

/-! ## The primitive bundle -/

/-- Computed forms of the relational dependencies of `InstructionAllocated.run`:
the two vector dependencies and the double-unwind policy. -/
structure ConstructorPrims (types : InstructionAllocated.Types) where
  /-- Instruction byte vectors. -/
  bytes : VecPrims types.bytes
  /-- Instruction metadata vectors. -/
  metas : VecPrims types.metas
  /-- The terminal reason chosen by the double-unwind policy. -/
  dbl : types.State → types.Unwind → types.Unwind → types.Terminal
  /-- `types.doubleUnwind` is the graph of `dbl`. -/
  double_fn : ∀ s o l t, types.doubleUnwind s o l t ↔ t = dbl s o l

variable {types : InstructionAllocated.Types} (C : ConstructorPrims types)

/-- A computed outcome of the dependencies of the constructor at `types`. -/
abbrev Out (types : InstructionAllocated.Types) (V : Type) :=
  Outcome types.State V types.Unwind types.Terminal

/-! ## Composite steps -/

/-- One packed-data write, computed. -/
def stepF (resource : types.ByteResource) : DataStep → types.State → Option (Out types Unit)
  | .push byte, s => C.bytes.pushF s (resource, byte)
  | .extend bytes, s => C.bytes.extendF s (resource, bytes)

/-- `InstructionAllocated.writeData`, computed: the writes in order. -/
def writeDataF (resource : types.ByteResource) : List DataStep → types.State → Option (Out types
  Unit)
  | [], s => some (.returned () s)
  | step :: rest, s =>
    (stepF C resource step s).bind (thenOpt · fun _ st => writeDataF resource rest st)

/-- `InstructionAllocated.writeData types resource steps` admits exactly
`writeDataF C resource steps`. -/
theorem writeData_fn (resource : types.ByteResource) :
    ∀ steps, Fn (InstructionAllocated.writeData types resource steps)
      (fun s _ => writeDataF C resource steps s)
  | [] => fun _ _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
  | step :: rest => by
    have hstep : Fn (match step with
        | .push byte => fun state (_ : Unit) => types.bytes.push state (resource, byte)
        | .extend bytes => fun state (_ : Unit) => types.bytes.extend state (resource, bytes))
        (fun s _ => stepF C resource step s) := by
      cases step with
      | push byte => exact fun s _ o => C.bytes.push_fn s (resource, byte) o
      | extend bytes => exact fun s _ o => C.bytes.extend_fn s (resource, bytes) o
    exact bind_fn hstep (fun _ st o => writeData_fn resource rest st () o)

/-- `InstructionAllocated.pushMetas`, computed: the pushes in order. -/
def pushMetasF (resource : types.MetaResource) :
    List Solanalib.Runtime.CpiMeta → types.State → Option (Out types Unit)
  | [], s => some (.returned () s)
  | item :: rest, s =>
    (C.metas.pushF s (resource, item)).bind (thenOpt · fun _ st => pushMetasF resource rest st)

/-- `InstructionAllocated.pushMetas types resource items` admits exactly
`pushMetasF C resource items`. -/
theorem pushMetas_fn (resource : types.MetaResource) :
    ∀ items, Fn (InstructionAllocated.pushMetas types resource items)
      (fun s _ => pushMetasF C resource items s)
  | [] => fun _ _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
  | item :: rest =>
    bind_fn (fun s _ o => C.metas.push_fn s (resource, item) o)
      (fun _ st o => pushMetas_fn resource rest st () o)

/-- The single drop action of the metadata owner admits exactly its computed form. -/
theorem metasDrops_fn (resource : types.MetaResource) :
    All2 DFn [fun current => types.metas.drop current resource]
      [fun current => C.metas.dropF current resource] :=
  .cons (fun s o => C.metas.drop_fn s resource o) .nil

/-- The single drop action of the byte owner admits exactly its computed form. -/
theorem bytesDrops_fn (resource : types.ByteResource) :
    All2 DFn [fun current => types.bytes.drop current resource]
      [fun current => C.bytes.dropF current resource] :=
  .cons (fun s o => C.bytes.drop_fn s resource o) .nil

/-- The pushes onto an owned metadata vector, which is dropped on unwind. -/
def protectedMetasF (resource : types.MetaResource) (items : List Solanalib.Runtime.CpiMeta)
    (s : types.State) : Option (Out types types.MetaResource) :=
  ((pushMetasF C resource items s).map (Outcome.map fun _ => resource)).bind
    (onUnwindF C.dbl [fun current => C.metas.dropF current resource])

/-- `InstructionAllocated.buildMetas`, computed. -/
def buildMetasF : MetaPlan → types.State → Option (Out types types.MetaResource)
  | .fromList items, s => C.metas.fromListF s items
  | .withCapacity capacity items, s =>
    (C.metas.withCapacityF s capacity).bind
      (thenOpt · fun resource st => protectedMetasF C resource items st)
  | .fromListThenPush initial rest, s =>
    (C.metas.fromListF s initial).bind
      (thenOpt · fun resource st => protectedMetasF C resource rest st)

/-- The protected pushes admit exactly `protectedMetasF`. -/
theorem protectedMetas_fn (resource : types.MetaResource) (items : List Solanalib.Runtime.CpiMeta) :
    Fn (Owned.protect types.doubleUnwind [fun current => types.metas.drop current resource]
      (Callback.map (fun _ => resource) (InstructionAllocated.pushMetas types resource items)))
      (fun s _ => protectedMetasF C resource items s) :=
  protect_fn C.double_fn (metasDrops_fn C resource) (map_fn (pushMetas_fn C resource items) _)

/-- `InstructionAllocated.buildMetas types plan` admits exactly `buildMetasF C plan`. -/
theorem buildMetas_fn (plan : MetaPlan) :
    Fn (InstructionAllocated.buildMetas types plan) (fun s _ => buildMetasF C plan s) := by
  cases plan with
  | fromList items => exact fun s _ o => C.metas.fromList_fn s items o
  | withCapacity capacity items =>
    exact bind_fn (fun s _ o => C.metas.withCapacity_fn s capacity o)
      (fun resource st o => protectedMetas_fn C resource items st () o)
  | fromListThenPush initial rest =>
    exact bind_fn (fun s _ o => C.metas.fromList_fn s initial o)
      (fun resource st o => protectedMetas_fn C resource rest st () o)

/-- The writes into an owned byte vector, which is dropped on unwind. -/
def protectedDataF (resource : types.ByteResource) (steps : List DataStep) (s : types.State) :
    Option (Out types types.ByteResource) :=
  ((writeDataF C resource steps s).map (Outcome.map fun _ => resource)).bind
    (onUnwindF C.dbl [fun current => C.bytes.dropF current resource])

/-- `InstructionAllocated.buildData`, computed. -/
def buildDataF (steps : List DataStep) (s : types.State) : Option (Out types types.ByteResource) :=
  (C.bytes.withCapacityF s types.enumSize).bind
    (thenOpt · fun resource st => protectedDataF C resource steps st)

/-- `InstructionAllocated.buildData types steps` admits exactly `buildDataF C steps`. -/
theorem buildData_fn (steps : List DataStep) :
    Fn (InstructionAllocated.buildData types steps) (fun s _ => buildDataF C steps s) :=
  bind_fn (fun s _ o => C.bytes.withCapacity_fn s types.enumSize o)
    (fun resource st o =>
      protect_fn C.double_fn (bytesDrops_fn C resource)
        (map_fn (writeData_fn C resource steps) _) st () o)

/-! ## The constructor relation -/

/-- The result of the constructor: an owned instruction or a program error. -/
abbrev Result (types : InstructionAllocated.Types) :=
  Except Token.Error (InstructionAllocated.Value types)

/-- The data-first order after the byte vector is allocated: the writes, then
the metadata, with the byte owner dropped on unwind. -/
def dataFirstF (plan : Plan) (data : types.ByteResource) (s : types.State) :
    Option (Out types (Result types)) :=
  ((writeDataF C data plan.dataSteps s).bind (thenOpt · fun _ current =>
      (buildMetasF C plan.metas current).map
        (Outcome.map fun metas =>
          Except.ok ({ programId := plan.programId, metas, data } : InstructionAllocated.Value
            types)))).bind
    (onUnwindF C.dbl [fun current => C.bytes.dropF current data])

/-- The metadata-first order after the metadata is built: the packed data,
with the metadata owner dropped on unwind. -/
def metasFirstF (plan : Plan) (metas : types.MetaResource) (s : types.State) :
    Option (Out types (Result types)) :=
  ((buildDataF C plan.dataSteps s).map
      (Outcome.map fun data =>
        Except.ok ({ programId := plan.programId, metas, data } : InstructionAllocated.Value
          types))).bind
    (onUnwindF C.dbl [fun current => C.metas.dropF current metas])

/-- `InstructionAllocated.run`, computed: a program rejection allocates nothing;
otherwise the two vectors are built in the order of the plan. -/
def runF (state : types.State) (plan : Plan) : Option (Out types (Result types)) :=
  match Instruction.checkProgram plan.programs plan.programId with
  | .error error => some (.returned (.error error) state)
  | .ok () =>
    match plan.order with
    | .dataThenMetas =>
      (C.bytes.withCapacityF state types.enumSize).bind
        (thenOpt · fun data after => dataFirstF C plan data after)
    | .metasThenData =>
      (buildMetasF C plan.metas state).bind
        (thenOpt · fun metas after => metasFirstF C plan metas after)

/-- Over any bundle, the constructor relation admits exactly `runF`. -/
theorem run_fn : Fn (InstructionAllocated.run types) (runF C) := by
  intro state plan o
  unfold InstructionAllocated.run runF
  cases Instruction.checkProgram plan.programs plan.programId with
  | error error =>
    dsimp only
    exact ⟨fun h => by subst h; rfl, fun h => (Option.some.inj h).symm⟩
  | ok u =>
    cases u
    dsimp only
    cases plan.order with
    | dataThenMetas =>
      refine bind_fn (fun s _ o => C.bytes.withCapacity_fn s types.enumSize o)
        (fun data after o => ?_) state () o
      exact protect_fn C.double_fn (bytesDrops_fn C data)
        (bind_fn (writeData_fn C data plan.dataSteps)
          (fun _ current o => map_fn (buildMetas_fn C plan.metas) _ current () o)) after () o
    | metasThenData =>
      refine bind_fn (buildMetas_fn C plan.metas) (fun metas after o => ?_) state () o
      exact protect_fn C.double_fn (metasDrops_fn C metas)
        (map_fn (buildData_fn C plan.dataSteps) _) after () o

/-! ## The onchain instance

`Types.constructor` takes its vectors and its double-unwind policy from the
onchain `types` unchanged, so the onchain bundle also supplies the constructor bundle. -/

section Onchain

variable {types : OnchainAllocated.Types}

/-- The bundle of the constructor at `types.constructor`, from the onchain bundle. -/
def constructorPrims (P : OnchainPrims.Prims types) : ConstructorPrims types.constructor where
  bytes := P.bytes
  metas := P.metas
  dbl := P.dbl
  double_fn := P.double_fn

/-- The construction step of the model in `OnchainAllocated.base` at a fixed plan,
computed as an onchain run. -/
def runR (P : OnchainPrims.Prims types) (plan : Plan) :
    RunF types (InstructionAllocated.Value types.constructor) :=
  fun s => runF (constructorPrims P) s plan

/-- `fun state => InstructionAllocated.run types.constructor state plan`, the
first step of `OnchainAllocated.base`, admits exactly `runR P plan`. -/
theorem runR_fn (P : OnchainPrims.Prims types) (plan : Plan) :
    RFn (fun state => InstructionAllocated.run types.constructor state plan) (runR P plan) :=
  call_fn (run_fn (constructorPrims P)) plan

end Onchain

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainConstructor
