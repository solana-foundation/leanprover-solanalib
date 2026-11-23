/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessFrames
public import Solanalib.Specs.Core.TokenRequestAllocatedAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

open AllocatedGuard Admission

/-- The partial vector operations of the sample preserve typed input cells on all
finite exits, including calls made before the first data borrow. -/
theorem emptyOnly_inputs {Element : Type}
    (part : Owned.Focus State (Owned.VectorState Unit))
    (outside : ∀ before inner, (part.set before inner).1 = before.1) :
    VectorInputs 64 (emptyOnlyOps (Element := Element) part) := by
  have units := VectorInputs.focus 64
    (Owned.vectorReference (Element := Unit) (Unwind := Nat) (Terminal := Nat)) part outside
  refine ⟨units.empty, units.capacity, ?_, InputPreserves.empty _, ?_, units.drop⟩
  · intro before values valid outcome called
    exact units.capacity before 0 valid outcome called.2
  · apply InputPreserves.of_accounts
    rintro before ⟨resource, values⟩ outcome ⟨_, _, same⟩
    cases same
    rfl

/-- Actual Rc counter/event mutations do not change source input cell types. -/
theorem rc_inputs : InputPreserves 64 rcOps.cloneRc ∧ InputPreserves 64 rcOps.dropRc := by
  constructor <;> apply InputPreserves.of_accounts
  all_goals
    rintro before ⟨field, cell⟩ outcome ⟨_, same⟩
    cases same
    rfl

/-- The two actual field operations of the sample clone preserve input typing. -/
theorem rcClone_inputs : InputPreserves 64 (AccountInfoRc.cloneCall rcOps) := by
  intro before info valid outcome called
  exact ((rc_inputs.1.arguments (fun (_ : Unit) => (.lamports, info.lamports))).bind
    (fun _ => (rc_inputs.1.arguments (fun (_ : Unit) => (.data, info.data))).map
      (fun _ => AccountInfo.clone info))) before () valid outcome called

/-- The two actual field operations of the sample destructor preserve input typing. -/
theorem rcDrop_inputs : InputPreserves 64 (AccountInfoRc.dropCall rcOps) := by
  intro before info valid outcome called
  exact ((rc_inputs.2.arguments (fun (_ : Unit) => (.lamports, info.lamports))).bind
    (fun _ => rc_inputs.2.arguments (fun (_ : Unit) => (.data, info.data))))
    before () valid outcome called

/-- Sequential current-element cloning retains the type of the next source borrow. -/
theorem cloneInfos_inputs (values : List AccountInfo.Value) :
    InputPreserves 64 (cloneInfos values) := by
  induction values with
  | nil =>
    apply InputPreserves.of_accounts
    intro _ _ _ same
    cases same
    rfl
  | cons value rest induction =>
    exact (rcClone_inputs.rcLift.arguments (fun (_ : Unit) => value)).bind (fun _ => induction)

/-- Sequential current-element destruction retains the borrowed input payloads. -/
theorem dropInfos_inputs (values : List AccountInfo.Value) :
    InputPreserves 64 (dropInfos values) := by
  induction values with
  | nil =>
    apply InputPreserves.of_accounts
    intro _ _ _ same
    cases same
    rfl
  | cons value rest induction =>
    exact (rcDrop_inputs.rcLift.arguments (fun (_ : Unit) => value)).bind (fun _ => induction)

/-- Actual vector/Rc composition keeps input representation on every finite exit. -/
theorem infos_inputs : VectorInputs 64 infosOps := by
  have storage := VectorInputs.focus 64
    (Owned.vectorReference (Element := AccountInfo.Value) (Unwind := Nat) (Terminal := Nat))
    infosFocus (fun _ _ => rfl)
  refine ⟨storage.empty, storage.capacity, storage.fromList, storage.push, ?_, ?_⟩
  · intro before input valid outcome called
    exact ((cloneInfos_inputs input.2).bind
      (fun _ => storage.extend.arguments (fun (_ : Unit) => input))) before () valid outcome called
  · intro before resource valid outcome called
    obtain ⟨values, _, run⟩ := called
    exact ((dropInfos_inputs values).bind
      (fun _ => storage.drop.arguments (fun (_ : Unit) => resource))) before () valid outcome run


/-- A provider that changes only auxiliary storage supplies both independent
continuation frames, without a length/scalar-bound assumption. -/
private theorem accounts_only {ExtraState Args Value Unwind Terminal : Type}
    {call : Callback.Run (World ExtraState) Args Value Unwind Terminal}
    (same : ∀ before args outcome, call before args outcome →
      match outcome with
      | .returned _ after | .unwound _ after => after.1 = before.1
      | .terminated _ => True) : Preserves call ∧ DataPreserves call :=
  ⟨Preserves.of_accounts same, DataPreserves.of_input (InputPreserves.of_accounts 0 same)⟩

/-- All and only the selected primitive catalogue is checked for the concrete
sample. These proofs precede, rather than assume, a complete Token execution. -/
theorem sample_primitives {Args Value Unwind : Type}
    {call : Callback.Run (World sampleTypes.Extra) Args Value Unwind sampleTypes.Terminal}
    (selected : Primitive sampleTypes call) : Preserves call ∧ DataPreserves call := by
  have bytesF := VectorFrames.focus
    (Owned.vectorReference (Element := UInt8) (Unwind := Nat) (Terminal := Nat))
    bytesFocus (fun _ _ => rfl)
  have bytesI := VectorInputs.focus 64
    (Owned.vectorReference (Element := UInt8) (Unwind := Nat) (Terminal := Nat))
    bytesFocus (fun _ _ => rfl)
  have metasF := VectorFrames.focus
    (Owned.vectorReference (Element := Solanalib.Runtime.CpiMeta) (Unwind := Nat) (Terminal := Nat))
    metasFocus (fun _ _ => rfl)
  have metasI := VectorInputs.focus 64
    (Owned.vectorReference (Element := Solanalib.Runtime.CpiMeta) (Unwind := Nat) (Terminal := Nat))
    metasFocus (fun _ _ => rfl)
  have discriminatorsF := VectorFrames.focus
    (Owned.vectorReference (Element := Bytes) (Unwind := Nat) (Terminal := Nat))
    discriminatorsFocus (fun _ _ => rfl)
  have discriminatorsI := VectorInputs.focus 64
    (Owned.vectorReference (Element := Bytes) (Unwind := Nat) (Terminal := Nat))
    discriminatorsFocus (fun _ _ => rfl)
  have seedsF := emptyOnly_frames (Element := AllocatedSeeds.Seed Nat) seedsFocus (fun _ _ => rfl)
  have seedsI := emptyOnly_inputs (Element := AllocatedSeeds.Seed Nat) seedsFocus (fun _ _ => rfl)
  have refsF := emptyOnly_frames (Element := AllocatedSeeds.BytesView State) seedRefsFocus (fun _ _
    => rfl)
  have refsI := emptyOnly_inputs (Element := AllocatedSeeds.BytesView State) seedRefsFocus (fun _ _
    => rfl)
  cases selected with
  | bytesEmpty =>
    apply accounts_only
    intro _ _ _ called
    cases called
    rfl
  | bytesCapacity => exact ⟨bytesF.capacity, DataPreserves.of_input bytesI.capacity⟩
  | bytesPush => exact ⟨bytesF.push, DataPreserves.of_input bytesI.push⟩
  | bytesExtend => exact ⟨bytesF.extend, DataPreserves.of_input bytesI.extend⟩
  | bytesDrop => exact ⟨bytesF.drop, DataPreserves.of_input bytesI.drop⟩
  | metasCapacity => exact ⟨metasF.capacity, DataPreserves.of_input metasI.capacity⟩
  | metasList => exact ⟨metasF.fromList, DataPreserves.of_input metasI.fromList⟩
  | metasPush => exact ⟨metasF.push, DataPreserves.of_input metasI.push⟩
  | metasExtend => exact ⟨metasF.extend, DataPreserves.of_input metasI.extend⟩
  | metasDrop => exact ⟨metasF.drop, DataPreserves.of_input metasI.drop⟩
  | infosPush => exact ⟨infos_frames.push, DataPreserves.of_input infos_inputs.push⟩
  | infosExtend => exact ⟨infos_frames.extend, DataPreserves.of_input infos_inputs.extend⟩
  | infosDrop => exact ⟨infos_frames.drop, DataPreserves.of_input infos_inputs.drop⟩
  | discriminatorsEmpty =>
    apply accounts_only
    intro _ _ _ called
    cases called
    rfl
  | discriminatorsPush => exact ⟨discriminatorsF.push, DataPreserves.of_input discriminatorsI.push⟩
  | discriminatorsDrop => exact ⟨discriminatorsF.drop, DataPreserves.of_input discriminatorsI.drop⟩
  | paddingList => exact ⟨bytesF.fromList, DataPreserves.of_input bytesI.fromList⟩
  | paddingDrop => exact ⟨bytesF.drop, DataPreserves.of_input bytesI.drop⟩
  | literalBytes => exact ⟨bytesF.fromList, DataPreserves.of_input bytesI.fromList⟩
  | seedsEmpty =>
    apply accounts_only
    intro _ _ _ called
    cases called
    rfl
  | seedsPush => exact ⟨seedsF.push, DataPreserves.of_input seedsI.push⟩
  | seedsDrop => exact ⟨seedsF.drop, DataPreserves.of_input seedsI.drop⟩
  | refsEmpty =>
    apply accounts_only
    intro _ _ _ called
    cases called
    rfl
  | refsPush => exact ⟨refsF.push, DataPreserves.of_input refsI.push⟩
  | refsDrop => exact ⟨refsF.drop, DataPreserves.of_input refsI.drop⟩
  | literalWork =>
    apply accounts_only
    intro before input outcome called
    change (if input.2.length < input.1 then _ else _) at called
    split at called
    · cases called; rfl
    · cases called.2; rfl
  | literalFinish => exact ⟨infos_frames.fromList, DataPreserves.of_input infos_inputs.fromList⟩
  | literalRetire =>
    apply accounts_only
    intro _ _ _ called
    cases called
    rfl
  | rcClone => exact ⟨rc_frames.1, DataPreserves.of_input rc_inputs.1⟩
  | rcDrop => exact ⟨rc_frames.2, DataPreserves.of_input rc_inputs.2⟩
  | pda => exact ⟨Preserves.empty, DataPreserves.of_input (InputPreserves.empty 0)⟩
  | raise =>
    apply accounts_only
    intro _ _ _ called
    cases called
    rfl
  | writeMeta =>
    apply accounts_only
    rintro before input outcome ⟨after, ⟨values, _, same⟩, rfl⟩
    cases same
    rfl

/-- Resolver callbacks retain the distinct Ref-vector ledger of the sample on
ordinary returns and unwinds; an unavailable primitive creates no exit. -/
theorem sample_resolver {Args Value : Type}
    {call : Callback.Run (World sampleTypes.Extra) Args Value sampleTypes.Unwind
      sampleTypes.Terminal}
    (selected : ResolverPrimitive sampleTypes call) : Retains sampleTypes.guards.current call := by
  cases selected with
  | literalBytes =>
    exact Retains.focus sampleTypes.guards.current bytesFocus (fun _ _ _ => rfl)
      Owned.vectorReference.fromList
  | seedsEmpty | refsEmpty =>
    intro before args resource value current outcome called
    cases called
    exact current
  | seedsPush | refsPush | pda => exact Retains.empty _
  | seedsDrop =>
    exact Retains.focus sampleTypes.guards.current seedsFocus (fun _ _ _ => rfl)
      Owned.vectorReference.drop
  | refsDrop =>
    exact Retains.focus sampleTypes.guards.current seedRefsFocus (fun _ _ _ => rfl)
      Owned.vectorReference.drop
  | raise =>
    intro before args resource value current outcome called
    cases called
    exact current

/-- The sample admits its actual primitives and the deliberately unused
collector without postulating a populated collection or a whole SDK result. -/
theorem sample_admitted (deps : Dependencies sampleTypes)
    (unused : ∀ iterator callback before outcome, deps.collect.run iterator callback before outcome
      → False) :
    Admitted sampleTypes deps sampleGuardProtocol := by
  refine {
    primitive := sample_primitives
    guardDrop := ?_
    guardDropData := ?_
    resolver := sample_resolver
    conforms := ?_
    collected := ?_
    collection := ?_
    pdaReady := ?_
    literalReady := ?_ }
  · intro before resource valid guard slot live _ outcome called
    exact (emptyOnly_frames (Element := GuardElement) guardsFocus (fun _ _ => rfl)).drop
      before resource valid guard slot live (by simp) outcome called
  · exact DataPreserves.of_input
      (emptyOnly_inputs (Element := GuardElement) guardsFocus (fun _ _ => rfl)).drop
  · intro iterator callback before outcome called
    exact False.elim (unused iterator callback before outcome called)
  · constructor
    intro _ _ _ _ impossible
    exact False.elim impossible
  · refine ⟨⟨fun _ _ => Preserves.empty, Preserves.empty, ?_⟩,
      fun _ _ => DataPreserves.of_input (InputPreserves.empty 0),
      DataPreserves.of_input (InputPreserves.empty 0), fun _ _ _ _ => rfl,
      fun _ _ => Retains.empty _, ?_⟩
    · intro acquired
      apply Preserves.of_accounts
      intro _ _ _ called
      cases called
      rfl
    · intro resource length entry
      exact AllocatedCollect.CleanupReady.of_order (fun _ _ => List.Perm.refl _)
  · intro _ _ _ _ _ impossible
    exact False.elim impossible
  · apply LiteralAdmission.Ready.of_conforms
    constructor
    · intro before count values after bounded called
      change (if values.length < count then _ else _) at called
      split at called
      · assumption
      · cases called.2
    · intro before count values after bounded called
      change (if values.length < count then _ else _) at called
      split at called
      · cases called
      · exact called.1
    · intro _ _
      exact List.Perm.refl _

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
