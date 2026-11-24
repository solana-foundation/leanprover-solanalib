/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.ErrorResources

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- Only the literal count used by this source call is constrained. Work may
have arbitrarily many finite steps or no finite exit; cleanup visits each
evaluated occurrence once, including equal or aliased elements. -/
structure LiteralControl (resources : Resources) (count : Nat) : Prop where
  evaluate : ∀ before values after, values.length ≤ count →
    resources.literalProvider.work before (count, values) (.returned .evaluate after) →
      values.length < count
  finish : ∀ before values after, values.length ≤ count →
    resources.literalProvider.work before (count, values) (.returned .finish after) →
      values.length = count
  cleanup : ∀ before values, values.length ≤ count →
    (resources.literalProvider.cleanupOrder before values).Perm (List.finRange values.length)

theorem LiteralControl.of_conforms {resources : Resources}
    (law : resources.literalProvider.Conforms) (count : Nat) : LiteralControl resources count :=
  ⟨fun before values after => law.evaluate_bound before count values after,
    fun before values after => law.finish_count before count values after,
    fun before values _ => law.cleanup_permutation before values⟩

/-- Array arguments are moved values; vector arguments are read at the call
site. The expected sequence is ghost information, never used as a fallback. -/
inductive AccountArgument (resources : Resources) where
  | array (values : List AccountInfo.Value)
  | vector (resource : resources.InfoResource) (expected : List AccountInfo.Value)

def AccountArgument.expected {resources : Resources} : AccountArgument resources → List
  AccountInfo.Value
  | .array values | .vector _ values => values

def AccountArgument.read {resources : Resources} (state : resources.State) :
    AccountArgument resources → Option (List AccountInfo.Value)
  | .array values => some values
  | .vector resource _ => resources.infos.current state resource

structure CallPoint (resources : Resources) where
  instruction : Built resources
  accounts : AccountArgument resources

/-- Exact successful prefixes reaching the next local request read. No
completed invocation or cleanup is used to decide admission. -/
inductive AtCall (resources : Resources) :
    (operation : Operation) → resources.State → Args resources operation →
      CallPoint resources → resources.State → Prop
  | associated (profile : Profile) (kind : CreateKind)
      (before after : resources.State) (args : Args resources (.associated profile kind))
      (instruction : Built resources)
      (built : build resources (.associated profile kind) before args (.returned instruction
        after)) :
      AtCall resources (.associated profile kind) before args
        ⟨instruction, .array args.context.accounts.owners⟩ after
  | deactivate (before after : resources.State) (args : Args resources .deactivate)
      (instruction : Built resources)
      (built : build resources .deactivate before args (.returned instruction after)) :
      AtCall resources .deactivate before args ⟨instruction, .array args.context.accounts.moved⟩
        after
  | memo (before after : resources.State) (args : Args resources .memo)
      (instruction : Built resources) (remaining : List AccountInfo.Value)
      (initial : resources.infos.current before args.context.remainingAccounts = some remaining)
      (built : build resources .memo before args (.returned instruction after)) :
      AtCall resources .memo before args
        ⟨instruction, .vector args.context.remainingAccounts remaining⟩ after
  | metadata (before builtState after : resources.State) (args : Args resources .metadata)
      (instruction : Built resources) (infos : resources.InfoResource) (remaining : List
        AccountInfo.Value)
      (initial : resources.infos.current before args.context.remainingAccounts = some remaining)
      (built : build resources .metadata before args (.returned instruction builtState))
      (prepared : metadataInfos resources args.context builtState () (.returned infos after)) :
      AtCall resources .metadata before args
        ⟨instruction, .vector infos (List.append
          (List.append args.context.accounts.owners remaining) [args.context.program])⟩ after
  | withdrawNone (before builtState after : resources.State) (args : Args resources .withdraw)
      (instruction : Built resources) (infos : resources.InfoResource)
      (absent : args.extra.custodian = none)
      (built : build resources .withdraw before args (.returned instruction builtState))
      (literal : withdrawLiteral resources args.context.accounts builtState (.returned infos
        after)) :
      AtCall resources .withdraw before args ⟨instruction, .vector infos
        args.context.accounts.moved⟩ after
  | withdrawSome (before builtState preparedState after : resources.State)
      (args : Args resources .withdraw) (instruction : Built resources) (infos :
        resources.InfoResource)
      (custodian : AccountInfo.Value) (present : args.extra.custodian = some custodian)
      (built : build resources .withdraw before args (.returned instruction builtState))
      (literal : withdrawLiteral resources args.context.accounts builtState (.returned infos
        preparedState))
      (pushed : resources.infos.push preparedState (infos, custodian) (.returned () after)) :
      AtCall resources .withdraw before args
        ⟨instruction, .vector infos (args.context.accounts.moved ++ [custodian])⟩ after

/-- Current instruction contents agree with the actual planned
value of this constructor, and current vector accounts agree with the source-ordered sequence.
These obligations include retention through all earlier local callbacks. -/
def CallPoint.Ready {resources : Resources} (point : CallPoint resources) (state : resources.State)
  : Prop :=
  observe resources state point.instruction = some point.instruction.planned ∧
    point.accounts.read state = some point.accounts.expected

def SerializationUsed {resources : Resources} (operation : Operation)
    (args : Args resources operation) (input : Serialization) : Prop :=
  match operation, input with
  | .deactivate, .stakeDeactivate => True
  | .withdraw, .stakeWithdraw amount => amount = args.extra.amount
  | .metadata, .metadataDiscriminator => True
  | .metadata, .metadataArguments _ mutable details =>
      mutable = args.extra.isMutable ∧ details = args.extra.details
  | _, _ => False

/-- A finite serializer return has the selected codec result. On Ok it owns
the exact encoded bytes; checked Borsh length failure remains an Err. -/
def SerializationResult (resources : Resources) (input : Serialization)
    (result : Except SerializationError resources.ByteResource) (after : resources.State) : Prop :=
  match input.encode, result with
  | .ok expected, .ok resource => resources.bytes.current after resource = some expected
  | .error expected, .error actual => actual = expected
  | _, _ => False

def NoUnwind {State Args Value Unwind Terminal : Type}
    (call : Callback.Run State Args Value Unwind Terminal) : Prop :=
  ∀ before args reason after, ¬ call before args (.unwound reason after)

/-- Source-used local read domains, constructor control, codec results, and
non-unwinding POD/AccountInfo vector destruction. Every field is conditional on
the wrapper that actually reaches it. No provider termination is assumed. -/
structure Ready (types : Types) (operation : Operation) (before : types.resources.State)
    (args : Args types.resources operation) : Prop where
  memo : match operation with
    | .memo => ∃ remaining,
        types.resources.infos.current before args.context.remainingAccounts = some remaining ∧
        ∀ keys after, types.resources.keys.fromList before (remaining.map AccountInfo.Value.key)
          (.returned keys after) →
          types.resources.keys.current after keys = some (remaining.map AccountInfo.Value.key)
    | _ => True
  metadataData : match operation with
    | .metadata => ∃ data, args.extra.data.current before = some data ∧
        ∀ allocated after,
          metadataPrefix types.resources args.context.accounts.keys args.extra.updateAuthoritySigner
            before () (.returned allocated after) → args.extra.data.current after = some data
    | _ => True
  metadataRemaining : match operation with
    | .metadata => ∃ remaining,
        types.resources.infos.current before args.context.remainingAccounts = some remaining ∧
        ∀ instruction builtState infos after,
          build types.resources .metadata before args (.returned instruction builtState) →
          metadataFields types.resources args.context.accounts builtState () (.returned infos
            after) →
          types.resources.infos.current after args.context.remainingAccounts = some remaining
    | _ => True
  call : ∀ point after, AtCall types.resources operation before args point after → point.Ready after
  literal : match operation with
    | .metadata => LiteralControl types.resources 1
    | .withdraw => LiteralControl types.resources 5
    | _ => True
  pda : match operation with
    | .associated .modern _ => Address.Syscall.SuccessInitialized types.resources.pda before
        (associatedSeeds args.context.accounts.keys)
    | _ => True
  serialized : ∀ state input result after, SerializationUsed operation args input →
    types.resources.serialize state input (.returned result after) →
      SerializationResult types.resources input result after
  metaDrop : NoUnwind types.resources.metas.drop
  byteDrop : NoUnwind types.resources.bytes.drop
  infoDrop : NoUnwind types.resources.infos.drop
  keyDrop : match operation with
    | .memo => NoUnwind types.resources.keys.drop
    | _ => True
  errors : ErrorResources types.resources operation.profile
  invocationError : ∀ point atCall program after,
    AtCall types.resources operation before args point atCall →
    types.invoke atCall
      ⟨point.instruction.planned, point.accounts.expected, args.context.signerSeeds⟩
      (.returned (.error program) after) →
    ∃ strings, (types.resources.errors.programStrings program).mapM
      (types.resources.errors.currentString after) = some strings

def family (operation : Operation) : Family where
  Index := Types
  State := fun types => types.resources.State
  Args := fun types => Args types.resources operation
  Value := fun types => Except (Error types.resources operation.profile) Unit
  Unwind := fun types => types.resources.Unwind
  Terminal := fun types => types.resources.Terminal
  contract := fun types => { requires := Ready types operation, post := run types operation }

def reference (operation : Operation) : FamilyRun (family operation) := fun types => run types
  operation

theorem reference_holds (operation : Operation) : FamilyReference (family operation) (reference
  operation) :=
  fun _ _ _ _ _ execution => execution

/-- The actual invocation state and error conversion are retained separately
from caller cleanup. This does not invent an invocation or an allocation exit. -/
def Conversion (types : Types) (profile : Profile)
    (invoked : Outcome types.resources.State (Except types.resources.ProgramError Unit)
      types.resources.Unwind types.resources.Terminal)
    (pending : Outcome types.resources.State (Except (Error types.resources profile) Unit)
      types.resources.Unwind types.resources.Terminal) : Prop :=
  match invoked with
  | .returned (.ok ()) after => pending = .returned (.ok ()) after
  | .returned (.error error) after => Callback.map Except.error
      (AccountInfoRc.lift (AnchorErrorOperations.fromProgram profile.storage
        types.resources.errors))
      after error pending
  | .unwound reason after => pending = .unwound reason after
  | .terminated reason => pending = .terminated reason

theorem invokeAndConvert_iff (types : Types) (profile : Profile) (instruction : Built
  types.resources)
    (infos : List AccountInfo.Value) (signers : List (List Solanalib.Runtime.Bytes)) (before :
      types.resources.State)
    (current : observe types.resources before instruction = some instruction.planned)
    (pending : Outcome types.resources.State (Except (Error types.resources profile) Unit)
      types.resources.Unwind types.resources.Terminal) :
    invokeAndConvert types profile instruction infos signers before () pending ↔
      ∃ invoked, types.invoke before ⟨instruction.planned, infos, signers⟩ invoked ∧
        Conversion types profile invoked pending := by
  rw [invokeAndConvert, current]
  simp only [Callback.bind]
  apply exists_congr
  intro invoked
  cases invoked with
  | returned result after => cases result with
    | error _ => rfl
    | ok valueUnit => cases valueUnit; rfl
  | unwound _ _ => rfl
  | terminated _ => rfl

/-- A reached current-read gate supplies the exact request for every actual
finite invocation and conversion continuation. Vector reads use current state. -/
theorem Ready.call_continue {types : Types} {operation : Operation}
    {before after : types.resources.State} {args : Args types.resources operation}
    (ready : Ready types operation before args) (point : CallPoint types.resources)
    (reached : AtCall types.resources operation before args point after)
    (invoked : Outcome types.resources.State (Except types.resources.ProgramError Unit)
      types.resources.Unwind types.resources.Terminal)
    (pending : Outcome types.resources.State (Except (Error types.resources operation.profile) Unit)
      types.resources.Unwind types.resources.Terminal)
    (called : types.invoke after
      ⟨point.instruction.planned, point.accounts.expected, args.context.signerSeeds⟩ invoked)
    (converted : Conversion types operation.profile invoked pending) :
    observe types.resources after point.instruction = some point.instruction.planned ∧
      point.accounts.read after = some point.accounts.expected ∧
      invokeAndConvert types operation.profile point.instruction point.accounts.expected
        args.context.signerSeeds after () pending := by
  have available := ready.call point after reached
  exact ⟨available.1, available.2,
    (invokeAndConvert_iff types operation.profile point.instruction point.accounts.expected
      args.context.signerSeeds after available.1 pending).mpr ⟨invoked, called, converted⟩⟩

/-- A successful instruction constructor is an earlier source prefix. Its
actual subsequent preparation, call and cleanup produce the corresponding
wrapper outcome without choosing replacement resources or states. -/
theorem run_after_build (types : Types) (operation : Operation)
    (before after : types.resources.State) (args : Args types.resources operation)
    (instruction : Built types.resources)
    (final : Outcome types.resources.State (Except (Error types.resources operation.profile) Unit)
      types.resources.Unwind types.resources.Terminal)
    (built : build types.resources operation before args (.returned instruction after))
    (continued : afterBuild types operation args instruction after () final) :
    run types operation before args final := ⟨.returned instruction after, built, continued⟩

theorem run_build_unwind (types : Types) (operation : Operation)
    (before after : types.resources.State) (args : Args types.resources operation)
    (reason : types.resources.Unwind)
    (final : Outcome types.resources.State (Except (Error types.resources operation.profile) Unit)
      types.resources.Unwind types.resources.Terminal)
    (built : build types.resources operation before args (.unwound reason after))
    (cleaned : Owned.cleanup types.resources.doubleUnwind
      (buildFailureDrops types.resources operation args) (.unwound reason after) final) :
    run types operation before args final := ⟨.unwound reason after, built, cleaned⟩

theorem run_build_terminal (types : Types) (operation : Operation) (before : types.resources.State)
    (args : Args types.resources operation) (reason : types.resources.Terminal)
    (built : build types.resources operation before args (.terminated reason)) :
    run types operation before args (.terminated reason) := ⟨.terminated reason, built, rfl⟩

/-- After an actual prefix return, DataV2 serialization uses exactly the
initial owned fields. No complete constructor outcome is an admission premise. -/
theorem Ready.metadata_read {types : Types} {before after : types.resources.State}
    {args : Args types.resources .metadata} (ready : Ready types .metadata before args)
    (allocated : types.resources.MetaResource × types.resources.ByteResource)
    (prefixRun : metadataPrefix types.resources args.context.accounts.keys
      args.extra.updateAuthoritySigner
      before () (.returned allocated after)) :
    ∃ data, args.extra.data.current before = some data ∧ args.extra.data.current after = some data
      := by
  obtain ⟨data, initial, retained⟩ := ready.metadataData
  exact ⟨data, initial, retained allocated after prefixRun⟩

/-- A finite literal work return requesting evaluation is accepted at the
next exact index, including an allocation step before the first expression. -/
theorem LiteralControl.evaluate_continue {resources : Resources} {count : Nat}
    (control : LiteralControl resources count) (values : List AccountInfo.Value)
    (before ready middle : resources.State) (value : AccountInfo.Value)
    (evaluate : Run resources Nat AccountInfo.Value)
    (final : Outcome resources.State resources.InfoResource
      (Owned.Array.Failure × resources.Unwind) resources.Terminal)
    (bounded : values.length ≤ count)
    (work : resources.literalProvider.work before (count, values) (.returned .evaluate ready))
    (expression : evaluate ready values.length (.returned value middle))
    (continued : Owned.Array.Trace resources.literalProvider count evaluate (values ++ [value])
      middle final) :
    Owned.Array.Trace resources.literalProvider count evaluate values before final :=
  .next values before ready middle value final (control.evaluate before values ready bounded work)
    work expression continued

/-- A finite literal finish command accepts its actual completion outcome.
This closes the local length check; it does not demand that completion returns. -/
theorem LiteralControl.finish_continue {resources : Resources} {count : Nat}
    (control : LiteralControl resources count) (values : List AccountInfo.Value)
    (before ready after : resources.State) (resource : resources.InfoResource)
    (evaluate : Run resources Nat AccountInfo.Value) (bounded : values.length ≤ count)
    (work : resources.literalProvider.work before (count, values) (.returned .finish ready))
    (completed : resources.literalProvider.finish ready values (.returned resource after)) :
    Owned.Array.Trace resources.literalProvider count evaluate values before (.returned resource
      after) :=
  .finishReturn values before ready after resource (control.finish before values ready bounded work)
    work completed

/-- Every evaluated occurrence is available to the source cleanup sequence
after an actual work unwind, even when some values compare equal. -/
theorem LiteralControl.unwind_continue {resources : Resources} {count : Nat}
    (control : LiteralControl resources count) (values : List AccountInfo.Value)
    (before after : resources.State) (reason : resources.Unwind)
    (evaluate : Run resources Nat AccountInfo.Value) (bounded : values.length ≤ count)
    (work : resources.literalProvider.work before (count, values) (.unwound reason after))
    (pending : Outcome resources.State resources.InfoResource resources.Unwind resources.Terminal)
    (cleaned : Owned.cleanup resources.doubleUnwind
      (resources.literalProvider.cleanupActions values
        (resources.literalProvider.cleanupOrder after values)) (.unwound reason after) pending) :
    Owned.Array.Trace resources.literalProvider count evaluate values before
      (Owned.Array.annotate ⟨values.length, .work⟩ pending) :=
  .workUnwind values before after reason _ work
    ⟨control.cleanup after values bounded, pending, cleaned, rfl⟩

/-- A missing current instruction at a reached call is rejected; a provider
cannot erase that local read merely by returning a nominal resource identity. -/
theorem Ready.rejects_missing_instruction {types : Types} {operation : Operation}
    {before after : types.resources.State} {args : Args types.resources operation}
    (point : CallPoint types.resources) (reached : AtCall types.resources operation before args
      point after)
    (missing : observe types.resources after point.instruction = none) :
    ¬ Ready types operation before args := by
  intro ready
  have retained := (ready.call point after reached).1
  rw [missing] at retained
  cases retained

end Solanalib.Specs.Core.AnchorSplSupport
