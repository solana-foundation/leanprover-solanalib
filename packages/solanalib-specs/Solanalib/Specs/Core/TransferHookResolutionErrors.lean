/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolutionFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-!
The complete operational family of the helper can return only the ordinary error
variants emitted by its checked borrow, TLV, POD and account-resolution paths.
This is an unconditional theorem about that mathematical family, including
actual allocation and cleanup outcomes. It is separate from source-call
correspondence and supplies the error-domain fact needed by the exact 2.2.2
ProgramError codec; no provider success or output-validity premise is added.
-/

namespace Solanalib.Specs.Core.TransferHookResolution.Errors

open Token.AllocatedControl
open Token (Bytes)

/-- The ProgramError variants reachable from this helper. Custom payloads fit the `u32` of Rust;
neither an arbitrary runtime error nor a String-bearing variant is
admitted by the local error constructors of the source. -/
def Supported : Token.Error → Prop
  | .InvalidAccountData | .AccountBorrowFailed => True
  | .Custom code => code < 2^32
  | _ => False

instance (error : Token.Error) : Decidable (Supported error) := by
  cases error <;> unfold Supported <;> infer_instance

/-- Every actual ordinary error of a subcomputation belongs to the supported
source domain. Unwinds, terminal exits and all intermediate states remain in
the original relation. -/
def ReturnsSupported {State Value Unwind Terminal : Type}
    (body : Token.AllocatedControl.Run State Value Unwind Terminal) : Prop :=
  ∀ before error after, body before (.returned (.error error) after) → Supported error

theorem cleanup_returned {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    {pending : Outcome State Value Unwind Terminal} {value : Value} {after : State}
    (cleaned : Owned.cleanup double drops pending (.returned value after)) :
    ∃ before, pending = .returned value before := by
  induction drops generalizing pending with
  | nil => exact ⟨after, cleaned.symm⟩
  | cons action rest induction =>
    cases pending with
    | returned actual state =>
      obtain ⟨dropped, _, continued⟩ := cleaned
      cases dropped with
      | returned doneValue middle =>
        obtain ⟨before, same⟩ := induction continued
        cases same
        exact ⟨state, rfl⟩
      | unwound reason middle =>
        obtain ⟨_, impossible⟩ := induction continued
        cases impossible
      | terminated reason => cases continued
    | unwound reason state =>
      obtain ⟨dropped, _, continued⟩ := cleaned
      cases dropped with
      | returned doneValue middle =>
        obtain ⟨_, impossible⟩ := induction continued
        cases impossible
      | unwound other middle =>
        obtain ⟨_, _, impossible⟩ := continued
        cases impossible
      | terminated terminal => cases continued
    | terminated reason => cases cleaned

theorem safe_pure {State Value Unwind Terminal : Type} (value : Value) :
    ReturnsSupported (pure (State := State) (Unwind := Unwind) (Terminal := Terminal) value) := by
  intro before error after returned
  cases returned

theorem safe_fail {State Value Unwind Terminal : Type} (error : Token.Error)
    (supported : Supported error) :
    ReturnsSupported (fail (State := State) (Value := Value) (Unwind := Unwind) (Terminal :=
      Terminal) error) := by
  intro before other after returned
  cases returned
  exact supported

theorem safe_inspect {State Value Unwind Terminal : Type} (observe : State → Option Value) :
    ReturnsSupported (inspect (Unwind := Unwind) (Terminal := Terminal) observe) := by
  rintro before error after ⟨_, _, impossible⟩
  cases impossible

theorem safe_perform {State Value Unwind Terminal : Type}
    (call : State → Outcome State Value Unwind Terminal → Prop) : ReturnsSupported (perform call)
      := by
  rintro before error after ⟨intermediate, _, impossible⟩
  cases intermediate <;> cases impossible

theorem safe_panic {State Value Unwind Terminal : Type}
    (call : State → Outcome State Empty Unwind Terminal → Prop) :
    ReturnsSupported (panic (Value := Value) call) := by
  rintro before error after ⟨intermediate, _, impossible⟩
  cases intermediate with
  | returned value _ => cases value
  | unwound _ _ => cases impossible
  | terminated _ => cases impossible

theorem safe_bind {State Value Next Unwind Terminal : Type}
    (first : Token.AllocatedControl.Run State Value Unwind Terminal)
    (next : Value → Token.AllocatedControl.Run State Next Unwind Terminal)
    (firstSafe : ReturnsSupported first) (nextSafe : ∀ value, ReturnsSupported (next value)) :
    ReturnsSupported (bind first next) := by
  rintro before error after ⟨intermediate, called, continued⟩
  cases intermediate with
  | returned value middle =>
    cases value with
    | ok value => exact nextSafe value middle error after continued
    | error original =>
      cases continued
      exact firstSafe _ _ _ called
  | unwound _ _ => cases continued
  | terminated _ => cases continued

theorem safe_scope {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Token.AllocatedControl.Run State Value Unwind Terminal) (safe : ReturnsSupported body) :
    ReturnsSupported (scope double drops body) := by
  rintro before error after ⟨pending, called, cleaned⟩
  obtain ⟨middle, rfl⟩ := cleanup_returned double drops cleaned
  exact safe before error middle called

theorem safe_moveOnOk {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Token.AllocatedControl.Run State Value Unwind Terminal) (safe : ReturnsSupported body) :
    ReturnsSupported (moveOnOk double drops body) := by
  rintro before error after ⟨pending, called, rest⟩
  cases pending with
  | returned value middle =>
    cases value with
    | ok value => cases rest
    | error original =>
      obtain ⟨state, same⟩ := cleanup_returned double drops rest
      cases same
      exact safe _ _ _ called
  | unwound reason middle =>
    obtain ⟨_, impossible⟩ := cleanup_returned double drops rest
    cases impossible
  | terminated reason =>
    obtain ⟨_, impossible⟩ := cleanup_returned double drops rest
    cases impossible

theorem safe_result {State Value Unwind Terminal : Type} (value : Except Token.Error Value)
    (supported : ∀ error, value = .error error → Supported error) :
    ReturnsSupported (result (State := State) (Unwind := Unwind) (Terminal := Terminal) value) := by
  intro before error after returned
  have same : value = .error error := by cases returned; rfl
  exact supported error same

theorem safe_callback_bind {State Args Value Next Unwind Terminal : Type}
    (first : Callback.Run State Args Value Unwind Terminal) (args : Args)
    (next : Value → Token.AllocatedControl.Run State Next Unwind Terminal)
    (nextSafe : ∀ value, ReturnsSupported (next value)) :
    ReturnsSupported (fun state => Callback.bind first next state args) := by
  rintro before error after ⟨intermediate, _, continued⟩
  cases intermediate with
  | returned value middle => exact nextSafe value middle error after continued
  | unwound _ _ => cases continued
  | terminated _ => cases continued

theorem safe_bindResult {State Value Next Unwind Terminal : Type}
    (first : Callback.Run State Unit (Except Token.Error Value) Unwind Terminal)
    (next : Value → Callback.Run State Unit (Except Token.Error Next) Unwind Terminal)
    (firstSafe : ReturnsSupported (fun state => first state ()))
    (nextSafe : ∀ value, ReturnsSupported (fun state => next value state ())) :
    ReturnsSupported (fun state => Token.AllocatedSeeds.bindResult first next state ()) := by
  rintro before error after ⟨intermediate, called, continued⟩
  cases intermediate with
  | returned value middle =>
    cases value with
    | ok value => exact nextSafe value middle error after continued
    | error original =>
      cases continued
      exact firstSafe _ _ _ called
  | unwound _ _ => cases continued
  | terminated _ => cases continued

theorem borrowData_safe (types : Types) (info : AccountInfo.Value) : ReturnsSupported (borrowData
  types info) := by
  intro before error after returned
  unfold borrowData Token.Onchain.borrowData at returned
  cases acquisition : AccountInfo.tryBorrow .shared info.data before.1 with
  | mk acquired pool =>
    rw [acquisition] at returned
    cases acquired with
    | error reason =>
      simp only [ite_true] at returned
      cases returned
      trivial
    | ok guard =>
      cases current : Borrow.current pool guard with
      | error reason => simp [current] at returned
      | ok value =>
        rcases value with ⟨fraction, content⟩
        cases content <;> simp [current] at returned

theorem protocol_cleanup_returned {Extra Resource Value Unwind Terminal : Type}
    (protocol : Token.AllocatedCollect.Protocol Extra Resource Unwind Terminal)
    (acquired : List Token.AllocatedCollect.Element)
    {pending : Outcome (World Extra) Value Unwind Terminal} {value : Value} {after : World Extra}
    (cleaned : protocol.cleanup acquired pending (.returned value after)) :
    ∃ before, pending = .returned value before := by
  cases pending with
  | returned old state => exact cleanup_returned protocol.double _ cleaned.2
  | unwound reason state => exact cleanup_returned protocol.double _ cleaned.2
  | terminated reason => cases cleaned

theorem collection_trace_safe {Extra Resource Unwind Terminal : Type}
    {protocol : Token.AllocatedCollect.Protocol Extra Resource Unwind Terminal}
    {iterator : Token.AllocatedCollect.Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value
      (Except Token.Error Token.AllocatedCollect.Element) Unwind Terminal}
    (callbackSafe : ∀ info, ReturnsSupported (fun state => callback state info))
    {position : Nat} {acquired : List Token.AllocatedCollect.Element}
    {before : World Extra} {calls : List Nat}
    {final : Outcome (World Extra) (Except Token.Error Resource) Unwind Terminal}
    (trace : Token.AllocatedCollect.Trace protocol iterator callback position acquired before calls
      final) :
    ∀ error after, final = .returned (.error error) after → Supported error := by
  induction trace with
  | done endOfIterator finished exit =>
    intro error after same
    cases same
    rename_i pending
    cases pending with
    | returned resource state => cases exit
    | unwound reason state =>
      change protocol.cleanup _ (.unwound reason state) _ at exit
      obtain ⟨_, impossible⟩ := protocol_cleanup_returned protocol _ exit
      cases impossible
    | terminated reason => cases exit
  | next within read called tail induction => exact induction
  | error within read called cleaned =>
    intro error after same
    cases same
    obtain ⟨_, same⟩ := protocol_cleanup_returned protocol _ cleaned
    cases same
    exact callbackSafe _ _ _ _ called
  | unwind within read called cleaned =>
    intro error after same
    cases same
    obtain ⟨_, impossible⟩ := protocol_cleanup_returned protocol _ cleaned
    cases impossible
  | terminal => intro error after impossible; cases impossible
  | internalReturn within stepped tail induction => exact induction
  | internalUnwind within stepped cleaned =>
    intro error after same
    cases same
    obtain ⟨_, impossible⟩ := protocol_cleanup_returned protocol _ cleaned
    cases impossible
  | internalTerminal => intro error after impossible; cases impossible

theorem collectRefs_safe (types : Types) (resource : types.InfoResource) :
    ReturnsSupported (collectRefs types resource) := by
  apply safe_bind _ _ (safe_inspect _)
  intro infos before error after executed
  obtain ⟨calls, trace⟩ := executed
  apply collection_trace_safe (fun info => safe_bind _ _ (borrowData_safe types info)
    (fun _ => safe_pure _)) trace error after rfl

theorem validateFrom_safe {State Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (observe : State → Option Bytes) (resource : Resource) (byteLength offset : Nat) :
    ReturnsSupported (Token.AllocatedTlv.validateFrom ops observe resource byteLength offset) := by
  intro before error after executed
  rw [Token.AllocatedTlv.validateFrom] at executed
  obtain ⟨bytes, _, executed⟩ := executed
  dsimp only at executed
  split at executed
  · split at executed
    · split at executed
      · cases executed
      · cases executed; trivial
    · split at executed
      · cases executed
      · split at executed
        · cases executed; trivial
        · obtain ⟨pushed, _, executed⟩ := executed
          cases pushed with
          | returned doneValue middle =>
            obtain ⟨current, _, executed⟩ := executed
            split at executed
            · cases executed; trivial
            · exact validateFrom_safe ops observe resource byteLength
                (offset + 12 + Solanalib.Runtime.leNat (Solanalib.Runtime.slice current (offset +
                  8) 4))
                middle error after executed
          | unwound _ _ => cases executed
          | terminated _ => cases executed
  · cases executed
termination_by byteLength - offset
decreasing_by omega

theorem validate_safe {State Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (observe : State → Option Bytes) :
    ReturnsSupported (fun state => Token.AllocatedTlv.validate ops double observe state ()) := by
  rintro before error after ⟨bytes, _, pending, executed, cleaned⟩
  obtain ⟨middle, rfl⟩ := cleanup_returned double _ cleaned
  exact validateFrom_safe ops observe (ops.empty before).1 bytes.length 0 _ error middle executed

theorem findExecuteRange_error (fuel : Nat) (bytes : Bytes) (offset : Nat)
    (error : Token.Error) (returned : findExecuteRange fuel bytes offset = .error error) :
    Supported error := by
  induction fuel generalizing bytes offset with
  | zero => cases returned; trivial
  | succ fuel induction =>
    rw [findExecuteRange] at returned
    dsimp only at returned
    split at returned
    · cases returned; trivial
    · split at returned
      · split at returned
        · cases returned; trivial
        · cases returned
      · split at returned
        · cases returned; decide +kernel
        · exact induction _ _ returned

theorem podHeader_error (bytes : Bytes) (error : Token.Error)
    (returned : podHeader bytes = .error error) : Supported error := by
  unfold podHeader at returned
  dsimp only at returned
  split at returned
  · cases returned; decide +kernel
  · split at returned
    · split at returned <;> cases returned <;> decide +kernel
    · cases returned

theorem podAccess_error (bytes : Bytes) (error : Token.Error)
    (returned : podAccess bytes = .error (.inl error)) : Supported error := by
  unfold podAccess at returned
  cases header : podHeader bytes with
  | error original =>
    rw [header] at returned
    cases returned
    exact podHeader_error bytes error header
  | ok pair =>
    rcases pair with ⟨count, capacity⟩
    rw [header] at returned
    change ((if capacity < count then Except.error (.inr (.podSliceBounds count capacity))
      else Except.ok count) : Except (Token.Error ⊕ Panic) Nat) = Except.error (.inl error)
        at returned
    split at returned <;> cases returned

theorem extraSlice_safe (types : Types) (reference : DataRef) :
    ReturnsSupported (extraSlice types reference) := by
  apply safe_bind _ _ (safe_inspect _)
  intro bytes
  apply safe_bind _ _ (safe_result _ (findExecuteRange_error (bytes.length + 1) bytes 0))
  intro range
  cases accessed : podAccess (Solanalib.Runtime.slice bytes range.1 range.2) with
  | error failure =>
    cases failure with
    | inl error => exact safe_fail error (podAccess_error _ error accessed)
    | inr reason => exact safe_panic _
  | ok count => exact safe_pure _

theorem safe_map_ok {State Args Value Next Unwind Terminal : Type}
    (call : Callback.Run State Args Value Unwind Terminal) (args : Args) (map : Value → Next) :
    ReturnsSupported (fun state => Callback.map (fun value => Except.ok (map value)) call state
      args) := by
  rintro before error after ⟨pending, _, same⟩
  cases pending <;> cases same

theorem safe_owned_scope {State Args Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args (Except Token.Error Value) Unwind Terminal) (args : Args)
    (safe : ReturnsSupported (fun state => body state args)) :
    ReturnsSupported (fun state => Owned.scope double drops body state args) := by
  rintro before error after ⟨pending, called, cleaned⟩
  obtain ⟨middle, rfl⟩ := cleanup_returned double drops cleaned
  exact safe before error middle called

section Seeds

open Token.AllocatedSeeds

variable {State ByteResource SeedResource RefResource Unwind Terminal : Type}

theorem unpackOne_safe (bytes : Owned.VectorOps State UInt8 ByteResource Unwind Terminal)
    (input : Bytes) : ReturnsSupported (fun state => unpackOne bytes input state ()) := by
  cases input with
  | nil => exact safe_fail _ (by trivial)
  | cons tag rest =>
    unfold unpackOne
    dsimp only
    split
    · exact safe_pure _
    · split
      · cases rest with
        | nil => exact safe_fail _ (by decide +kernel)
        | cons length payload =>
          dsimp only
          split
          · exact safe_fail _ (by decide +kernel)
          · exact safe_map_ok _ () _
      · split
        · split
          · exact safe_pure _
          · exact safe_fail _ (by decide +kernel)
        · split
          · split
            · exact safe_pure _
            · exact safe_fail _ (by decide +kernel)
          · split
            · split
              · exact safe_pure _
              · exact safe_fail _ (by decide +kernel)
            · exact safe_fail _ (by trivial)

theorem unpackFrom_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (configurationAt : State → Option Solanalib.Runtime.Pubkey) (resource : SeedResource) (offset :
      Nat) :
    ReturnsSupported (unpackFrom ops configurationAt resource offset) := by
  intro before error after executed
  rw [unpackFrom] at executed
  split at executed
  · obtain ⟨configuration, _, decoded, called, continued⟩ := executed
    cases decoded with
    | returned value middle =>
      cases value with
      | error original =>
        cases continued
        exact unpackOne_safe ops.bytes (configuration.bytes.drop offset) _ _ _ called
      | ok seed =>
        obtain ⟨width, _, continued⟩ := continued
        cases seed <;> simp only at continued
        · cases continued
        all_goals
          split at continued
          · exact safe_callback_bind _ () _
              (fun _ => unpackFrom_safe ops configurationAt resource (offset + width))
              middle error after continued
          · cases continued
    | unwound _ _ => cases continued
    | terminated _ => cases continued
  · cases executed
termination_by 32 - offset
decreasing_by all_goals omega

theorem unpack_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (configurationAt : State → Option Solanalib.Runtime.Pubkey) :
    ReturnsSupported (fun state => unpack ops double configurationAt state ()) := by
  rintro before error after ⟨configuration, _, pending, called, continued⟩
  cases pending with
  | returned value middle =>
    cases value with
    | ok value => cases continued
    | error original =>
      obtain ⟨_, same⟩ := cleanup_returned double _ continued
      cases same
      exact unpackFrom_safe ops configurationAt (ops.seeds.empty before).1 0 _ _ _ called
  | unwound _ _ =>
    obtain ⟨_, impossible⟩ := cleanup_returned double _ continued
    cases impossible
  | terminated _ =>
    obtain ⟨_, impossible⟩ := cleanup_returned double _ continued
    cases impossible

theorem seedView_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (args : Token.AllocatedSeeds.Args State) (instruction : BytesView State)
    (seed : Seed ByteResource) : ReturnsSupported (fun state => seedView ops args instruction seed
      state ()) := by
  intro before error after executed
  cases seed with
  | uninitialized => cases executed
  | literal resource =>
    obtain ⟨_, _, impossible⟩ := executed
    cases impossible
  | instructionData offset length =>
    obtain ⟨_, _, executed⟩ := executed
    split at executed
    · cases executed; decide +kernel
    · cases executed
  | accountKey index =>
    obtain ⟨_, _, executed⟩ := executed
    split at executed
    · cases executed; decide +kernel
    · cases executed
  | accountData index offset length =>
    obtain ⟨_, _, executed⟩ := executed
    split at executed
    · cases executed; decide +kernel
    · cases executed; decide +kernel
    · split at executed
      · cases executed; decide +kernel
      · cases executed

theorem pushViewsFrom_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (args : Token.AllocatedSeeds.Args State) (instruction : BytesView State)
    (seeds : SeedResource) (references : RefResource) (seedCount index : Nat) :
    ReturnsSupported (pushViewsFrom ops args instruction seeds references seedCount index) := by
  intro before error after executed
  rw [pushViewsFrom] at executed
  split at executed
  · obtain ⟨current, _, _, seed, _, executed⟩ := executed
    apply safe_bindResult _ _ (seedView_safe ops args instruction seed) ?_ before error after
      executed
    intro view
    cases view with
    | none => exact pushViewsFrom_safe ops args instruction seeds references seedCount (index + 1)
    | some borrowed =>
      exact safe_callback_bind _ () _
        (fun _ => pushViewsFrom_safe ops args instruction seeds references seedCount (index + 1))
  · cases executed
termination_by seedCount - index
decreasing_by all_goals omega

theorem searchPda_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (find : FindPda State Unwind Terminal) (programAt : State → Option Solanalib.Runtime.Pubkey)
    (references : RefResource) : ReturnsSupported (fun state => searchPda ops find programAt
      references state ()) := by
  rintro before error after ⟨views, values, program, _, _, _, called⟩
  exact safe_map_ok find ⟨values, program⟩ Prod.fst before error after called

theorem resolvePda_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (find : FindPda State Unwind Terminal)
    (args : Token.AllocatedSeeds.Args State) (instruction : BytesView State)
    (programAt : State → Option Solanalib.Runtime.Pubkey) (seeds : SeedResource) :
    ReturnsSupported (fun state => resolvePda ops double find args instruction programAt seeds
      state ()) := by
  rintro before error after ⟨current, _, executed⟩
  exact safe_owned_scope double _ _ ()
    (safe_bindResult _ _
      (pushViewsFrom_safe ops args instruction seeds (ops.refs.empty before).1 current.length 0)
      (fun _ => searchPda_safe ops find programAt (ops.refs.empty before).1))
    (ops.refs.empty before).2 error after executed

theorem finishMeta_safe (args : Token.AllocatedSeeds.Args State) (key : Solanalib.Runtime.Pubkey) :
    ReturnsSupported (fun state => finishMeta (Unwind := Unwind) (Terminal := Terminal) args key
      state ()) := by
  rintro before error after ⟨_, _, impossible⟩
  cases impossible

theorem resolveSelected_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (find : FindPda State Unwind Terminal)
    (args : Token.AllocatedSeeds.Args State) (programAt : State → Option Solanalib.Runtime.Pubkey) :
    ReturnsSupported (fun state => resolveSelected ops double find args programAt state ()) := by
  rintro before error after ⟨instruction, _, executed⟩
  exact safe_bindResult _ _ (unpack_safe ops double _) (fun seeds =>
    safe_owned_scope double _ _ ()
      (safe_bindResult _ _
        (resolvePda_safe ops double find args ⟨instruction.length, args.instructionAt⟩ programAt
          seeds)
        (finishMeta_safe args))) before error after executed

theorem resolveKeyData_safe (args : Token.AllocatedSeeds.Args State) (configuration :
  Solanalib.Runtime.Pubkey) :
    ReturnsSupported (fun state => resolveKeyData (Unwind := Unwind) (Terminal := Terminal)
      args configuration state ()) := by
  intro before error after executed
  unfold resolveKeyData at executed
  split at executed
  · obtain ⟨instruction, _, executed⟩ := executed
    split at executed
    · cases executed
    · cases executed; decide +kernel
  · obtain ⟨accounts, _, executed⟩ := executed
    split at executed
    · cases executed; decide +kernel
    · cases executed; decide +kernel
    · split at executed
      · cases executed
      · cases executed; decide +kernel
  · cases executed; decide +kernel
  · cases executed; decide +kernel
  · cases executed; trivial

theorem resolve_safe (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (find : FindPda State Unwind Terminal)
    (args : Token.AllocatedSeeds.Args State) :
    ReturnsSupported (fun state => resolve ops double find args state ()) := by
  rintro before error after ⟨extra, _, executed⟩
  dsimp only at executed
  split at executed
  · cases executed
  · split at executed
    · obtain ⟨_, _, executed⟩ := executed
      exact resolveSelected_safe ops double find args args.programAt before error after executed
    · split at executed
      · obtain ⟨_, _, executed⟩ := executed
        split at executed
        · cases executed; decide +kernel
        · exact resolveSelected_safe ops double find args _ before error after executed
      · split at executed
        · exact safe_bindResult _ _ (resolveKeyData_safe args extra.configuration)
            (finishMeta_safe args) before error after executed
        · cases executed; trivial

end Seeds

theorem cloneInfo_safe (types : Types) (info : AccountInfo.Value) :
    ReturnsSupported (cloneInfo types info) := safe_perform _

theorem withData_safe (types : Types) {Value : Type} (info : AccountInfo.Value)
    (body : DataRef → Run types Value) (safe : ∀ reference, ReturnsSupported (body reference)) :
    ReturnsSupported (withData types info body) :=
  safe_bind _ _ (borrowData_safe types info)
    (fun reference => safe_scope _ _ _ (safe reference))

theorem executeInfos_safe (types : Types) (args : Args types) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    ReturnsSupported (executeInfos types args validation instruction) := by
  rintro before error after ⟨detailed, _, executed⟩
  cases detailed with
  | returned _ _ => cases executed
  | unwound failure middle =>
    rcases failure with ⟨failure, reason⟩
    obtain ⟨_, impossible⟩ := cleanup_returned types.doubleUnwind _ executed
    cases impossible
  | terminated _ => cases executed

theorem pushClonedInfo_safe (types : Types) (resource : types.InfoResource)
    (info : AccountInfo.Value) : ReturnsSupported (pushClonedInfo types resource info) :=
  safe_bind _ _ (cloneInfo_safe types info) (fun _ => safe_perform _)

theorem resolveExtra_safe (types : Types) (execute : Execute types) (slice : ExtraSlice)
    (index : Nat) : ReturnsSupported (resolveExtra types execute slice index) :=
  safe_bind _ _ (collectRefs_safe types execute.infos) (fun _ =>
    safe_scope _ _ _ (resolve_safe types.seedOps types.doubleUnwind types.findPda _))

theorem appendResolved_safe (types : Types) (args : Args types) (execute : Execute types)
    (resolved : Solanalib.Runtime.CpiMeta) : ReturnsSupported (appendResolved types args execute
      resolved) := by
  apply safe_bind _ _ (safe_inspect _)
  intro previous
  dsimp only
  split
  · exact safe_fail _ (by decide +kernel)
  · exact safe_bind _ _ (cloneInfo_safe types _) (fun _ =>
      safe_bind _ _ (safe_moveOnOk _ _ _ (safe_perform _)) (fun _ => safe_perform _))

theorem addExtraEntries_safe (types : Types) (args : Args types) (execute : Execute types)
    (slice : ExtraSlice) (remaining index : Nat) :
    ReturnsSupported (addExtraEntries types args execute slice remaining index) := by
  induction remaining generalizing index with
  | zero => exact safe_pure ()
  | succ remaining induction =>
    exact safe_bind _ _ (resolveExtra_safe types execute slice index) (fun resolved =>
      safe_bind _ _ (appendResolved_safe types args execute resolved) (fun _ => induction (index +
        1)))

theorem addExtraList_safe (types : Types) (args : Args types) (execute : Execute types)
    (reference : DataRef) : ReturnsSupported (addExtraList types args execute reference) :=
  safe_bind _ _ (validate_safe types.discriminators types.doubleUnwind reference.read) (fun _ =>
    safe_bind _ _ (extraSlice_safe types reference) (fun slice =>
      addExtraEntries_safe types args execute slice slice.count 0))

theorem executeInstruction_safe (types : Types) (args : Args types) (programId :
  Solanalib.Runtime.Pubkey) :
    ReturnsSupported (executeInstruction types args programId) := by
  intro before error after executed
  exact safe_moveOnOk _ _ _
    (safe_bind _ _ (safe_perform _) (fun _ =>
      safe_bind _ _ (safe_perform _) (fun _ =>
      safe_bind _ _ (safe_perform _) (fun _ => safe_pure _))))
    (types.bytes.empty before).2 error after executed

theorem executePrelude_safe (types : Types) (args : Args types)
    (programId validationKey : Solanalib.Runtime.Pubkey) :
    ReturnsSupported (executePrelude types args programId validationKey) :=
  safe_bind _ _ (executeInstruction_safe types args programId) (fun _ =>
    safe_moveOnOk _ _ _ (safe_bind _ _ (safe_perform _) (fun _ => safe_pure _)))

theorem copyExtras_safe (types : Types) (transfer execute : Execute types) :
    ReturnsSupported (copyExtras types transfer execute) :=
  safe_bind _ _ (safe_inspect _) (fun _ =>
    safe_bind _ _ (safe_perform _) (fun _ =>
    safe_bind _ _ (safe_inspect _) (fun _ => safe_perform _)))

theorem appendReadonly_safe (types : Types) (prepared : Execute types)
    (key : Solanalib.Runtime.Pubkey) (info : AccountInfo.Value) :
    ReturnsSupported (appendReadonly types prepared key info) :=
  safe_bind _ _ (safe_perform _) (fun _ => pushClonedInfo_safe types prepared.infos info)

theorem hookEntry_safe (types : Types) (args : Args types) (programId : Solanalib.Runtime.Pubkey) :
    ReturnsSupported (hookEntry types args programId) := by
  apply safe_bind _ _ (safe_perform _)
  intro value
  dsimp only
  split
  · exact safe_fail _ (by decide +kernel)
  · exact safe_pure _

theorem addHook_safe (types : Types) (args : Args types)
    (programId : Solanalib.Runtime.Pubkey) (transfer : Execute types) :
    ReturnsSupported (addHook types args programId transfer) := by
  apply safe_bind _ _ (safe_moveOnOk _ _ _ (hookEntry_safe types args programId))
  rintro ⟨validationKey, program, validation⟩
  cases validation with
  | none => exact safe_scope _ _ _ (appendReadonly_safe types transfer programId program)
  | some validationInfo =>
    exact safe_bind _ _
      (safe_moveOnOk _ _ _ (executePrelude_safe types args programId validationKey))
      (fun instruction =>
        safe_bind _ _ (executeInfos_safe types args validationInfo instruction) (fun infos =>
          safe_bind _ _ (safe_scope _ _ _ (safe_scope _ _ _
            (safe_bind _ _
              (withData_safe types validationInfo _ (addExtraList_safe types args ⟨instruction,
                infos⟩))
              (fun _ => safe_bind _ _ (copyExtras_safe types transfer ⟨instruction, infos⟩)
                (fun _ => appendReadonly_safe types transfer validationKey validationInfo)))))
            (fun _ => appendReadonly_safe types transfer programId program)))

/-- Every ordinary error of the full helper, including all resolver and cleanup
paths, has a concrete ProgramError 2.2.2 representation. The callback protocols
cannot synthesize a String-bearing or out-of-range custom error. This result
places no condition on successful returns, unwinds, terminal exits or states. -/
theorem run_error_supported (types : Types) (args : Args types)
    (before after : World types.Extra) (error : Token.Error)
    (execution : run types before args (.returned (.error error) after)) : Supported error :=
  addHook_safe types args args.programId ⟨args.instruction, args.infos⟩ before error after execution

end Solanalib.Specs.Core.TransferHookResolution.Errors
