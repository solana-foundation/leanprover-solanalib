/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.accounts
public import Solanalib.Specs.AnchorLang.loading
public import Solanalib.Specs.AnchorLang.construct
public import Solanalib.Specs.AnchorLang.log
public import Solanalib.Specs.AnchorLang.Capabilities
public import Solanalib.Specs.AnchorLang.Lifecycle

@[expose] public section

open Solanalib.Specs

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.Accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount

/-- Interface dereference yields the underlying AccountInfo, not a value of
the phantom program type. The key projection therefore sees the original key. -/
theorem interface_then_key (info : AccountInfo.Value) :
    infoKey (interfaceDeref (Interface.mk (Tag := Empty) ⟨info⟩)) = info.key := rfl

/-- InterfaceAccount dereference exposes its decoded payload while retaining
the separately stored owner for later exit behavior. -/
theorem interface_account_projection (payload : Nat) (info : AccountInfo.Value)
    (remembered : _root_.Solanalib.Runtime.Pubkey) :
    interfaceAccountDeref (InterfaceAccount.mk ⟨payload, info⟩ remembered) = payload := rfl

def loadedState : AccountInfo.State :=
  (Borrow.transfer (AccountInfo.tryBorrow .shared AccountInfo.sampleInfo.data
    AccountInfo.sampleState).2 ⟨0, 0⟩ (.bytesRange 1 2)).2

/-- A successful load consumes generation zero and exposes exactly the payload
range through generation one of the same shared guard. -/
theorem mapped_view_is_live :
    Borrow.current loadedState ⟨0, 1⟩ = .ok (.bytesRange 1 2, .data [10, 20, 30]) ∧
    Borrow.current loadedState ⟨0, 0⟩ = .error .invalidGuard ∧
    AccountInfo.projectBytes (.bytesRange 1 2) (.data [10, 20, 30]) = .ok [20, 30] :=
  ⟨rfl, rfl, rfl⟩

def borrowedState : AccountInfo.State :=
  (AccountInfo.tryBorrowMutData AccountInfo.sampleState AccountInfo.sampleArgs).2

/-- Anchor adds the writable check before attempting the mutable borrow. A
nonwritable, already borrowed account reports AccountNotMutable first. -/
theorem writable_check_precedes_borrow :
    load .exclusive loadSample borrowedState
      ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩ =
      some (.returned (.error (error .notMutable)) borrowedState) := rfl

/-- Shared loading has no owner callback and does not recheck the owner. -/
theorem load_does_not_recheck_owner :
    load .shared loadSample AccountInfo.sampleState
      ⟨AccountInfo.sampleProfile,
        ⟨{ AccountInfo.sampleInfo with owner := _root_.Solanalib.Runtime.Pubkey.ofNat 88 }⟩, 8⟩ =
      some (.returned (.ok ⟨⟨0, 1⟩⟩) loadedState) := rfl

def shortIndex : LoadIndex := ⟨Nat, [10], 3, 1, true⟩

def releasedShared : AccountInfo.State :=
  (Borrow.release (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2 ⟨0,
    0⟩).2

/-- A matching discriminator alone does not establish the slice
bounds of the payload. Unwinding releases the acquired guard. -/
theorem prefix_match_short_payload_panics :
    load .shared shortIndex AccountInfo.sampleState
      ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩ =
      some (.unwound .sliceBounds releasedShared) ∧
    releasedShared.sharedCount AccountInfo.sampleInfo.data = 0 := ⟨rfl, rfl⟩

/-- A zero-sized payload can have alignment eight. Unlike a size-two,
alignment-eight pair, these arithmetic layout parameters are consistent. -/
def misalignedIndex : LoadIndex := ⟨Unit, [10], 0, 8, true⟩

theorem cast_alignment_panic :
    load .shared misalignedIndex AccountInfo.sampleState
      ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩ =
      some (.unwound .castAlignment releasedShared) := rfl

/-- The exact observation family retains the alignment panic and its actual
guard cleanup. It imposes no unused source-range hypothesis. -/
theorem misaligned_family_panic :
    (AnchorLang.accounts.account_loader.AccountLoader.load_observation_contract.contract
      misalignedIndex).requires AccountInfo.sampleState
        ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩ ∧
    AnchorLang.accounts.account_loader.AccountLoader.load_observation_run
      misalignedIndex
      AccountInfo.sampleState ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩
      (.unwound .castAlignment releasedShared) := ⟨trivial, cast_alignment_panic⟩

def releasedExclusive : AccountInfo.State :=
  (Borrow.release (AccountInfo.tryBorrowMutData AccountInfo.sampleState AccountInfo.sampleArgs).2
    ⟨0, 0⟩).2

/-- RefMut mapping also releases its exclusive lease on an unwinding bounds
panic. The abort case deliberately has no cleanup state. -/
theorem mutable_mapping_panic_cleanup :
    load .exclusive shortIndex AccountInfo.sampleState
      ⟨AccountInfo.sampleProfile, ⟨{ AccountInfo.sampleInfo with isWritable := true }⟩, 8⟩ =
      some (.unwound .sliceBounds releasedExclusive) ∧
    releasedExclusive.exclusiveCount AccountInfo.sampleInfo.data = 0 ∧
    load .exclusive shortIndex AccountInfo.sampleState
      ⟨{ AccountInfo.sampleProfile with aborts := true },
        ⟨{ AccountInfo.sampleInfo with isWritable := true }⟩, 8⟩ =
      some (.terminated .sliceBounds) := ⟨rfl, rfl, rfl⟩

def mismatchIndex : LoadIndex := ⟨Nat, [11], 2, 1, true⟩
def missingIndex : LoadIndex := ⟨Nat, [10, 20, 30, 40], 2, 1, true⟩

theorem discriminator_errors_release :
    load .shared mismatchIndex AccountInfo.sampleState
      ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩ =
      some (.returned (.error (error .discriminatorMismatch)) releasedShared) ∧
    load .shared missingIndex AccountInfo.sampleState
      ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 8⟩ =
      some (.returned (.error (error .discriminatorNotFound)) releasedShared) := ⟨rfl, rfl⟩

/-- The initializer has no owner-callback or data-codec path after the system
owner and zero balance condition has already produced its checked error. -/
theorem system_zero_is_uninitialized :
    initialized (Unwind := String) (Terminal := String)
      constructorSample.ownerAt
      ((Borrow.replaceCell AccountInfo.sampleState AccountInfo.sampleInfo.lamports (.lamports
        0)).2, ())
      AccountInfo.sampleArgs =
      some (.returned (.error (error .notInitialized))
        ((AccountInfo.observe .lamports
          (Borrow.replaceCell AccountInfo.sampleState AccountInfo.sampleInfo.lamports (.lamports
            0)).2
          AccountInfo.sampleInfo).2, ())) := rfl

namespace Initialization

/-- A successful borrow of this designated cell would expose data, not lamports. -/
def malformedArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with
    info := { AccountInfo.sampleInfo with lamports := AccountInfo.sampleInfo.data } }

theorem malformed_raw_initialization :
    initialized (Unwind := String) (Terminal := String) constructorSample.ownerAt
      (AccountInfo.sampleState, ()) malformedArgs = none := rfl

/-- Both exact observation families reject the malformed read at entry,
before any successful-prefix premise can become vacuous. -/
theorem malformed_entry_rejected :
    ¬ ((constructorFamily .account).contract constructorSample).requires
      (AccountInfo.sampleState, ()) malformedArgs ∧
    ¬ ((constructorFamily .interfaceAccount).contract constructorSample).requires
      (AccountInfo.sampleState, ()) malformedArgs := by
  constructor <;> intro ready <;> exact ready.1 rfl rfl

theorem malformed_raw_constructor_empty
    (outcome : Outcome (World Unit) (Except Error (Account Nat))
      (ConstructorUnwind String) (ConstructorTerminal String)) :
    ¬ construct .account constructorSample (AccountInfo.sampleState, ()) malformedArgs outcome := by
  rintro ⟨_, started, _⟩
  change none = some _ at started
  cases started

/-- A conflict is observed before the malformed cell projection. Admission
therefore keeps this actual panic, even with an abstract zero-width profile. -/
def busyArgs (aborts : Bool) : AccountInfo.Args :=
  { malformedArgs with profile := ⟨0, aborts⟩ }

theorem borrow_failure_admitted (aborts : Bool) :
    ((constructorFamily .account).contract constructorSample).requires
      (borrowedState, ()) (busyArgs aborts) ∧
    ((constructorFamily .interfaceAccount).contract constructorSample).requires
      (borrowedState, ()) (busyArgs aborts) := by
  have domain : InitReady constructorSample.ownerAt (borrowedState, ()) (busyArgs aborts) := by
    intro _ impossible
    cases impossible
  have noSuccess : ∀ after, initialized (Unwind := String) (Terminal := String)
      constructorSample.ownerAt (borrowedState, ()) (busyArgs aborts) =
        some (.returned (.ok ()) after) → False := by
    intro after called
    cases aborts <;> cases called
  exact ⟨⟨domain, fun after called => False.elim (noSuccess after called)⟩,
    ⟨domain, fun after called => False.elim (noSuccess after called)⟩⟩

theorem borrow_failure_retains_unwind_and_abort :
    construct .account constructorSample (borrowedState, ()) (busyArgs false)
      (.unwound (.inl .borrowFailed) (borrowedState, ())) ∧
    construct .interfaceAccount constructorSample (borrowedState, ()) (busyArgs true)
      (.terminated (.inl .borrowFailed)) := by
  constructor
  · exact ⟨.unwound (.inl .borrowFailed) (borrowedState, ()), rfl, rfl⟩
  · exact ⟨.terminated (.inl .borrowFailed), rfl, rfl⟩

def zeroState : AccountInfo.State :=
  (Borrow.replaceCell AccountInfo.sampleState AccountInfo.sampleInfo.lamports (.lamports 0)).2

def zeroAfter : AccountInfo.State :=
  (AccountInfo.observe .lamports zeroState AccountInfo.sampleInfo).2

theorem zero_balance_admitted_and_retained :
    ((constructorFamily .account).contract constructorSample).requires
      (zeroState, ()) AccountInfo.sampleArgs ∧
    construct .account constructorSample (zeroState, ()) AccountInfo.sampleArgs
      (.returned (.error (error .notInitialized)) (zeroAfter, ())) := by
  refine ⟨⟨?_, ?_⟩, .returned (.error (error .notInitialized)) (zeroAfter, ()), rfl, rfl⟩
  · intro _ impossible
    cases impossible
  · intro after started
    change (some (.returned (.error (error .notInitialized)) (zeroAfter, ())) :
      Option (Outcome (World Unit) (Except Error Unit) (ConstructorUnwind String)
        (ConstructorTerminal String))) = some (.returned (.ok ()) after) at started
    cases started

def nonSystem : ConstructorIndex :=
  { constructorSample with
    ownerAt := fun _ _ => .ofNat 1
    owner := Callback.ofFunction fun state _ => .returned (.ofNat 1) state }

theorem non_system_ready :
    ((constructorFamily .account).contract nonSystem).requires (sampleAfterInit, ()) malformedArgs
      := by
  refine ⟨?_, ?_⟩
  · intro impossible
    exact False.elim ((by decide : _root_.Solanalib.Runtime.Pubkey.ofNat 1 ≠ .zero) impossible)
  intro after started checked owned
  change (some (.returned (.ok ()) (sampleAfterInit, ())) :
    Option (Outcome (World Unit) (Except Error Unit) (ConstructorUnwind String)
      (ConstructorTerminal String))) = some (.returned (.ok ()) after) at started
  cases started
  have same : checked = (sampleAfterInit, ()) := by
    simp [ownerCheck, nonSystem, widenCallback, Callback.ofFunction, Callback.bind, widen] at owned
    exact (Outcome.returned.inj owned).2
  cases same
  exact decode_sample_ready

/-- The non-system branch does not call the malformed lamports projection;
the full admitted constructor still reaches the real decoder and release. -/
theorem non_system_bypasses_malformed_lamports :
    (AccountInfo.observe .lamports sampleAfterInit malformedArgs.info).1 = .malformed ∧
    construct .account nonSystem (sampleAfterInit, ()) malformedArgs
      (.returned (.ok (Account.mk (7 : Nat) malformedArgs.info)) (sampleAfterDecode, ())) := by
  refine ⟨rfl, ?_⟩
  have owned : ownerCheck nonSystem (sampleAfterInit, ()) malformedArgs
      (.returned (.ok ()) (sampleAfterInit, ())) :=
    ⟨.returned (.ofNat 1) (sampleAfterInit, ()),
      ⟨.returned (.ofNat 1) (sampleAfterInit, ()), rfl, rfl⟩, rfl⟩
  obtain ⟨decoded, released, retained⟩ := constructor_account_retain non_system_ready rfl owned rfl
    rfl
    (show nonSystem.deserialize (sampleDataDuring, ())
      ⟨malformedArgs.info, ⟨1, 0⟩, [10, 20, 30]⟩
      (.returned ⟨.ok (7 : Nat), []⟩ (sampleDataDuring, ())) from rfl)
  change some (Outcome.returned (Except.ok (7 : Nat)) (sampleAfterDecode, ())) = some decoded
    at released
  cases released
  exact retained

end Initialization

def changingOwner : ConstructorIndex where
  Aux := Nat
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := [10]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction (fun state _ =>
    .returned (_root_.Solanalib.Runtime.Pubkey.ofNat (state.2 + 1)) (state.1, state.2 + 1))
  checkOwner := fun _ _ _ => False
  deserialize := fun _ _ _ => False

/-- The comparison uses the first callback result, while the diagnostic uses
the second. The effects of both calls survive in the error state. -/
theorem owner_mismatch_calls_twice (state : AccountInfo.State) :
    ownerCheck changingOwner (state, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.error ((error .ownedByWrongProgram).replaceCompared
        (.pubkeys .zero (_root_.Solanalib.Runtime.Pubkey.ofNat 2)))) (state, (2 : Nat))) := by
  refine ⟨.returned (_root_.Solanalib.Runtime.Pubkey.ofNat 1) (state, (1 : Nat)),
    ⟨.returned (_root_.Solanalib.Runtime.Pubkey.ofNat 1) (state, (1 : Nat)), rfl, rfl⟩, ?_⟩
  exact ⟨.returned (_root_.Solanalib.Runtime.Pubkey.ofNat 2) (state, (2 : Nat)),
    ⟨.returned (_root_.Solanalib.Runtime.Pubkey.ofNat 2) (state, (2 : Nat)), rfl, rfl⟩, rfl⟩

def callbackError : Error := programError (.custom 77)

def effectIndex
    (decoder : World Nat → DecodeArgs → Outcome (World Nat) (Decoded Nat) String String) :
    ConstructorIndex where
  Aux := Nat
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := [10]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction (fun state _ => .returned .zero state)
  checkOwner := Callback.ofFunction (fun state _ => .returned (.ok ()) state)
  deserialize := Callback.ofFunction decoder

/-- The concrete prefix reaches this one codec input. Its admission is
universal over finite exits there and does not assume a completed constructor. -/
theorem effect_index_account_ready
    (decoder : World Nat → DecodeArgs → Outcome (World Nat) (Decoded Nat) String String)
    (admitted : AccountInfo.GuardCallback.Admissible ⟨1, 0⟩ (Callback.ofFunction decoder)
      (sampleDataDuring, (0 : Nat)) ⟨AccountInfo.sampleInfo, ⟨1, 0⟩, [10, 20, 30]⟩) :
    ((constructorFamily .account).contract (effectIndex decoder)).requires
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro _ impossible
    cases impossible
  intro after started checked owned
  change (some (.returned (.ok ()) (sampleAfterInit, (0 : Nat))) :
    Option (Outcome (World Nat) (Except Error Unit) (ConstructorUnwind String)
      (ConstructorTerminal String))) = some (.returned (.ok ()) after) at started
  cases started
  have same : checked = (sampleAfterInit, (0 : Nat)) := by
    simp [ownerCheck, effectIndex, widenCallback, Callback.ofFunction, Callback.bind, widen]
      at owned
    exact (Outcome.returned.inj owned).2
  cases same
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current
  change (Except.ok (⟨1, 0⟩ : Borrow.Guard), sampleDataDuring) = (.ok guard, during) at acquired
  cases acquired
  change Except.ok (AccountInfo.View.whole, AccountInfo.Content.data [10, 20, 30]) =
    .ok (view, .data bytes) at current
  cases current
  exact admitted

theorem effect_index_owner_check
    (decoder : World Nat → DecodeArgs → Outcome (World Nat) (Decoded Nat) String String) :
    ownerCheck (effectIndex decoder) (sampleAfterInit, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.ok ()) (sampleAfterInit, (0 : Nat))) :=
  ⟨.returned .zero (sampleAfterInit, (0 : Nat)),
    ⟨.returned .zero (sampleAfterInit, (0 : Nat)), rfl, rfl⟩, rfl⟩

def errorDecoder (state : World Nat) (_ : DecodeArgs) :
    Outcome (World Nat) (Decoded Nat) String String :=
  .returned ⟨.error callbackError, [99]⟩ (state.1, state.2 + 1)

theorem error_constructor_admitted :
    ((constructorFamily .account).contract (effectIndex errorDecoder)).requires
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs := by
  apply effect_index_account_ready
  intro produced called
  cases called
  exact sharedDataFrame_refl _ _ sampleDataDuring_valid

/-- An ordinary error from a decoder is not rolled back. The local data guard is
released, while the changed captured state and exact error payload survive. -/
theorem decoder_error_releases_and_preserves_effects :
    decodeAccount (effectIndex errorDecoder) (sampleAfterInit, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.error callbackError) (sampleAfterDecode, (1 : Nat))) := by
  exact ⟨.returned ⟨.error callbackError, [99]⟩ (sampleDataDuring, (1 : Nat)), rfl, rfl⟩

/-- The same behavior composes through Account::try_from, including its earlier
lamports check and owner callback. -/
theorem account_error_composition :
    construct .account (effectIndex errorDecoder)
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs
      (.returned (.error callbackError) (sampleAfterDecode, (1 : Nat))) := by
  obtain ⟨decoded, released, retained⟩ := constructor_account_retain
    error_constructor_admitted rfl (effect_index_owner_check errorDecoder) rfl rfl
    (show (effectIndex errorDecoder).deserialize (sampleDataDuring, (0 : Nat))
      ⟨AccountInfo.sampleInfo, ⟨1, 0⟩, [10, 20, 30]⟩
      (.returned ⟨.error callbackError, [99]⟩ (sampleDataDuring, (1 : Nat))) from rfl)
  change some (Outcome.returned (Except.error callbackError) (sampleAfterDecode, (1 : Nat))) =
    some decoded at released
  cases released
  exact retained

def panicDecoder (state : World Nat) (_ : DecodeArgs) :
    Outcome (World Nat) (Decoded Nat) String String := .unwound "decode" (state.1, state.2 + 2)

theorem panic_constructor_admitted :
    ((constructorFamily .account).contract (effectIndex panicDecoder)).requires
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs := by
  apply effect_index_account_ready
  intro produced called
  cases called
  exact sharedDataFrame_refl _ _ sampleDataDuring_valid

theorem decoder_panic_releases_and_preserves_effects :
    decodeAccount (effectIndex panicDecoder) (sampleAfterInit, (0 : Nat)) AccountInfo.sampleArgs
      (.unwound (.inr "decode") (sampleAfterDecode, (2 : Nat))) := by
  exact ⟨.unwound "decode" (sampleDataDuring, (2 : Nat)), rfl, rfl⟩

/-- The admitted unwind continues through the entire observation constructor,
retaining its actual auxiliary effect and performing the checked release. -/
theorem account_panic_composition :
    construct .account (effectIndex panicDecoder)
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs
      (.unwound (.inr "decode") (sampleAfterDecode, (2 : Nat))) := by
  obtain ⟨decoded, released, retained⟩ := constructor_account_retain
    panic_constructor_admitted rfl (effect_index_owner_check panicDecoder) rfl rfl
    (show (effectIndex panicDecoder).deserialize (sampleDataDuring, (0 : Nat))
      ⟨AccountInfo.sampleInfo, ⟨1, 0⟩, [10, 20, 30]⟩
      (.unwound "decode" (sampleDataDuring, (2 : Nat))) from rfl)
  change some (Outcome.unwound (.inr "decode") (sampleAfterDecode, (2 : Nat))) = some decoded
    at released
  cases released
  exact retained

def stopDecoder (_ : World Nat) (_ : DecodeArgs) :
    Outcome (World Nat) (Decoded Nat) String String := .terminated "stop"

theorem terminal_constructor_admitted :
    ((constructorFamily .account).contract (effectIndex stopDecoder)).requires
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs := by
  apply effect_index_account_ready
  intro produced called
  cases called
  trivial

/-- A terminal callback creates neither a post-state nor fictitious cleanup. -/
theorem decoder_terminal_has_no_state :
    decodeAccount (effectIndex stopDecoder) (sampleAfterInit, (0 : Nat)) AccountInfo.sampleArgs
      (.terminated (.inr "stop")) := ⟨.terminated "stop", rfl, rfl⟩

/-- A terminal callback also extends through the admitted full constructor,
without a post-state or a fabricated release. -/
theorem account_terminal_composition :
    construct .account (effectIndex stopDecoder)
      (AccountInfo.sampleState, (0 : Nat)) AccountInfo.sampleArgs
      (.terminated (.inr "stop")) := by
  obtain ⟨decoded, released, retained⟩ := constructor_account_retain
    terminal_constructor_admitted rfl (effect_index_owner_check stopDecoder) rfl rfl
    (show (effectIndex stopDecoder).deserialize (sampleDataDuring, (0 : Nat))
      ⟨AccountInfo.sampleInfo, ⟨1, 0⟩, [10, 20, 30]⟩ (.terminated "stop") from rfl)
  change some (Outcome.terminated (.inr "stop")) = some decoded at released
  cases released
  exact retained

def rejectingOwner : ConstructorIndex where
  Aux := Nat
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := []
  ownerAt := fun _ _ => .zero
  owner := fun _ _ _ => False
  checkOwner := Callback.ofFunction (fun state _ =>
    .returned (.error callbackError) (state.1, state.2 + 7))
  deserialize := fun _ _ _ => False

/-- the error and state of CheckOwner are forwarded. No Owner callback or codec
execution is needed or admitted on this branch. -/
theorem interface_check_owner_error :
    construct .interfaceAccount rejectingOwner (AccountInfo.sampleState, (0 : Nat))
      AccountInfo.sampleArgs (.returned (.error callbackError) (sampleAfterInit, (7 : Nat))) := by
  refine ⟨.returned (.ok ()) (sampleAfterInit, (0 : Nat)), rfl, ?_⟩
  exact ⟨.returned (.error callbackError) (sampleAfterInit, (7 : Nat)),
    ⟨.returned (.error callbackError) (sampleAfterInit, (7 : Nat)), rfl, rfl⟩, rfl⟩

/-- The actual post-state of AsRef is preserved when ToAccountInfo clones its alias. -/
theorem to_info_preserves_callback_effect :
    toInfoRun toInfoSample (4 : Nat) () (.returned AccountInfo.sampleInfo (5 : Nat)) :=
  ⟨.returned AccountInfo.sampleInfo (5 : Nat), rfl, rfl⟩

/-- Anchor forwards nested binary fields without flattening their boundaries. -/
theorem log_preserves_fields :
    AnchorLog.run AnchorLog.sample ([] : List Log.Event) [[], [1, 2], []]
      (.returned () ([.data [[], [1, 2], []]] : List Log.Event)) := rfl

/-- the host branch of Anchor is black_box, not a host logging stub. Even an empty
sink relation cannot prevent this state-preserving return. -/
theorem log_host_calls_no_sink :
    AnchorLog.run ⟨Nat, String, String, .host, fun _ _ _ => False⟩
      (7 : Nat) [[1, 2], []] (.returned () (7 : Nat)) := rfl

end SolanalibTest.Specs.AnchorLang.Accounts

namespace SolanalibTest.Specs.AnchorLang.Accounts.LifecycleBuilds

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 4096

abbrev Key := AnchorLang.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Resolved facts for the retained 0.32.1 reference, not a source-body proof. -/
def selectedBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.32.1"
  source := registry
  dependencies :=
    [⟨"solana-account-info", "2.3.0", registry⟩,
      ⟨"solana-program-error", "2.2.2", registry⟩]

def members : List Key :=
  [.AccountsExit_exit,
    .accounts_account_Account_close,
    .accounts_account_Account_exit,
    .accounts_account_Account_try_accounts,
    .accounts_account_Account_try_from_unchecked,
    .accounts_account_info_AccountInfo_try_accounts,
    .accounts_boxed_Box_close,
    .accounts_boxed_Box_exit,
    .accounts_boxed_Box_try_accounts,
    .accounts_option_Option_exit,
    .accounts_option_Option_try_accounts,
    .accounts_program_Program_try_accounts,
    .accounts_signer_Signer_try_accounts]

/-- Both literal lifetime spellings remain distinct registered aliases. -/
def expectedAliases : Key → List (String × String)
  | .AccountsExit_exit =>
    [("anchor_lang::AccountsExit::exit",
        "anchor_lang::AccountsExit::exit")]
  | .accounts_account_Account_close =>
    [("anchor_lang::AccountsClose::close",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsClose<'info>>::close"),
      ("anchor_lang::AccountsClose::close",
        "<anchor_lang::accounts::account::Account<'_, T> as \
          anchor_lang::AccountsClose<'_>>::close")]
  | .accounts_account_Account_exit =>
    [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"),
      ("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account::Account<'_, T> as \
          anchor_lang::AccountsExit<'_>>::exit")]
  | .accounts_account_Account_try_accounts =>
    [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
      ("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account::Account<'_, T> as anchor_lang::Accounts<'_, \
          B>>::try_accounts")]
  | .accounts_account_Account_try_from_unchecked =>
    [("anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"),
      ("anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked")]
  | .accounts_account_info_AccountInfo_try_accounts =>
    [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info, B> for \
          solana_account_info::AccountInfo<'info>>::try_accounts"),
      ("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'_, B> for \
          solana_account_info::AccountInfo<'_>>::try_accounts")]
  | .accounts_boxed_Box_close =>
    [("anchor_lang::AccountsClose::close",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsClose<'info> for \
          alloc::boxed::Box<T>>::close"),
      ("anchor_lang::AccountsClose::close",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsClose<'_> for \
          alloc::boxed::Box<T>>::close")]
  | .accounts_boxed_Box_exit =>
    [("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
          alloc::boxed::Box<T>>::exit"),
      ("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
          alloc::boxed::Box<T>>::exit")]
  | .accounts_boxed_Box_try_accounts =>
    [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
          alloc::boxed::Box<T>>::try_accounts"),
      ("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'_, B> for \
          alloc::boxed::Box<T>>::try_accounts")]
  | .accounts_option_Option_exit =>
    [("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
          core::option::Option<T>>::exit"),
      ("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'_> for \
          core::option::Option<T>>::exit")]
  | .accounts_option_Option_try_accounts =>
    [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
          core::option::Option<T>>::try_accounts"),
      ("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'_, B> for \
          core::option::Option<T>>::try_accounts")]
  | .accounts_program_Program_try_accounts =>
    [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
      ("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Accounts<'_, \
          B>>::try_accounts")]
  | .accounts_signer_Signer_try_accounts =>
    [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
          B>>::try_accounts"),
      ("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Accounts<'_, \
          B>>::try_accounts")]
  | _ => []

def expectedIdentities (version : String) (key : Key) :
    List Capabilities.RustIdentity :=
  (expectedAliases key).map fun (item, implementation) =>
    ⟨"anchor-lang", version, item, implementation⟩

def identitiesMatch (keys : List Key) (build : Versioning.Build) : Bool :=
  keys.all fun key =>
    decide ((AnchorLang.Capabilities.catalog.forBuild build).identities key =
      expectedIdentities build.version key)

def identitiesAbsent (keys : List Key) (build : Versioning.Build) : Bool :=
  keys.all fun key =>
    ((AnchorLang.Capabilities.catalog.forBuild build).identities key).isEmpty

def inspectedReleases : List String := ["0.32.0", "0.32.1", "0.32.2", "0.32.3"]

/-- These versions exercise declared compatibility; they add no source or
native evidence for a release that was not inspected. -/
def compatibleReleases : List String := ["0.32.4", "0.32.99", "0.32.4+fixture.1"]

theorem selected_member_and_alias_counts :
    members.length = 13 ∧ members.Nodup ∧
      ((members.map expectedAliases).map List.length).sum = 25 := by
  decide +kernel

/-- Select the original compact profile and its two normalized lifetime aliases.
The explicit IDs keep later reference profiles outside these assertions. -/
def referenceProfiles (key : Key) : List Versioning.Profile :=
  (AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
    ["anchor-lifecycle-0.32.1", "anchor-lifecycle-0.32.1:0",
      "anchor-lifecycle-0.32.1:1"].contains profile.id)

/-- A matching interval must not hide an omitted inspected reference. -/
theorem inspected_reference_sets :
    members.all (fun key =>
      let profiles := referenceProfiles key
      !profiles.isEmpty &&
        profiles.all (fun profile => decide (profile.releases = inspectedReleases ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩]))) = true := by
  decide +kernel

theorem inspected_releases_keep_actual_identities :
    inspectedReleases.all (fun version =>
      identitiesMatch members { selectedBuild with version := version }) = true := by
  decide +kernel

/-- In-range selection returns the actual resolved version, including build
metadata, rather than rewriting it to the 0.32.1 native reference. -/
theorem compatible_patches_keep_actual_identities :
    compatibleReleases.all (fun version =>
      identitiesMatch members { selectedBuild with version := version }) = true := by
  decide +kernel

theorem outside_minor_line_and_prereleases_rejected :
    let referenceCatalog : Capabilities.Catalog :=
      { AnchorLang.Capabilities.catalog with applicability := referenceProfiles }
    members.all (fun key => !(referenceCatalog.applicability key).isEmpty) = true ∧
    ["0.27.0", "0.29.0", "0.31.3", "0.31.99", "0.33.0",
      "1.0.2", "1.2.2", "0.32.0-rc.1", "0.32.4-rc.1",
      "0.33.0+fixture.1"].all (fun version =>
        members.all (fun key =>
          ((referenceCatalog.forBuild { selectedBuild with version := version }).identities
            key).isEmpty)) = true := by
  decide +kernel

/-- The old reference profiles reject 1.1.2, independently of later profiles. -/
theorem original_profiles_reject_modern_release :
    members.all (fun key =>
      let profiles := referenceProfiles key
      !profiles.isEmpty && profiles.all (fun profile =>
        !(profile.matches { selectedBuild with version := "1.1.2" }))) = true := by
  decide +kernel

/-- With the old provider fixture, only the two dependency-free modern operations
are eligible; the others still require their own modern provider facts. -/
theorem modern_release_preserves_provider_requirements :
    members.filter (fun key =>
      !((AnchorLang.Capabilities.catalog.forBuild
        { selectedBuild with version := "1.1.2" }).identities key).isEmpty) =
        [.AccountsExit_exit, .accounts_boxed_Box_exit] ∧
      identitiesMatch [.AccountsExit_exit, .accounts_boxed_Box_exit]
        { selectedBuild with version := "1.1.2" } = true := by
  constructor
  · rfl
  · decide +kernel

def otherOrigins : List Versioning.Source :=
  [⟨"git", "https://example.invalid/anchor-lang", "0123456789abcdef0123456789abcdef01234567"⟩,
    ⟨"registry", "https://example.invalid/index", ""⟩]

theorem defining_forks_and_other_registries_rejected :
    ["0.32.1", "0.32.4"].all (fun version => otherOrigins.all (fun source =>
      identitiesAbsent members
        { selectedBuild with version := version, source := source })) = true := by
  decide +kernel

theorem other_defining_package_rejected :
    identitiesAbsent members
      { selectedBuild with package := "anchor-spl" } = true := by
  decide +kernel

/-- These four methods do not call resize. Close is tested separately. -/
def nonResizeMembers : List Key :=
  [.accounts_account_Account_exit, .accounts_account_Account_try_accounts,
    .accounts_account_Account_try_from_unchecked,
    .accounts_account_info_AccountInfo_try_accounts]

def providerMembers : List Key := .accounts_account_Account_close :: nonResizeMembers

def independentMembers : List Key :=
  [.AccountsExit_exit, .accounts_boxed_Box_close, .accounts_boxed_Box_exit,
    .accounts_boxed_Box_try_accounts, .accounts_option_Option_exit,
    .accounts_option_Option_try_accounts, .accounts_program_Program_try_accounts,
    .accounts_signer_Signer_try_accounts]

def accountInfoReferences : List String :=
  ["2.1.0", "2.1.1", "2.1.2", "2.1.4",
    "2.1.5", "2.1.6", "2.1.7", "2.1.8",
    "2.1.9", "2.1.10", "2.1.11", "2.1.12",
    "2.1.13", "2.1.14", "2.1.15", "2.1.16",
    "2.1.17", "2.1.18", "2.1.20", "2.1.21",
    "2.2.0", "2.2.1", "2.3.0"]

def programErrorReferences : List String :=
  ["2.1.0", "2.1.1", "2.1.2", "2.1.4",
    "2.1.5", "2.1.6", "2.1.7", "2.1.8",
    "2.1.9", "2.1.10", "2.1.11", "2.1.12",
    "2.1.13", "2.1.14", "2.1.15", "2.1.16",
    "2.1.17", "2.1.18", "2.1.20", "2.1.21",
    "2.2.0", "2.2.1", "2.2.2"]

def dependencyBuild (package version : String) : Versioning.Build :=
  { selectedBuild with
    dependencies := selectedBuild.dependencies.map fun dependency =>
      if dependency.package == package then { dependency with version := version }
      else dependency }

def withDependencySource (build : Versioning.Build) (package : String)
    (source : Versioning.Source) : Versioning.Build :=
  { build with
    dependencies := build.dependencies.map fun dependency =>
      if dependency.package == package then { dependency with source := source }
      else dependency }

def requirementShape (requirement : Versioning.DependencyRequirement)
    (package : String) (references : List String) (lower : String) : Bool :=
  decide (requirement.package = package ∧ requirement.source = some registry ∧
    requirement.releases = references ∧
    requirement.compatibleRanges = [⟨lower, "3.0.0"⟩])

def providerShape (profile : Versioning.Profile)
    (infoReferences : List String) (infoLower : String) : Bool :=
  match profile.dependencies with
  | [info, error] =>
    requirementShape info "solana-account-info" infoReferences infoLower &&
      requirementShape error "solana-program-error" programErrorReferences "2.1.0"
  | _ => false

/-- The two provider requirements retain their own references, origins and
bounds. The other eight functions acquire no unused dependency requirement. -/
theorem dependency_shapes_are_per_operation :
    (let profiles := referenceProfiles .accounts_account_Account_close
     !profiles.isEmpty &&
       profiles.all (fun profile => providerShape profile ["2.3.0"] "2.3.0")) = true ∧
    nonResizeMembers.all (fun key =>
      let profiles := referenceProfiles key
      !profiles.isEmpty &&
        profiles.all (fun profile => providerShape profile accountInfoReferences "2.1.0")) = true ∧
    independentMembers.all (fun key =>
      let profiles := referenceProfiles key
      !profiles.isEmpty &&
        profiles.all (fun profile => profile.dependencies.isEmpty)) = true := by
  decide +kernel

theorem all_inspected_account_info_dependencies :
    accountInfoReferences.all (fun version =>
      identitiesMatch nonResizeMembers (dependencyBuild "solana-account-info" version)) = true := by
  decide +kernel

theorem all_inspected_program_error_dependencies :
    programErrorReferences.all (fun version =>
      identitiesMatch providerMembers (dependencyBuild "solana-program-error" version)) = true := by
  decide +kernel

theorem compatible_provider_patches :
    ["2.3.0", "2.4.0", "2.99.0", "2.4.0+fixture.1"].all (fun version =>
      identitiesMatch providerMembers (dependencyBuild "solana-account-info" version) &&
      identitiesMatch providerMembers (dependencyBuild "solana-program-error" version)) = true ∧
    identitiesMatch providerMembers
      { selectedBuild with
        version := "0.32.4"
        dependencies :=
          [⟨"solana-account-info", "2.4.0", registry⟩,
            ⟨"solana-program-error", "2.4.0", registry⟩] } = true := by
  decide +kernel

/-- Resize is absent in the inspected 2.1/2.2 AccountInfo releases, while the
other four profiles remain eligible with those providers. -/
theorem close_requires_resize_but_other_methods_do_not :
    (accountInfoReferences.filter (fun version => version != "2.3.0")).all (fun version =>
      identitiesAbsent [.accounts_account_Account_close]
        (dependencyBuild "solana-account-info" version) &&
      identitiesMatch nonResizeMembers
        (dependencyBuild "solana-account-info" version)) = true ∧
    identitiesMatch [.accounts_account_Account_close]
      (dependencyBuild "solana-account-info" "2.3.0") = true := by
  decide +kernel

theorem account_info_lower_upper_and_prerelease_bounds :
    ["2.0.99", "3.0.0", "3.0.0+fixture.1", "2.3.0-rc.1"].all (fun version =>
      identitiesAbsent providerMembers (dependencyBuild "solana-account-info" version)) = true := by
  decide +kernel

/-- ProgramError 3 changes the owned BorshIoError payload; a shared numeric
error tag does not admit that different provider domain. -/
theorem program_error_lower_upper_and_prerelease_bounds :
    ["2.0.99", "3.0.0", "3.0.0+fixture.1", "2.2.2-rc.1"].all (fun version =>
      identitiesAbsent providerMembers (dependencyBuild "solana-program-error" version)) = true :=
        by
  decide +kernel

def providerPackages : List String := ["solana-account-info", "solana-program-error"]

def withoutProvider (package : String) : Versioning.Build :=
  { selectedBuild with
    dependencies := selectedBuild.dependencies.filter
      (fun dependency => dependency.package != package) }

theorem missing_required_dependencies_rejected :
    providerPackages.all (fun package =>
      decide ((withoutProvider package).dependency package = none) &&
      identitiesAbsent providerMembers (withoutProvider package)) = true := by
  decide +kernel

/-- Duplicate equal entries, two compatible versions, and a registry/fork
pair are all ambiguous actual dependency facts. -/
def ambiguousBuilds (package : String) : List Versioning.Build :=
  [{ selectedBuild with
      dependencies := selectedBuild.dependencies ++
        selectedBuild.dependencies.filter (fun dependency => dependency.package == package) },
    { selectedBuild with
      dependencies := selectedBuild.dependencies ++ [⟨package, "2.4.0", registry⟩] },
    { selectedBuild with
      dependencies := selectedBuild.dependencies ++
        [⟨package, "2.4.0",
          ⟨"git", "https://example.invalid/solana-sdk",
            "0123456789abcdef0123456789abcdef01234567"⟩⟩] }]

theorem ambiguous_required_dependencies_rejected :
    providerPackages.all (fun package => (ambiguousBuilds package).all (fun build =>
      decide (build.dependency package = none) &&
      identitiesAbsent providerMembers build)) = true := by
  decide +kernel

theorem dependency_forks_and_other_registries_rejected :
    providerPackages.all (fun package => otherOrigins.all (fun source =>
      identitiesAbsent providerMembers (withDependencySource selectedBuild package source) &&
      identitiesAbsent providerMembers
        (withDependencySource (dependencyBuild package "2.4.0") package source))) = true := by
  decide +kernel

theorem no_unused_dependency_gate :
    identitiesMatch independentMembers { selectedBuild with dependencies := [] } = true ∧
    providerPackages.all (fun package => (ambiguousBuilds package).all (fun build =>
      identitiesMatch independentMembers build)) = true ∧
    providerPackages.all (fun package => otherOrigins.all (fun source =>
      identitiesMatch independentMembers
        (withDependencySource (dependencyBuild package "3.0.0") package source))) = true := by
  decide +kernel

/-- Metadata eligibility preserves both optional-account feature indices.
The source binding must still supply the cfg value of the actual defining crate. -/
theorem no_blanket_optional_or_debug_feature_filter :
    ([none, some [], some ["allow-missing-optionals"], some ["anchor-debug"],
      some ["allow-missing-optionals", "anchor-debug"]] : List (Option (List String))).all
      (fun features => identitiesMatch members
        { selectedBuild with features := features }) = true := by
  decide +kernel

/-- Host-unwind recordings and target/abort source interpretations are
separate. Catalog selection alone discharges neither layout nor panic binding. -/
theorem target_and_panic_remain_interpretation_obligations :
    ([[],
      [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩, ⟨"panic", "unwind"⟩],
      [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"panic", "abort"⟩]] :
        List (List Versioning.TargetFact)).all (fun target =>
      identitiesMatch members { selectedBuild with target := target }) = true ∧
    ([none, some []] : List (Option (List String))).all (fun targetFeatures =>
      identitiesMatch members { selectedBuild with targetFeatures := targetFeatures }) = true := by
  decide +kernel

/-- Selection retains the complete receiver-specific family. In particular,
close stays cloning/legacy, Account exit stays noncloning, and constructors
stay borrowed/boxed; existing contract scenario proofs remain applicable. -/
theorem fixed_lifecycle_families (build : Versioning.Build) :
    (AnchorLang.Capabilities.catalog.forBuild build).family .AccountsExit_exit =
      AnchorLang.AccountsExit.exit_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_account_Account_close =
      AnchorLang.accounts.account.Account.close_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_account_Account_exit =
      AnchorLang.accounts.account.Account.exit_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_account_Account_try_accounts =
      AnchorLang.accounts.account.Account.try_accounts_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_account_Account_try_from_unchecked =
      AnchorLang.accounts.account.Account.try_from_unchecked_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_account_info_AccountInfo_try_accounts =
      AnchorLang.accounts.account_info.AccountInfo.try_accounts_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_boxed_Box_close =
      AnchorLang.accounts.boxed.Box.close_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_boxed_Box_exit =
      AnchorLang.accounts.boxed.Box.exit_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_boxed_Box_try_accounts =
      AnchorLang.accounts.boxed.Box.try_accounts_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_option_Option_exit =
      AnchorLang.accounts.option.Option.exit_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_option_Option_try_accounts =
      AnchorLang.accounts.option.Option.try_accounts_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_program_Program_try_accounts =
      AnchorLang.accounts.program.Program.try_accounts_contract ∧
    (AnchorLang.Capabilities.catalog.forBuild build).family
      .accounts_signer_Signer_try_accounts =
      AnchorLang.accounts.signer.Signer.try_accounts_contract :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SolanalibTest.Specs.AnchorLang.Accounts.LifecycleBuilds

namespace SolanalibTest.Specs.AnchorLang.Accounts.ReloadProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := AnchorLang.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_Account_reload,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry,
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
          "2.2.0", registry⟩] },
      [("anchor_lang::accounts::account::Account::<'a, T>::reload",
        "anchor_lang::accounts::account::Account::<'a, T>::reload"),
        ("anchor_lang::accounts::account::Account::<'_, T>::reload",
          "anchor_lang::accounts::account::Account::<'_, T>::reload")]),
    (.accounts_interface_Interface_try_accounts,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface::Interface<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
        ("anchor_lang::Accounts::try_accounts",
          "<anchor_lang::accounts::interface::Interface<'_, T> as \
            anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_interface_account_InterfaceAccount_exit,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry,
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
          "2.2.0", registry⟩] },
      [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"),
        ("anchor_lang::AccountsExit::exit",
          "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
            anchor_lang::AccountsExit<'_>>::exit")]),
    (.accounts_interface_account_InterfaceAccount_reload,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry,
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
          "2.2.0", registry⟩] },
      [("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::reload",
        "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::reload"),
        ("anchor_lang::accounts::interface_account::InterfaceAccount::<'_, T>::reload",
          "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, T>::reload")]),
    (.accounts_interface_account_InterfaceAccount_try_accounts,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry,
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
          "2.2.0", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
        ("anchor_lang::Accounts::try_accounts",
          "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
            anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_sysvar_Sysvar_try_accounts,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry,
        dependencies := [⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
          "2.2.0", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as anchor_lang::Accounts<'info, \
          B>>::try_accounts"),
        ("anchor_lang::Accounts::try_accounts",
          "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Accounts<'_, \
            B>>::try_accounts")]),
    (.accounts_unchecked_account_UncheckedAccount_try_accounts,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"),
        ("anchor_lang::Accounts::try_accounts",
          "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
            anchor_lang::Accounts<'_, B>>::try_accounts")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((AnchorLang.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"anchor-lang", build.version, item, implementation⟩))

def members : List Key := [.accounts_account_Account_reload,
  .accounts_interface_Interface_try_accounts, .accounts_interface_account_InterfaceAccount_exit,
  .accounts_interface_account_InterfaceAccount_reload,
  .accounts_interface_account_InterfaceAccount_try_accounts, .accounts_sysvar_Sysvar_try_accounts,
  .accounts_unchecked_account_UncheckedAccount_try_accounts]

theorem every_member_has_a_literal_case :
    members.length = 7 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3"].all (fun version => fixtures.all (fun (key, build,
      expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.32.4", "0.32.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    let referenceCatalog : Capabilities.Catalog :=
      { AnchorLang.Capabilities.catalog with
        applicability := fun key =>
          (AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
            ["anchor-lifecycle-0.32.1:0", "anchor-lifecycle-0.32.1:1"].contains profile.id) }
    members.all (fun key => !(referenceCatalog.applicability key).isEmpty) = true ∧
    ["0.31.99", "0.33.0", "1.0.2", "0.32.4-rc.1"].all (fun version => fixtures.all (fun (key,
      build, _) =>
      ((referenceCatalog.forBuild { build with version := version }).identities key).isEmpty)) =
        true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      let profiles := (AnchorLang.Capabilities.catalog.applicability key).filter
        (fun profile =>
          ["anchor-lifecycle-0.32.1:0", "anchor-lifecycle-0.32.1:1"].contains profile.id)
      !profiles.isEmpty &&
      profiles.all (fun profile =>
        decide (profile.releases = ["0.32.0", "0.32.1", "0.32.2", "0.32.3"] ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

/-- Each required edge is checked independently. Duplicate compatible
candidates remain ambiguous actual dependency facts. -/
theorem dependency_facts_cannot_be_missing_wrong_or_ambiguous :
    fixtures.all (fun (key, build, _) => build.dependencies.all (fun required =>
      identitiesMatch key { build with dependencies := (build.dependencies.filter
        (fun dependency => dependency.package != required.package)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with version := "99.0.0" } else dependency)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with source :=
            ⟨"git", "https://example.invalid/dependency", "01234567890123456789012345678901\
              23456789"⟩ }
          else dependency)) } [] &&
      identitiesMatch key { build with dependencies := build.dependencies ++ [required] } [])) =
        true := by
  decide +kernel

/-- Provider references and compatible fixtures preserve the actual
identity of the caller; the provider version is not substituted for the defining crate. -/
theorem dependency_references_and_compatible_versions :
    ([("solana-account-info", ["2.3.0", "2.9.99", "2.9.99+fixture"]),
      ("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.9.99", "2.9.99+fixture"])] : List
        (String × List String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, expected) => versions.all (fun version =>
        identitiesMatch key { build with dependencies := (build.dependencies.map
          (fun dependency => if dependency.package == package then
            { dependency with version := version } else dependency)) } expected))) = true := by
  decide +kernel

/-- In particular, the unit BorshIoError of ProgramError 3 cannot replace the
selected owned String carrier. Other rows enforce their declared bounds. -/
theorem dependency_bounds_retain_the_selected_domains :
    ([("solana-account-info", ["2.2.1", "3.0.0", "2.3.0-rc.1"]),
      ("solana-program-error", ["2.1.0", "3.0.0", "2.2.2-rc.1"])] : List (String × List
        String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, _) => if (build.dependency package).isSome then
        versions.all (fun version => identitiesMatch key
          { build with dependencies := (build.dependencies.map (fun dependency =>
            if dependency.package == package then { dependency with version := version }
            else dependency)) } []) else true)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.Accounts.ReloadProfiles

@[expose] public section

namespace SolanalibTest.Specs.AnchorLang.V1_0_2Accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { AnchorLang.Capabilities.catalog with applicability := fun key =>
      (AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id || (id ++ ":").toList.isPrefixOf profile.id.toList) }

def build0 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build0 with version := version }).identities
          .accounts_system_account_SystemAccount_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::system_account::SystemAccount<'_> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all
                (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build0).identities .accounts_system_account_SystemAccount_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_system_account_SystemAccount_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build0 with version := version
        }).identities
        .accounts_system_account_SystemAccount_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-lang-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_system_account_SystemAccount_try_accounts).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build1 with version := version }).identities .AccountsExit_exit =
          [⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "anchor_lang::AccountsExit::exit"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "anchor_lang::AccountsExit::exit"⟩] : List Capabilities.RustIdentity).all (fun identity
              =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build1).identities .AccountsExit_exit)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability .AccountsExit_exit).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build1 with version := version
        }).identities
        .AccountsExit_exit).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "anchor-lang-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .AccountsExit_exit).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build2 with version := version }).identities .accounts_boxed_Box_exit =
          [⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
              alloc::boxed::Box<T>>::exit"⟩,
          ⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
              alloc::boxed::Box<T>>::exit"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
              alloc::boxed::Box<T>>::exit"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
              alloc::boxed::Box<T>>::exit"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build2).identities .accounts_boxed_Box_exit)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability .accounts_boxed_Box_exit).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build2 with version := version
        }).identities
        .accounts_boxed_Box_exit).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "anchor-lang-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_boxed_Box_exit).isEmpty) = true := by
  decide +kernel

def build3 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile3_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build3 with version := version }).identities .accounts_boxed_Box_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
              alloc::boxed::Box<T>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'_, B> for \
              alloc::boxed::Box<T>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile3_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
              alloc::boxed::Box<T>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'_, B> for \
              alloc::boxed::Box<T>>::try_accounts"⟩] : List Capabilities.RustIdentity).all (fun
                identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build3).identities .accounts_boxed_Box_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile3_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_boxed_Box_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build3 with version := version
        }).identities
        .accounts_boxed_Box_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile3_build_rejections :
    ([{ build3 with package := "anchor-lang-other" },
      { build3 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build3 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_boxed_Box_try_accounts).isEmpty) = true := by
  decide +kernel

def build4 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile4_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build4 with version := version }).identities .accounts_interface_Interface_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface::Interface<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface::Interface<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile4_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface::Interface<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface::Interface<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all
                (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build4).identities .accounts_interface_Interface_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile4_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_interface_Interface_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build4 with version := version
        }).identities
        .accounts_interface_Interface_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile4_build_rejections :
    ([{ build4 with package := "anchor-lang-other" },
      { build4 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build4 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_interface_Interface_try_accounts).isEmpty) = true := by
  decide +kernel

def build5 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile5_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build5 with version := version }).identities
          .accounts_interface_account_InterfaceAccount_exit =
          [⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              anchor_lang::AccountsExit<'info>>::exit"⟩,
          ⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              anchor_lang::AccountsExit<'_>>::exit"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile5_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              anchor_lang::AccountsExit<'info>>::exit"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              anchor_lang::AccountsExit<'_>>::exit"⟩] : List Capabilities.RustIdentity).all (fun
                identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build5).identities .accounts_interface_account_InterfaceAccount_exit)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile5_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_interface_account_InterfaceAccount_exit).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build5 with version := version
        }).identities
        .accounts_interface_account_InterfaceAccount_exit).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile5_build_rejections :
    ([{ build5 with package := "anchor-lang-other" },
      { build5 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build5 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build5 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_interface_account_InterfaceAccount_exit).isEmpty) = true := by
  decide +kernel

def build6 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile6_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build6 with version := version }).identities
          .accounts_interface_account_InterfaceAccount_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile6_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all
                (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build6).identities .accounts_interface_account_InterfaceAccount_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile6_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_interface_account_InterfaceAccount_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build6 with version := version
        }).identities
        .accounts_interface_account_InterfaceAccount_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile6_build_rejections :
    ([{ build6 with package := "anchor-lang-other" },
      { build6 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build6 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build6 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_interface_account_InterfaceAccount_try_accounts).isEmpty) = true := by
  decide +kernel

def build7 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile7_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build7 with version := version }).identities
          .accounts_interface_account_InterfaceAccount_try_from_unchecked =
          [⟨"anchor-lang", version,
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
              T>::try_from_unchecked",
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
              T>::try_from_unchecked"⟩,
          ⟨"anchor-lang", version,
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, \
              T>::try_from_unchecked",
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, \
              T>::try_from_unchecked"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile7_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2",
      "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
        T>::try_from_unchecked",
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'a, \
              T>::try_from_unchecked"⟩,
          ⟨"anchor-lang", "1.0.2",
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, \
              T>::try_from_unchecked",
            "anchor_lang::accounts::interface_account::InterfaceAccount::<'_, \
              T>::try_from_unchecked"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build7).identities .accounts_interface_account_InterfaceAccount_try_from_unchecked)) = true
        := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile7_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_interface_account_InterfaceAccount_try_from_unchecked).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build7 with version := version
        }).identities
        .accounts_interface_account_InterfaceAccount_try_from_unchecked).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile7_build_rejections :
    ([{ build7 with package := "anchor-lang-other" },
      { build7 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build7 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build7 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build7 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_interface_account_InterfaceAccount_try_from_unchecked).isEmpty) = true := by
  decide +kernel

def build8 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile8_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build8 with version := version }).identities .accounts_option_Option_exit =
          [⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
              core::option::Option<T>>::exit"⟩,
          ⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'_> for \
              core::option::Option<T>>::exit"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile8_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
              core::option::Option<T>>::exit"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsExit::exit",
            "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'_> for \
              core::option::Option<T>>::exit"⟩] : List Capabilities.RustIdentity).all (fun identity
                =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build8).identities .accounts_option_Option_exit)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile8_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability .accounts_option_Option_exit).length
      = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build8 with version := version
        }).identities
        .accounts_option_Option_exit).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile8_build_rejections :
    ([{ build8 with package := "anchor-lang-other" },
      { build8 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build8 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_option_Option_exit).isEmpty) = true := by
  decide +kernel

def build9 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile9_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build9 with version := version }).identities .accounts_option_Option_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
              core::option::Option<T>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'_, B> for \
              core::option::Option<T>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile9_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
              core::option::Option<T>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'_, B> for \
              core::option::Option<T>>::try_accounts"⟩] : List Capabilities.RustIdentity).all (fun
                identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build9).identities .accounts_option_Option_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile9_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_option_Option_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build9 with version := version
        }).identities
        .accounts_option_Option_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile9_build_rejections :
    ([{ build9 with package := "anchor-lang-other" },
      { build9 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build9 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_option_Option_try_accounts).isEmpty) = true := by
  decide +kernel

def build10 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile10_literal_identities :
    ["1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build10 with version := version }).identities .accounts_program_Program_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::program::Program<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Accounts<'_, \
              B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile10_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::program::Program<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Accounts<'_, \
              B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build10).identities .accounts_program_Program_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile10_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_program_Program_try_accounts).length = 2 ∧
    ["1.0.0", "1.0.1", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build10 with version := version
        }).identities
        .accounts_program_Program_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile10_build_rejections :
    ([{ build10 with package := "anchor-lang-other" },
      { build10 with source := ⟨"git", "https://example.invalid/repository", "0123456789abc\
        def0123456789abcdef01234567"⟩ },
      { build10 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_program_Program_try_accounts).isEmpty) = true := by
  decide +kernel

def build11 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile11_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build11 with version := version }).identities .accounts_signer_Signer_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
              B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Accounts<'_, \
              B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile11_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
              B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Accounts<'_, \
              B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build11).identities .accounts_signer_Signer_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile11_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_signer_Signer_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build11 with version := version
        }).identities
        .accounts_signer_Signer_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile11_build_rejections :
    ([{ build11 with package := "anchor-lang-other" },
      { build11 with source := ⟨"git", "https://example.invalid/repository", "0123456789abc\
        def0123456789abcdef01234567"⟩ },
      { build11 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_signer_Signer_try_accounts).isEmpty) = true := by
  decide +kernel

def build12 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile12_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build12 with version := version }).identities .accounts_sysvar_Sysvar_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Accounts<'_, \
              B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile12_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Accounts<'_, \
              B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build12).identities .accounts_sysvar_Sysvar_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile12_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_sysvar_Sysvar_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build12 with version := version
        }).identities
        .accounts_sysvar_Sysvar_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile12_build_rejections :
    ([{ build12 with package := "anchor-lang-other" },
      { build12 with source := ⟨"git", "https://example.invalid/repository", "0123456789abc\
        def0123456789abcdef01234567"⟩ },
      { build12 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build12 with dependencies := [⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build12 with dependencies := [⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_sysvar_Sysvar_try_accounts).isEmpty) = true := by
  decide +kernel

def build13 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile13_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build13 with version := version }).identities
          .accounts_unchecked_account_UncheckedAccount_try_accounts =
          [⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", version, "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile13_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
              anchor_lang::Accounts<'info, B>>::try_accounts"⟩,
          ⟨"anchor-lang", "1.0.2", "anchor_lang::Accounts::try_accounts",
            "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
              anchor_lang::Accounts<'_, B>>::try_accounts"⟩] : List Capabilities.RustIdentity).all
                (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build13).identities .accounts_unchecked_account_UncheckedAccount_try_accounts)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile13_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_unchecked_account_UncheckedAccount_try_accounts).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build13 with version := version
        }).identities
        .accounts_unchecked_account_UncheckedAccount_try_accounts).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile13_build_rejections :
    ([{ build13 with package := "anchor-lang-other" },
      { build13 with source := ⟨"git", "https://example.invalid/repository", "0123456789abc\
        def0123456789abcdef01234567"⟩ },
      { build13 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_unchecked_account_UncheckedAccount_try_accounts).isEmpty) = true := by
  decide +kernel

def build14 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile14_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-lifecycle-1.0.2").forBuild
        { build14 with version := version }).identities
          .accounts_unchecked_account_UncheckedAccount_try_from =
          [⟨"anchor-lang", version,
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from",
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from"⟩,
          ⟨"anchor-lang", version,
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from",
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from"⟩])) = true
              := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile14_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2",
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from",
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from"⟩,
          ⟨"anchor-lang", "1.0.2",
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from",
            "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (AnchorLang.Capabilities.catalog.forBuild
        build14).identities .accounts_unchecked_account_UncheckedAccount_try_from)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile14_range_rejections :
    ((selectedProfile "anchor-lifecycle-1.0.2").applicability
      .accounts_unchecked_account_UncheckedAccount_try_from).length = 2 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-lifecycle-1.0.2").forBuild { build14 with version := version
        }).identities
        .accounts_unchecked_account_UncheckedAccount_try_from).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile14_build_rejections :
    ([{ build14 with package := "anchor-lang-other" },
      { build14 with source := ⟨"git", "https://example.invalid/repository", "0123456789abc\
        def0123456789abcdef01234567"⟩ },
      { build14 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => ((AnchorLang.Capabilities.catalog.forBuild build).identities
        .accounts_unchecked_account_UncheckedAccount_try_from).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.V1_0_2Accounts

namespace SolanalibTest.Specs.AnchorLang.LegacyAccountCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorLang.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_Account_exit_cloned_info, {
    package := "anchor-lang", version := "0.2\
    9.0",
    source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"), ("anchor_lang::AccountsExit::exit", "<\
            anchor_lang::accounts::account::Account<'_, T> as \
            anchor_lang::AccountsExit<'_>>::exit")]),
    (.accounts_interface_account_InterfaceAccount_exit_cloned_info, {
      package := "anchor-la\
      ng",
      version := "0.29.0", source := registry, dependencies := [⟨"solana-program", "1.18.26",
      registry⟩] },
      [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"), ("anchor_lang::AccountsExit::exit", "<\
            anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
            anchor_lang::AccountsExit<'_>>::exit")]),
    (.accounts_program_Program_try_from, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry },
      [("core::convert::TryFrom::try_from",
        "<anchor_lang::accounts::program::Program<'a, T> as core::convert::TryFrom<&'a \
          solana_program::account_info::AccountInfo<'a>>>::try_from"), ("core::convert::Try\
            From::try_from", "<anchor_lang::accounts::program::Program<'_, T> as \
              core::convert::TryFrom<&'_ \
              solana_program::account_info::AccountInfo<'_>>>::try_from")]),
    (.accounts_signer_Signer_try_from, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry },
      [("anchor_lang::accounts::signer::Signer::<'info>::try_from",
        "anchor_lang::accounts::signer::Signer::<'info>::try_from"),
        ("anchor_lang::accounts::signer::Signer::<'_>::try_from",
        "anchor_lang::accounts::signer::Signer::<'_>::try_from")]),
    (.AccountsExit_exit, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      [("anchor_lang::AccountsExit::exit", "anchor_lang::AccountsExit::exit")]),
    (.accounts_account_Account_close, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::AccountsClose::close",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsClose<'info>>::close"), ("anchor_lang::AccountsClose::close",
            "<anchor_lang::accounts::account::Account<'_, T> as \
              anchor_lang::AccountsClose<'_>>::close")]),
    (.accounts_account_Account_try_accounts, {
      package := "anchor-lang", version := "0.29.0",
      source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"), ("anchor_lang::Accounts::try_ac\
            counts", "<anchor_lang::accounts::account::Account<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_account_Account_try_from_unchecked, {
      package := "anchor-lang", version := "0.29.0",
      source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"),
        ("anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked")]),
    (.accounts_account_info_AccountInfo_try_accounts, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info, B> for \
          solana_program::account_info::AccountInfo<'info>>::try_accounts"), ("anchor_lang:\
            :Accounts::try_accounts", "anchor_lang::accounts::account_info::<impl \
              anchor_lang::Accounts<'_, B> for \
              solana_program::account_info::AccountInfo<'_>>::try_accounts")]),
    (.accounts_boxed_Box_close, {
      package := "anchor-lang", version := "0.29.0", source := registry
      },
      [("anchor_lang::AccountsClose::close",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsClose<'info> for \
          alloc::boxed::Box<T>>::close"), ("anchor_lang::AccountsClose::close", "anchor_lan\
            g::accounts::boxed::<impl anchor_lang::AccountsClose<'_> for \
            alloc::boxed::Box<T>>::close")]),
    (.accounts_boxed_Box_exit, {
      package := "anchor-lang", version := "0.29.0", source := registry
      },
      [("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
          alloc::boxed::Box<T>>::exit"), ("anchor_lang::AccountsExit::exit", "anchor_lang::\
            accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
            alloc::boxed::Box<T>>::exit")]),
    (.accounts_boxed_Box_try_accounts, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry },
      [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
          alloc::boxed::Box<T>>::try_accounts"), ("anchor_lang::Accounts::try_accounts", "a\
            nchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'_, B> for \
            alloc::boxed::Box<T>>::try_accounts")]),
    (.accounts_interface_account_InterfaceAccount_try_accounts, {
      package := "anchor-lang", version
      := "0.29.0", source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"), ("anchor_lang::Accounts::try_ac\
            counts", "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> \
              as anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_option_Option_exit, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry },
      [("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
          core::option::Option<T>>::exit"), ("anchor_lang::AccountsExit::exit", "anchor_lan\
            g::accounts::option::<impl anchor_lang::AccountsExit<'_> for \
            core::option::Option<T>>::exit")]),
    (.accounts_option_Option_try_accounts, {
      package := "anchor-lang", version := "0.29.0", source
      := registry },
      [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
          core::option::Option<T>>::try_accounts"), ("anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'_, B> for \
              core::option::Option<T>>::try_accounts")]),
    (.accounts_program_Program_try_accounts, {
      package := "anchor-lang", version := "0.29.0",
      source := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"), ("anchor_lang::Accounts::try_ac\
            counts", "<anchor_lang::accounts::program::Program<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_signer_Signer_try_accounts, {
      package := "anchor-lang", version := "0.29.0", source
      := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
          B>>::try_accounts"), ("anchor_lang::Accounts::try_accounts", "<anchor_lang::accou\
            nts::signer::Signer<'_> as anchor_lang::Accounts<'_, B>>::try_accounts")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_Account_exit_cloned_info, {
    package := "anchor-lang", version := "0.2\
    9.1",
    source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"), ("anchor_lang::AccountsExit::exit", "<\
            anchor_lang::accounts::account::Account<'_, T> as \
            anchor_lang::AccountsExit<'_>>::exit")]),
    (.accounts_interface_account_InterfaceAccount_exit_cloned_info, {
      package := "anchor-la\
      ng",
      version := "0.29.1", source := registry, dependencies := [⟨"solana-program", "1.18.26",
      registry⟩] },
      [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit"), ("anchor_lang::AccountsExit::exit", "<\
            anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
            anchor_lang::AccountsExit<'_>>::exit")]),
    (.accounts_program_Program_try_from, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry },
      [("core::convert::TryFrom::try_from",
        "<anchor_lang::accounts::program::Program<'a, T> as core::convert::TryFrom<&'a \
          solana_program::account_info::AccountInfo<'a>>>::try_from"), ("core::convert::Try\
            From::try_from", "<anchor_lang::accounts::program::Program<'_, T> as \
              core::convert::TryFrom<&'_ \
              solana_program::account_info::AccountInfo<'_>>>::try_from")]),
    (.accounts_signer_Signer_try_from, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry },
      [("anchor_lang::accounts::signer::Signer::<'info>::try_from",
        "anchor_lang::accounts::signer::Signer::<'info>::try_from"),
        ("anchor_lang::accounts::signer::Signer::<'_>::try_from",
        "anchor_lang::accounts::signer::Signer::<'_>::try_from")]),
    (.AccountsExit_exit, {
      package := "anchor-lang", version := "0.29.1", source := registry },
      [("anchor_lang::AccountsExit::exit", "anchor_lang::AccountsExit::exit")]),
    (.accounts_account_Account_close, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::AccountsClose::close",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::AccountsClose<'info>>::close"), ("anchor_lang::AccountsClose::close",
            "<anchor_lang::accounts::account::Account<'_, T> as \
              anchor_lang::AccountsClose<'_>>::close")]),
    (.accounts_account_Account_try_accounts, {
      package := "anchor-lang", version := "0.29.1",
      source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account::Account<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"), ("anchor_lang::Accounts::try_ac\
            counts", "<anchor_lang::accounts::account::Account<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_account_Account_try_from_unchecked, {
      package := "anchor-lang", version := "0.29.1",
      source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"),
        ("anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked",
        "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked")]),
    (.accounts_account_info_AccountInfo_try_accounts, {
      package := "anchor-lang", version :=
      "0.29.1", source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info, B> for \
          solana_program::account_info::AccountInfo<'info>>::try_accounts"), ("anchor_lang:\
            :Accounts::try_accounts", "anchor_lang::accounts::account_info::<impl \
              anchor_lang::Accounts<'_, B> for \
              solana_program::account_info::AccountInfo<'_>>::try_accounts")]),
    (.accounts_boxed_Box_close, {
      package := "anchor-lang", version := "0.29.1", source := registry
      },
      [("anchor_lang::AccountsClose::close",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsClose<'info> for \
          alloc::boxed::Box<T>>::close"), ("anchor_lang::AccountsClose::close", "anchor_lan\
            g::accounts::boxed::<impl anchor_lang::AccountsClose<'_> for \
            alloc::boxed::Box<T>>::close")]),
    (.accounts_boxed_Box_exit, {
      package := "anchor-lang", version := "0.29.1", source := registry
      },
      [("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
          alloc::boxed::Box<T>>::exit"), ("anchor_lang::AccountsExit::exit", "anchor_lang::\
            accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
            alloc::boxed::Box<T>>::exit")]),
    (.accounts_boxed_Box_try_accounts, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry },
      [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info, B> for \
          alloc::boxed::Box<T>>::try_accounts"), ("anchor_lang::Accounts::try_accounts", "a\
            nchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'_, B> for \
            alloc::boxed::Box<T>>::try_accounts")]),
    (.accounts_interface_account_InterfaceAccount_try_accounts, {
      package := "anchor-lang", version
      := "0.29.1", source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"), ("anchor_lang::Accounts::try_ac\
            counts", "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> \
              as anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_option_Option_exit, {
      package := "anchor-lang", version := "0.29.1", source :=
      registry },
      [("anchor_lang::AccountsExit::exit",
        "anchor_lang::accounts::option::<impl anchor_lang::AccountsExit<'info> for \
          core::option::Option<T>>::exit"), ("anchor_lang::AccountsExit::exit", "anchor_lan\
            g::accounts::option::<impl anchor_lang::AccountsExit<'_> for \
            core::option::Option<T>>::exit")]),
    (.accounts_option_Option_try_accounts, {
      package := "anchor-lang", version := "0.29.1", source
      := registry },
      [("anchor_lang::Accounts::try_accounts",
        "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'info, B> for \
          core::option::Option<T>>::try_accounts"), ("anchor_lang::Accounts::try_accounts",
            "anchor_lang::accounts::option::<impl anchor_lang::Accounts<'_, B> for \
              core::option::Option<T>>::try_accounts")]),
    (.accounts_program_Program_try_accounts, {
      package := "anchor-lang", version := "0.29.1",
      source := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::program::Program<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts"), ("anchor_lang::Accounts::try_ac\
            counts", "<anchor_lang::accounts::program::Program<'_, T> as \
              anchor_lang::Accounts<'_, B>>::try_accounts")]),
    (.accounts_signer_Signer_try_accounts, {
      package := "anchor-lang", version := "0.29.1", source
      := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info, \
          B>>::try_accounts"), ("anchor_lang::Accounts::try_accounts", "<anchor_lang::accou\
            nts::signer::Signer<'_> as anchor_lang::Accounts<'_, B>>::try_accounts")])]

theorem exact_reference_identities :
    referenceRows.length = 17 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 17 ∧ compatibleRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem build_metadata_keeps_actual_version :
    compatibleRows.all (fun row =>
      let build := { row.2.1 with version := row.2.1.version ++ "+review" }
      decide ((catalog.forBuild build).identities row.1 =
        row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩))) = true := by
  decide +kernel

def rejectedVersions : List (Key × Versioning.Build × List String) :=
  [(.accounts_account_Account_exit_cloned_info, {
    package := "anchor-lang", version := "0.2\
    9.0",
    source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] }, ["0.28\
      .999",
    "0.30.0", "0.29.0-rc.1"]),
    (.accounts_interface_account_InterfaceAccount_exit_cloned_info, {
      package := "anchor-la\
      ng",
      version := "0.29.0", source := registry, dependencies := [⟨"solana-program", "1.18.26",
      registry⟩] }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_program_Program_try_from, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_signer_Signer_try_from, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.AccountsExit_exit, {
      package := "anchor-lang", version := "0.29.0", source := registry },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_account_Account_close, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] }, ["0.28.999",
        "0.30.0",
      "0.29.0-rc.1"]),
    (.accounts_account_Account_try_accounts, {
      package := "anchor-lang", version := "0.29.0",
      source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] }, ["0.\
        28.999",
      "0.30.0", "0.29.0-rc.1"]),
    (.accounts_account_Account_try_from_unchecked, {
      package := "anchor-lang", version := "0.29.0",
      source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] }, ["0.\
        28.999",
      "0.30.0", "0.29.0-rc.1"]),
    (.accounts_account_info_AccountInfo_try_accounts, {
      package := "anchor-lang", version :=
      "0.29.0", source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_boxed_Box_close, {
      package := "anchor-lang", version := "0.29.0", source := registry
      }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_boxed_Box_exit, {
      package := "anchor-lang", version := "0.29.0", source := registry
      }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_boxed_Box_try_accounts, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_interface_account_InterfaceAccount_try_accounts, {
      package := "anchor-lang", version
      := "0.29.0", source := registry, dependencies := [⟨"solana-program", "1.18.26", registry⟩] },
      ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_option_Option_exit, {
      package := "anchor-lang", version := "0.29.0", source :=
      registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_option_Option_try_accounts, {
      package := "anchor-lang", version := "0.29.0", source
      := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_program_Program_try_accounts, {
      package := "anchor-lang", version := "0.29.0",
      source := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.accounts_signer_Signer_try_accounts, {
      package := "anchor-lang", version := "0.29.0", source
      := registry }, ["0.28.999", "0.30.0", "0.29.0-rc.1"])]

theorem bounds_and_prereleases_rejected :
    rejectedVersions.all (fun row => row.2.2.all (fun version =>
      ((catalog.forBuild { row.2.1 with version := version }).identities row.1).isEmpty)) = true :=
        by
  decide +kernel

theorem defining_package_and_fork_rejected :
    (referenceRows ++ compatibleRows).all (fun row =>
      ((catalog.forBuild { row.2.1 with package := "wrong-defining-package" }).identities
        row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with source :=
        ⟨"git", "https://example.invalid/source-fork", "01234567890123456789012345678901234\
          56789"⟩
        }).identities row.1).isEmpty) = true := by
  decide +kernel

/-- Literal provider intervals test selection, without claiming native coverage. -/
def dependencyVersions : List (String × String × List String) :=
  [("solana-program", "1.18.27", ["1.18.25", "2.0.0", "1.18.27-rc.1"])]

theorem compatible_dependencies_keep_literal_identities :
    dependencyVersions.length = 1 ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        let build := { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
          if d.package = dep.package then { d with version := item.2.1 } else d) }
        decide ((catalog.forBuild build).identities row.1 =
          row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩)))) = true :=
            by
  decide +kernel

theorem dependency_bounds_prereleases_and_two_compatible_candidates_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        item.2.2.all (fun version =>
          ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
            if d.package = dep.package then { d with version } else d) }).identities
              row.1).isEmpty) &&
        ((catalog.forBuild { row.2.1 with dependencies :=
          row.2.1.dependencies ++ [{ dep with version := item.2.1 }] }).identities row.1).isEmpty))
            = true := by
  decide +kernel

theorem required_dependency_cannot_be_omitted :
    referenceRows.any (fun row => !row.2.1.dependencies.isEmpty) = true ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.filter (fun d => d.package != dep.package)) }).identities
          row.1).isEmpty)) = true := by
  decide +kernel

theorem dependency_generation_fork_and_ambiguity_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with version := "99.0.0" } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with source := ⟨"git", "https://example.invalid/provider-fork",
            "0123456789012345678901234567890123456789"⟩ } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies ++ [dep] }).identities
        row.1).isEmpty)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.LegacyAccountCompatibility

/- Per-operation compatibility selection. Synthetic versions carry no native or ABI credit. -/
namespace SolanalibTest.Specs.AnchorLang.Accounts.LegacyCompatibility

@[expose] public section

set_option autoImplicit false

namespace Lifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  dependencies := [⟨"solana-program", "1.15.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.accounts_account_Account_close_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::AccountsClose::close",
      "<anchor_lang::accounts::account::Account<'info, T> as \
        anchor_lang::AccountsClose<'info>>::close"⟩, ⟨"anchor-lang", version, "anchor_lang:\
          :AccountsClose::close", "<anchor_lang::accounts::account::Account<'_, T> as \
            anchor_lang::AccountsClose<'_>>::close"⟩]),
    (.accounts_account_Account_exit_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::AccountsExit::exit",
      "<anchor_lang::accounts::account::Account<'info, T> as \
        anchor_lang::AccountsExit<'info>>::exit"⟩, ⟨"anchor-lang", version, "anchor_lang::A\
          ccountsExit::exit", "<anchor_lang::accounts::account::Account<'_, T> as \
            anchor_lang::AccountsExit<'_>>::exit"⟩]),
    (.accounts_account_Account_reload_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::accounts::account::Account::<'a, T>::reload",
      "anchor_lang::accounts::account::Account::<'a, T>::reload"⟩, ⟨"anchor-lang", version,
      "anchor_lang::accounts::account::Account::<'_, T>::reload",
      "anchor_lang::accounts::account::Account::<'_, T>::reload"⟩]),
    (.accounts_account_Account_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "<anchor_lang::accounts::account::Account<'info, T> as \
        anchor_lang::Accounts<'info>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lan\
          g::Accounts::try_accounts", "<anchor_lang::accounts::account::Account<'_, T> as \
            anchor_lang::Accounts<'_>>::try_accounts"⟩]),
    (.accounts_account_Account_try_from_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::accounts::account::Account::<'a, T>::try_from",
      "anchor_lang::accounts::account::Account::<'a, T>::try_from"⟩, ⟨"anchor-lang", version,
      "anchor_lang::accounts::account::Account::<'_, T>::try_from",
      "anchor_lang::accounts::account::Account::<'_, T>::try_from"⟩]),
    (.accounts_account_Account_try_from_unchecked_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked",
      "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked"⟩, ⟨"anchor-lan\
        g",
      version, "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked",
      "anchor_lang::accounts::account::Account::<'_, T>::try_from_unchecked"⟩]),
    (.accounts_account_info_AccountInfo_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info> for \
        solana_program::account_info::AccountInfo<'info>>::try_accounts"⟩, ⟨"anchor-lang", version,
          "anchor_lang::Accounts::try_accounts",
          "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'_> for \
            solana_program::account_info::AccountInfo<'_>>::try_accounts"⟩]),
    (.accounts_program_Program_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "<anchor_lang::accounts::program::Program<'info, T> as \
        anchor_lang::Accounts<'info>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lan\
          g::Accounts::try_accounts", "<anchor_lang::accounts::program::Program<'_, T> as \
            anchor_lang::Accounts<'_>>::try_accounts"⟩]),
    (.accounts_signer_Signer_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "<anchor_lang::accounts::signer::Signer<'info> as \
        anchor_lang::Accounts<'info>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lan\
          g::Accounts::try_accounts", "<anchor_lang::accounts::signer::Signer<'_> as \
            anchor_lang::Accounts<'_>>::try_accounts"⟩]),
    (.accounts_system_account_SystemAccount_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
        anchor_lang::Accounts<'info>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lan\
          g::Accounts::try_accounts", "<anchor_lang::accounts::system_account::SystemAccoun\
            t<'_> as anchor_lang::Accounts<'_>>::try_accounts"⟩]),
    (.accounts_sysvar_Sysvar_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as \
        anchor_lang::Accounts<'info>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lan\
          g::Accounts::try_accounts", "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as \
            anchor_lang::Accounts<'_>>::try_accounts"⟩]),
    (.accounts_unchecked_account_UncheckedAccount_try_accounts_inline_error, [⟨"anchor-lang",
      version, "anchor_lang::Accounts::try_accounts",
      "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
        anchor_lang::Accounts<'info>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lan\
          g::Accounts::try_accounts", "<anchor_lang::accounts::unchecked_account::Unchecked\
            Account<'_> as anchor_lang::Accounts<'_>>::try_accounts"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

theorem every_dependency_is_required_and_unambiguous :
    [referenceBuild, compatibleBuild].all (fun build =>
      build.dependencies.all (fun dep =>
        (identityCases build.version).all (fun entry =>
          ((catalog.forBuild { build with dependencies := build.dependencies.filter (fun kept =>
            kept.package != dep.package) }).identities entry.1).isEmpty &&
          ((catalog.forBuild { build with dependencies := build.dependencies ++ [dep] }).identities
            entry.1).isEmpty))) = true := by decide +kernel

theorem every_dependency_rejects_wrong_release_or_origin :
    compatibleBuild.dependencies.all (fun dep =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with version := "99.0.0" } else kept)
            }).identities entry.1).isEmpty &&
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun kept =>
              if kept.package = dep.package then { kept with source := ⟨"git", "https://example.org/provider-fork",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else kept) }).identities
                  entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_dependency_actual_identities :
    ([("solana-program", "1.15.3")] : List (String × String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry => decide
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1 = entry.2))) = true := by decide +kernel

theorem exact_codecs_and_dependency_boundaries_retained :
    ([("solana-program", "1.16.0"), ("solana-program", "1.15.3-rc.1")] : List (String ×
      String)).all (fun change =>
      (identityCases compatibleBuild.version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with
          dependencies := compatibleBuild.dependencies.map
            (fun dep =>
              if dep.package = change.1 then { dep with version := change.2 } else dep)
                }).identities
            entry.1).isEmpty)) = true := by decide +kernel

end Lifecycle

namespace Delegation

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorLang.Capabilities (catalog)

/-- Exact inspected reference; the declared dependencies and build facts are operation-specific. -/
def referenceBuild : Versioning.Build where
  package := "anchor-lang"
  version := "0.27.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Synthetic selector input only; no extra inspected or native-tested release is claimed. -/
def compatibleBuild : Versioning.Build := { referenceBuild with version := "0.27.1" }

def identityCases (version : String) : List (AnchorLang.Capabilities.Key × List
  Solanalib.Contracts.Model.Capabilities.RustIdentity) :=
  [
    (.accounts_boxed_Box_try_accounts_inline_error, [⟨"anchor-lang", version,
      "anchor_lang::Accounts::try_accounts",
      "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info> for \
        alloc::boxed::Box<T>>::try_accounts"⟩, ⟨"anchor-lang", version, "anchor_lang::Accou\
          nts::try_accounts", "anchor_lang::accounts::boxed::<impl \
            anchor_lang::Accounts<'_> for alloc::boxed::Box<T>>::try_accounts"⟩]),
    (.accounts_unchecked_account_UncheckedAccount_try_from_owned_info, [⟨"anchor-lang", version,
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from",
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from"⟩,
      ⟨"anchor-lang", version,
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from",
      "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'_>::try_from"⟩]),
    (.AccountsExit_exit, [⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
      "anchor_lang::AccountsExit::exit"⟩]),
    (.accounts_boxed_Box_exit, [⟨"anchor-lang", version, "anchor_lang::AccountsExit::exit",
      "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for \
        alloc::boxed::Box<T>>::exit"⟩, ⟨"anchor-lang", version, "anchor_lang::AccountsExit:\
          :exit", "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'_> for \
            alloc::boxed::Box<T>>::exit"⟩])
  ]

/-- Literal source identities are independent of generated catalog identities. -/
theorem reference_and_compatible_identities :
    [referenceBuild, compatibleBuild].all (fun build =>
      (identityCases build.version).all (fun entry => decide
        ((catalog.forBuild build).identities entry.1 = entry.2))) = true := by decide +kernel

theorem compatibility_boundaries_and_prerelease_rejected :
    ["0.26.9", "0.28.0", "0.27.1-rc.1"].all (fun version =>
      (identityCases version).all (fun entry =>
        ((catalog.forBuild { compatibleBuild with version := version }).identities
          entry.1).isEmpty)) = true := by decide +kernel

theorem compatible_origin_rejected :
    (identityCases compatibleBuild.version).all (fun entry =>
      ((catalog.forBuild { compatibleBuild with source :=
        ⟨"git", "https://example.org/source-fork", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
          a"⟩ }).identities entry.1).isEmpty) = true := by decide +kernel

end Delegation

end

end SolanalibTest.Specs.AnchorLang.Accounts.LegacyCompatibility
