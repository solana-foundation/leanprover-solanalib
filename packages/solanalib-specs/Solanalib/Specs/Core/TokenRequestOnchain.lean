/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestHooks
public import Solanalib.Specs.Core.TokenInstructionConstructors
public import Solanalib.Specs.Core.AccountInfoDataAdmission
import Solanalib.Specs.Core.AccountInfoGuardCallback
import Solanalib.Specs.Core.BorrowFacts
public import Solanalib.Specs.Core.CpiRequest
public import Solanalib.Specs.Core.TokenExtensionState

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Onchain

/-- The common AccountInfo borrow world used by these value observations. -/
abbrev State := AccountInfo.State
/-- An AccountInfo value retaining its shared cell identities. -/
abbrev Account := AccountInfo.Value

/-- Local panics of ordinary Token-2022 11.0.0 preparation. -/
inductive Panic where
  /-- An unchecked data borrow conflicts with an existing live borrow. -/
  | borrowFailed
  /-- The multisig n field exceeds its eleven stored signer keys. -/
  | multisigSignerRange
  /-- No PDA bump produced a viable address. -/
  | noViableProgramAddress
  deriving DecidableEq, Repr

/-- Malformed mathematical representations are distinct from source errors and
panics. The contract excludes them; they do not manufacture a Rust result. -/
inductive Step (Value : Type) where
  /-- A normally returned local value. -/
  | success (value : Value)
  /-- A normally returned ProgramError. -/
  | error (error : Error)
  /-- A local panic whose target interpretation is supplied separately. -/
  | panic (reason : Panic)
  /-- A mathematical representation failure, not a fabricated source result. -/
  | malformed
  deriving DecidableEq, Repr

/-- Stateful sequencing preserves failure states and calls the continuation
only after a successful preparation step. -/
def bind {Value Next : Type} (step : Step Value × State)
    (next : State → Value → Step Next × State) : Step Next × State :=
  match step.1 with
  | .success value => next step.2 value
  | .error error => (.error error, step.2)
  | .panic reason => (.panic reason, step.2)
  | .malformed => (.malformed, step.2)

/-- The local instruction and account vector before the opaque invocation. -/
structure Prepared where
  /-- The ordered instruction value prepared for the opaque call. -/
  instruction : Solanalib.Runtime.CpiInstruction
  /-- The ordered account payloads, preserving duplicates. -/
  accounts : List Account
  deriving DecidableEq, Repr

/-- Add the unchanged signer seeds of the caller to a prepared request. -/
def Prepared.request (prepared : Prepared) (signers : List (List Bytes)) :
    CpiRequest.Request Account := ⟨prepared.instruction, prepared.accounts, signers⟩

/-- Checked-transfer source arguments and explicit target/cryptographic interpretations. -/
structure Args where
  /-- The AccountInfo borrow and target panic profile. -/
  profile : AccountInfo.Profile
  /-- The explicit PDA hash and curve interpretation. -/
  crypto : Address.Crypto
  /-- The target Token program ID supplied by the caller. -/
  tokenProgramId : Solanalib.Runtime.Pubkey
  /-- The source account or observed account reference. -/
  source : Account
  /-- The readonly mint account or observed reference. -/
  mint : Account
  /-- The destination account or observed account reference. -/
  destination : Account
  /-- The authority account or observed account reference. -/
  authority : Account
  /-- The ordered additional AccountInfos searched for signers and hook accounts. -/
  additional : List Account
  /-- The unsigned transfer amount, constrained to the source u64 range. -/
  amount : Nat
  /-- The decimal value constrained to the source u8 range. -/
  decimals : Nat
  /-- The original ordered signer seed slices forwarded to CPI. -/
  signers : List (List Bytes)

/-- A Rust byte slice occupies at most isize::MAX bytes. This bound makes
the saturating usize additions of the selected dependencies agree with the natural
range checks on every admitted slice. -/
def dataAddressable (profile : AccountInfo.Profile) (state : State) (info : Account) : Prop :=
  ∃ bytes, state.lookupCell info.data = some ⟨.data bytes, profile.policy⟩ ∧
    bytes.length < 2^(profile.wordBits - 1)

/-- Pointer-size conversions in these selected dependencies are interpreted
on targets at least 32 bits wide, with addressable Rust byte slices. All
AccountInfo aliases use the same world. -/
def Args.Valid (args : Args) (state : State) : Prop :=
  32 ≤ args.profile.wordBits ∧
    args.amount < Solanalib.Runtime.U64_LIMIT ∧ args.decimals < 256 ∧
    args.additional.length + 4 < 2^args.profile.wordBits ∧
    ∀ info ∈ [args.source, args.mint, args.destination, args.authority] ++ args.additional,
      AccountInfo.Valid args.profile state info ∧ dataAddressable args.profile state info

/-- An acquired shared data guard and its immediate byte observation. -/
structure Borrowed where
  /-- The actual acquired borrow identity. -/
  guard : Borrow.Guard
  /-- The data bytes observed immediately after acquisition. -/
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Both checked and unchecked acquisitions use the same live guard protocol.
Only their failure interpretation differs. -/
def borrowData (checked : Bool) (state : State) (info : Account) : Step Borrowed × State :=
  let (result, after) := AccountInfo.tryBorrow .shared info.data state
  match result with
  | .error _ =>
    if checked then (.error .AccountBorrowFailed, after) else (.panic .borrowFailed, after)
  | .ok guard =>
    match Borrow.current after guard with
    | .ok (_, .data bytes) => (.success ⟨guard, bytes⟩, after)
    | _ => (.malformed, after)

/-- Release one actual guard after the selected value-level step. -/
def releaseOne {Value : Type} (step : Step Value × State) (guard : Borrow.Guard) :
    Step Value × State :=
  match Borrow.release step.2 guard with
  | (.ok (), after) => (step.1, after)
  | (.error _, after) => (.malformed, after)

/-- Scoped data guards are released on ordinary errors and on unwind. A
terminal panic has no post-state, so the cleanup state is not exposed there. -/
def withData {Value : Type} (checked : Bool) (state : State) (info : Account)
    (next : State → Bytes → Step Value × State) : Step Value × State :=
  bind (borrowData checked state info) fun after borrowed =>
    releaseOne (next after borrowed.bytes) borrowed.guard

/-- The owner test short-circuits before the source data_len getter. The getter
itself acquires and releases a shared guard and can panic on a borrow conflict. -/
def isMultisig (state : State) (info : Account) : Step Bool × State :=
  if info.owner != token2022ProgramId && info.owner != legacyProgramId then (.success false, state)
  else
    match AccountInfo.observe .dataLen state info with
    | (.value length, after) => (.success (length == multisigLength), after)
    | (.borrowFailed, after) => (.panic .borrowFailed, after)
    | (.malformed, after) => (.malformed, after)

/-- The POD multisig reader checks size only. It does not validate the
initialized flag, threshold, or the signer flags of additional accounts. -/
def multisigKeys (bytes : Bytes) : Step (List Solanalib.Runtime.Pubkey) :=
  if bytes.length ≠ multisigLength then .error .InvalidArgument
  else
    let count := bytes[1]!.toNat
    if 11 < count then .panic .multisigSignerRange
    else .success ((List.range count).map fun index =>
      Solanalib.Runtime.Pubkey.ofBytes (Solanalib.Runtime.slice bytes (3 + 32 * index) 32))

/-- Value-level multisig selection, account ordering and authority-flag correction. -/
def addMultisig (state : State) (args : Args) (prepared : Prepared) : Step Prepared × State :=
  bind (isMultisig state args.authority) fun after recognized =>
    if !recognized then (.success prepared, after)
    else withData false after args.authority fun during bytes =>
      bind (multisigKeys bytes, during) fun current keys =>
        let selected := args.additional.filter (fun info => keys.contains info.key)
        let baseMetas := prepared.instruction.metas.mapIdx fun index item =>
          if index = 3 then { item with signerByte := 0 } else item
        (.success {
          instruction := { prepared.instruction with
            metas := baseMetas ++ selected.map
              (fun info => Solanalib.Specs.Core.Instruction.accountMeta info.key true false) }
          accounts := prepared.accounts ++ selected }, current)

/-- Every acquisition in a temporary collected vector is dropped, including
after a borrow of a later account fails. -/
def releaseMany : State → List Borrow.Guard → Step Unit × State
  | state, [] => (.success (), state)
  | state, guard :: rest =>
    match Borrow.release state guard with
    | (.ok (), after) => releaseMany after rest
    | (.error _, after) => (.malformed, after)

/-- Release the acquired guard prefix before exposing the selected local result. -/
def cleanup {Value : Type} (result : Step Value) (state : State) (guards : List Borrow.Guard) :
    Step Value × State :=
  bind (releaseMany state guards) fun after _ => (result, after)

/-- The observations are collected in account-vector order, retaining aliases.
A conflict releases the already acquired prefix before returning its error. -/
def collectDataAux : State → List Account → List Borrow.Guard → Hook.Observations →
    Step (List Borrow.Guard × Hook.Observations) × State
  | state, [], guards, observations => (.success (guards, observations), state)
  | state, info :: rest, guards, observations =>
    match borrowData true state info with
    | (.success borrowed, after) =>
      collectDataAux after rest (guards ++ [borrowed.guard])
        (observations ++ [(info.key, some borrowed.bytes)])
    | (.error error, after) => cleanup (.error error) after guards
    | (.panic reason, after) => cleanup (.panic reason) after guards
    | (.malformed, after) => cleanup .malformed after guards

/-- Translate an ordinary resolver error or PDA panic into the local step type. -/
def resolveFailure : Hook.ResolveFailure → Step Solanalib.Runtime.CpiMeta
  | .program error => .error error
  | .noViableProgramAddress => .panic .noViableProgramAddress

/-- Resolve each meta against all accounts accumulated so far. All temporary
data guards are released before privilege reduction and first-match lookup. -/
def addExtraMetas (crypto : Address.Crypto) (additional : List Account) :
    List Hook.ExtraMeta → State → Prepared → Step Prepared × State
  | [], state, prepared => (.success prepared, state)
  | extra :: rest, state, prepared =>
    bind (collectDataAux state prepared.accounts [] []) fun during collected =>
      let resolved := match Hook.resolve crypto prepared.instruction.data
          prepared.instruction.programId collected.2 extra with
        | .ok item => Step.success item
        | .error error => resolveFailure error
      bind (cleanup resolved during collected.1) fun after item =>
        let reduced := Hook.deescalate prepared.instruction.metas item
        match additional.find? (fun info => info.key == reduced.key) with
        | none => (.error Hook.incorrectExtraAccount, after)
        | some info =>
          addExtraMetas crypto additional rest after {
            instruction := { prepared.instruction with metas := prepared.instruction.metas ++
              [reduced] }
            accounts := prepared.accounts ++ [info] }

/-- The transfer-hook helper resolves its validation PDA before searching for
the hook program account. A missing validation account is permitted. -/
def addHook (state : State) (args : Args) (programId : Solanalib.Runtime.Pubkey)
    (prepared : Prepared) : Step Prepared × State :=
  match Address.tryFind ⟨args.crypto, [Hook.extraAccountMetasSeed, args.mint.key.bytes], programId⟩
    with
  | none => (.panic .noViableProgramAddress, state)
  | some (validationKey, _) =>
    match args.additional.find? (fun info => info.key == programId) with
    | none => (.error Hook.incorrectHookAccount, state)
    | some programInfo =>
      let appendProgram := fun (result : Prepared) => {
        instruction := { result.instruction with
          metas := result.instruction.metas ++
            [Solanalib.Specs.Core.Instruction.accountMeta programId false false] }
        accounts := result.accounts ++ [programInfo] : Prepared }
      match args.additional.find? (fun info => info.key == validationKey) with
      | none => (.success (appendProgram prepared), state)
      | some validationInfo =>
        withData true state validationInfo fun during bytes =>
          let decoded := match Hook.decodeValidation bytes with
            | .ok extras => Step.success extras
            | .error error => Step.error error
          bind (decoded, during) fun current extras =>
            let execute := {
              instruction := { Hook.executeInstruction programId args.source.key args.mint.key
                  args.destination.key args.authority.key args.amount with
                metas := (Hook.executeInstruction programId args.source.key args.mint.key
                  args.destination.key args.authority.key args.amount).metas ++
                    [Solanalib.Specs.Core.Instruction.accountMeta validationKey false false] }
              accounts := [args.source, args.mint, args.destination, args.authority, validationInfo]
              : Prepared }
            bind (addExtraMetas args.crypto args.additional extras current execute) fun after
              extended =>
              (.success (appendProgram {
                instruction := { prepared.instruction with
                  metas := prepared.instruction.metas ++ extended.instruction.metas.drop 5 ++
                    [Solanalib.Specs.Core.Instruction.accountMeta validationKey false false] }
                accounts := prepared.accounts ++ extended.accounts.drop 5 ++ [validationInfo] }),
                  after)

/-- Transfer-hook retrieval intentionally treats every extension lookup error
as absence. The optional program ID uses zero as its None encoding. -/
def hookProgram (tlv : Bytes) : Option Solanalib.Runtime.Pubkey :=
  match getExtension .mint ⟨.transferHook, 64, 1⟩ 0 tlv with
  | .error _ => none
  | .ok view =>
    let key := Solanalib.Runtime.Pubkey.ofBytes (Solanalib.Runtime.slice view.bytes 32 32)
    if key == .zero then none else some key

/-- The mint guard spans parsing and all extra-account preparation; it is
released before returning either a constructed request or an ordinary error. -/
def addMintExtensions (state : State) (args : Args) (prepared : Prepared) :
    Step Prepared × State :=
  withData true state args.mint fun during bytes =>
    match unpackMintWithExtensions bytes with
    | .error error => (.error error, during)
    | .ok mint =>
      match hookProgram mint.tlv with
      | none => (.success prepared, during)
      | some programId => addHook during args programId prepared

/-- Complete value-level preparation of invoke_transfer_checked (fee=None).
Program admission precedes every AccountInfo borrow and parsing operation. -/
def prepare (state : State) (args : Args) : Step Prepared × State :=
  match Instruction.transferChecked .either {
    programId := args.tokenProgramId
    source := args.source.key
    mint := args.mint.key
    destination := args.destination.key
    authority := args.authority.key
    signers := []
    amount := args.amount
    decimals := args.decimals } with
  | .error error => (.error error, state)
  | .ok instruction =>
    let base := {
      instruction := instruction
      accounts := [args.source, args.mint, args.destination, args.authority] : Prepared }
    bind (addMultisig state args base) fun after prepared => addMintExtensions after args prepared

/-- Inspect the actual successful prefix before admitting its continuation.
An error or panic does not demand any later input. This does not assert that
the prefix itself is well formed. -/
def AfterSuccess {Value : Type} (step : Step Value × State)
    (ready : State → Value → Prop) : Prop :=
  match step.1 with
  | .success value => ready step.2 value
  | .error _ | .panic _ | .malformed => True

/-- Local destructor admission tests the actual held token at the actual
cleanup state. It grants no cell, owner or target-width invariant. -/
def ReleaseReady (state : State) (guard : Borrow.Guard) : Prop :=
  (Borrow.release state guard).1 = .ok ()

/-- The acquired prefix is released in the order of the raw collector, with each
check made in the state produced by the preceding release. -/
def ReleasesReady : State → List Borrow.Guard → Prop
  | _, [] => True
  | state, guard :: rest =>
    match Borrow.release state guard with
    | (.ok (), after) => ReleasesReady after rest
    | (.error _, _) => False

/-- Admission for a scoped read. The local requirements of the body are checked
independently of its result; its held token must also survive to the actual
cleanup point. No completed outer preparation is assumed. -/
def ScopeReady {Value : Type} (checked : Bool) (state : State) (info : Account)
    (next : State → Bytes → Step Value × State) (bodyReady : State → Bytes → Prop) : Prop :=
  AccountInfo.DataBorrow.Ready .shared state info.data ∧
    AfterSuccess (borrowData checked state info) fun during borrowed =>
      bodyReady during borrowed.bytes ∧ ReleaseReady (next during borrowed.bytes).2 borrowed.guard

/-- Sequencing preserves every nonmalformed local result when the actual
successful continuation has its own input admission. -/
theorem bind_not_malformed {Value Next : Type} {step : Step Value × State}
    {next : State → Value → Step Next × State} {ready : State → Value → Prop}
    (first : step.1 ≠ .malformed) (admitted : AfterSuccess step ready)
    (continued : ∀ during value, ready during value → (next during value).1 ≠ .malformed) :
    (bind step next).1 ≠ .malformed := by
  rcases step with ⟨result, during⟩
  cases result with
  | success value => exact continued during value admitted
  | error error => simp [bind]
  | panic reason => simp [bind]
  | malformed => exact False.elim (first rfl)

/-- Selected-data admission retains both checked errors and unchecked panics;
successful acquisition exposes the actual current bytes. -/
theorem borrowData_not_malformed {checked : Bool} {state : State} {info : Account}
    (ready : AccountInfo.DataBorrow.Ready .shared state info.data) :
    (borrowData checked state info).1 ≠ .malformed := by
  cases acquired : AccountInfo.tryBorrow .shared info.data state with
  | mk result during =>
    cases result with
    | error failure => cases checked <;> simp [borrowData, acquired]
    | ok guard =>
      obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current ready acquired
      simp [borrowData, acquired, current]

/-- A returned data observation retains the guard and
state of the actual acquisition, rather than an independently selected token. -/
theorem borrowData_acquired {checked : Bool} {state during : State} {info : Account}
    {borrowed : Borrowed}
    (success : borrowData checked state info = (.success borrowed, during)) :
    AccountInfo.tryBorrow .shared info.data state = (.ok borrowed.guard, during) := by
  cases acquired : AccountInfo.tryBorrow .shared info.data state with
  | mk result after =>
    cases result with
    | error failure => cases checked <;> simp [borrowData, acquired] at success
    | ok guard =>
      cases current : Borrow.current after guard with
      | error failure => simp [borrowData, acquired, current] at success
      | ok observation =>
        rcases observation with ⟨view, content⟩
        cases content with
        | lamports value => simp [borrowData, acquired, current] at success
        | data bytes =>
          simp only [borrowData, acquired, current, Prod.mk.injEq, Step.success.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          rfl

/-- An immediate successful data read can release its token, without a global
borrow-world validity assumption. -/
theorem borrowData_release {checked : Bool} {state during : State} {info : Account}
    {borrowed : Borrowed}
    (success : borrowData checked state info = (.success borrowed, during)) :
    ReleaseReady during borrowed.guard := by
  have acquired := AccountInfo.GuardCallback.tryBorrow_acquire (borrowData_acquired success)
  simp only [ReleaseReady, Borrow.release_after_acquire acquired]

/-- A pure body that leaves the borrow world unchanged needs no additional
release assumption for the newly acquired guard. -/
theorem scopeReady_of_unchanged {Value : Type} {checked : Bool} {state : State} {info : Account}
    {next : State → Bytes → Step Value × State} {bodyReady : State → Bytes → Prop}
    (dataReady : AccountInfo.DataBorrow.Ready .shared state info.data)
    (body : ∀ during bytes, bodyReady during bytes)
    (unchanged : ∀ during bytes, (next during bytes).2 = during) :
    ScopeReady checked state info next bodyReady := by
  refine ⟨dataReady, ?_⟩
  cases step : borrowData checked state info with
  | mk result during =>
    cases result with
    | success borrowed =>
      exact ⟨body during borrowed.bytes,
        by simpa only [unchanged] using borrowData_release step⟩
    | error _ | panic _ | malformed => trivial

/-- A legal local destructor keeps the selected value, ordinary error or panic
and uses the actual release state. -/
theorem releaseOne_preserves {Value : Type} {step : Step Value × State} {guard : Borrow.Guard}
    (ready : ReleaseReady step.2 guard) :
    (releaseOne step guard).1 = step.1 := by
  cases released : Borrow.release step.2 guard with
  | mk result after =>
    cases result with
    | error failure => simp [ReleaseReady, released] at ready
    | ok value => cases value; simp only [releaseOne, released]

/-- Scoped admission prevents its read or release from erasing the actual
body result. The guarantee of the body is applied at the reached read state. -/
theorem withData_not_malformed {Value : Type} {checked : Bool} {state : State} {info : Account}
    {next : State → Bytes → Step Value × State} {bodyReady : State → Bytes → Prop}
    (ready : ScopeReady checked state info next bodyReady)
    (body : ∀ during bytes, bodyReady during bytes → (next during bytes).1 ≠ .malformed) :
    (withData checked state info next).1 ≠ .malformed := by
  apply bind_not_malformed (borrowData_not_malformed ready.1) ready.2
  intro during borrowed admitted
  rw [releaseOne_preserves admitted.2]
  exact body during borrowed.bytes admitted.1

/-- Each admitted prefix release completes locally, retaining its exact
sequence of tombstones. No opaque provider termination is assumed. -/
theorem releaseMany_success {state : State} {guards : List Borrow.Guard}
    (ready : ReleasesReady state guards) :
    ∃ after, releaseMany state guards = (.success (), after) := by
  induction guards generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons guard rest ih =>
    cases released : Borrow.release state guard with
    | mk result during =>
      cases result with
      | error failure => simp [ReleasesReady, released] at ready
      | ok value =>
        cases value
        obtain ⟨after, done⟩ := ih (by simpa only [ReleasesReady, released] using ready)
        exact ⟨after, by simp only [releaseMany, released, done]⟩

/-- Admitted prefix cleanup preserves the original value/error/panic while
returning the actual release state. -/
theorem cleanup_preserves {Value : Type} {result : Step Value} {state : State}
    {guards : List Borrow.Guard} (ready : ReleasesReady state guards) :
    (cleanup result state guards).1 = result := by
  obtain ⟨after, released⟩ := releaseMany_success ready
  simp only [cleanup, released, bind]

/-- The ordinary data-length getter distinguishes missing storage from a
borrow conflict. Only its reached successful acquisition needs a data read. -/
def DataLenReady (state : State) (info : Account) : Prop :=
  match Borrow.acquire state info.data .shared AccountInfo.View.whole with
  | (.error .conflict, _) | (.error .sharedLimit, _) => True
  | (.error _, _) => False
  | (.ok _, _) => AccountInfo.DataBorrow.Ready .shared state info.data

/-- The owner test bypasses the data-length getter for every other program. -/
def MultisigReady (state : State) (info : Account) : Prop :=
  if info.owner != token2022ProgramId && info.owner != legacyProgramId then True
  else DataLenReady state info

/-- Only a recognized multisig reaches its second data borrow. Its body changes
no borrow state, so immediate release is derived rather than required. -/
def AddMultisigReady (state : State) (args : Args) : Prop :=
  MultisigReady state args.authority ∧
    AfterSuccess (isMultisig state args.authority) fun after recognized =>
      if !recognized then True else AccountInfo.DataBorrow.Ready .shared after args.authority.data

/-- Collection admission follows each actual acquisition and checks only the
already acquired prefix when the next checked borrow fails. -/
def CollectReady : State → List Account → List Borrow.Guard → Prop
  | _, [], _ => True
  | state, info :: rest, guards =>
    AccountInfo.DataBorrow.Ready .shared state info.data ∧
      match borrowData true state info with
      | (.success borrowed, after) => CollectReady after rest (guards ++ [borrowed.guard])
      | (.error _, after) | (.panic _, after) => ReleasesReady after guards
      | (.malformed, _) => True

/-- Each extra meta independently admits its reached data collection and
cleanup, then continues only after the actual resolver and account lookup
succeed. Pure resolver errors and PDA panics demand no later account. -/
def ExtraReady (crypto : Address.Crypto) (additional : List Account) :
    List Hook.ExtraMeta → State → Prepared → Prop
  | [], _, _ => True
  | extra :: rest, state, prepared =>
    CollectReady state prepared.accounts [] ∧
      AfterSuccess (collectDataAux state prepared.accounts [] []) fun during collected =>
        ReleasesReady during collected.1 ∧
          let resolved := match Hook.resolve crypto prepared.instruction.data
              prepared.instruction.programId collected.2 extra with
            | .ok item => Step.success item
            | .error error => resolveFailure error
          AfterSuccess (cleanup resolved during collected.1) fun after item =>
            let reduced := Hook.deescalate prepared.instruction.metas item
            match additional.find? (fun info => info.key == reduced.key) with
            | none => True
            | some info =>
              ExtraReady crypto additional rest after {
                instruction := { prepared.instruction with
                  metas := prepared.instruction.metas ++ [reduced] }
                accounts := prepared.accounts ++ [info] }

/-- Validation-data admission is reached only after successful PDA resolution
and the hook-program lookup. Missing validation accounts retain their ordinary
success branch; a present one admits each nested read and its own release. -/
def HookReady (state : State) (args : Args) (programId : Solanalib.Runtime.Pubkey)
    (prepared : Prepared) : Prop :=
  match Address.tryFind ⟨args.crypto, [Hook.extraAccountMetasSeed, args.mint.key.bytes], programId⟩
    with
  | none => True
  | some (validationKey, _) =>
    match args.additional.find? (fun info => info.key == programId) with
    | none => True
    | some programInfo =>
      let appendProgram := fun (result : Prepared) => {
        instruction := { result.instruction with
          metas := result.instruction.metas ++
            [Solanalib.Specs.Core.Instruction.accountMeta programId false false] }
        accounts := result.accounts ++ [programInfo] : Prepared }
      match args.additional.find? (fun info => info.key == validationKey) with
      | none => True
      | some validationInfo =>
        ScopeReady true state validationInfo (fun during bytes =>
          let decoded := match Hook.decodeValidation bytes with
            | .ok extras => Step.success extras
            | .error error => Step.error error
          bind (decoded, during) fun current extras =>
            let execute := {
              instruction := { Hook.executeInstruction programId args.source.key args.mint.key
                  args.destination.key args.authority.key args.amount with
                metas := (Hook.executeInstruction programId args.source.key args.mint.key
                  args.destination.key args.authority.key args.amount).metas ++
                    [Solanalib.Specs.Core.Instruction.accountMeta validationKey false false] }
              accounts := [args.source, args.mint, args.destination, args.authority, validationInfo]
              : Prepared }
            bind (addExtraMetas args.crypto args.additional extras current execute) fun after
              extended =>
              (.success (appendProgram {
                instruction := { prepared.instruction with
                  metas := prepared.instruction.metas ++ extended.instruction.metas.drop 5 ++
                    [Solanalib.Specs.Core.Instruction.accountMeta validationKey false false] }
                accounts := prepared.accounts ++ extended.accounts.drop 5 ++ [validationInfo] }),
                  after))
          (fun during bytes =>
            match Hook.decodeValidation bytes with
            | .error _ => True
            | .ok extras =>
              ExtraReady args.crypto args.additional extras during {
                instruction := { Hook.executeInstruction programId args.source.key args.mint.key
                    args.destination.key args.authority.key args.amount with
                  metas := (Hook.executeInstruction programId args.source.key args.mint.key
                    args.destination.key args.authority.key args.amount).metas ++
                      [Solanalib.Specs.Core.Instruction.accountMeta validationKey false false] }
                accounts := [args.source, args.mint, args.destination, args.authority,
                  validationInfo] })

/-- Mint parsing errors bypass all hook requirements. A hook-bearing mint
admits its reached nested scopes before releasing the actual outer mint guard. -/
def MintReady (state : State) (args : Args) (prepared : Prepared) : Prop :=
  ScopeReady true state args.mint (fun during bytes =>
    match unpackMintWithExtensions bytes with
    | .error error => (.error error, during)
    | .ok mint =>
      match hookProgram mint.tlv with
      | none => (.success prepared, during)
      | some programId => addHook during args programId prepared)
    (fun during bytes =>
      match unpackMintWithExtensions bytes with
      | .error _ => True
      | .ok mint =>
        match hookProgram mint.tlv with
        | none => True
        | some programId => HookReady during args programId prepared)

/-- Admission is checked along the actual branches of the ordinary preparation. It
requires only selected reads and reached releases, not amount/decimal bounds,
whole AccountInfo validity, opaque-provider execution or a finished preparation. -/
def PreparationReady (state : State) (args : Args) : Prop :=
  match Instruction.transferChecked .either {
    programId := args.tokenProgramId
    source := args.source.key
    mint := args.mint.key
    destination := args.destination.key
    authority := args.authority.key
    signers := []
    amount := args.amount
    decimals := args.decimals } with
  | .error _ => True
  | .ok instruction =>
    let base := {
      instruction := instruction
      accounts := [args.source, args.mint, args.destination, args.authority] : Prepared }
    AddMultisigReady state args ∧
      AfterSuccess (addMultisig state args base) fun after prepared => MintReady after args prepared

/-- The admitted data-length getter preserves its finite value or borrow-panic
branch, including the actual acquire/read/release sequence. -/
theorem dataLen_not_malformed {state : State} {info : Account} (ready : DataLenReady state info) :
    (AccountInfo.observe .dataLen state info).1 ≠ .malformed := by
  cases acquired : Borrow.acquire state info.data .shared AccountInfo.View.whole with
  | mk result during =>
    cases result with
    | error failure =>
      cases failure <;>
        simp [DataLenReady, acquired, AccountInfo.observe, AccountInfo.Observation.handle] at *
    | ok guard =>
      have checked : AccountInfo.tryBorrow .shared info.data state = (.ok guard, during) := by
        simp [AccountInfo.tryBorrow, acquired, Except.mapError]
      obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current
        (by simpa only [DataLenReady, acquired] using ready) checked
      simp [AccountInfo.observe, AccountInfo.Observation.handle, acquired, current,
        AccountInfo.Observation.project, Borrow.release_after_acquire acquired]

/-- The owner short circuit and the admitted getter both retain their actual
ordinary value or panic. -/
theorem isMultisig_not_malformed {state : State} {info : Account}
    (ready : MultisigReady state info) : (isMultisig state info).1 ≠ .malformed := by
  unfold MultisigReady at ready
  split at ready
  · rename_i bypass
    simp [isMultisig, bypass]
  · rename_i reached
    simp only [isMultisig, reached]
    have safe := dataLen_not_malformed ready
    cases observed : AccountInfo.observe .dataLen state info with
    | mk result after =>
      cases result <;> simp_all

/-- Invalid multisig length and signer count are preserved as ordinary error
and panic, respectively; neither is a malformed mathematical read. -/
theorem multisigKeys_not_malformed (bytes : Bytes) : multisigKeys bytes ≠ .malformed := by
  unfold multisigKeys
  split
  · simp
  · dsimp only
    split <;> simp

/-- Selected multisig admission supplies both actual reads. The stateless
key-selection body releases its fresh guard without an extra cleanup gate. -/
theorem addMultisig_not_malformed {state : State} {args : Args} {prepared : Prepared}
    (ready : AddMultisigReady state args) : (addMultisig state args prepared).1 ≠ .malformed := by
  unfold addMultisig
  apply bind_not_malformed (isMultisig_not_malformed ready.1) ready.2
  intro after recognized admitted
  cases recognized with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at admitted ⊢
    apply withData_not_malformed (bodyReady := fun _ _ => True)
    · apply scopeReady_of_unchanged admitted (fun _ _ => True.intro)
      intro during bytes
      cases multisigKeys bytes <;> simp [bind]
    · intro during bytes _
      have safe := multisigKeys_not_malformed bytes
      cases keys : multisigKeys bytes <;> simp_all [bind]

/-- Each actual collection prefix retains its checked error and real cleanup.
Successful acquisition continues at the actual state of the newly issued guard. -/
theorem collectDataAux_not_malformed {state : State} {infos : List Account}
    {guards : List Borrow.Guard} {observations : Hook.Observations}
    (ready : CollectReady state infos guards) :
    (collectDataAux state infos guards observations).1 ≠ .malformed := by
  induction infos generalizing state guards observations with
  | nil => simp [collectDataAux]
  | cons info rest ih =>
    rcases ready with ⟨dataReady, later⟩
    have safe := borrowData_not_malformed (checked := true) dataReady
    cases acquired : borrowData true state info with
    | mk result during =>
      cases result with
      | success borrowed =>
        simpa only [collectDataAux, acquired] using
          ih (observations := observations ++ [(info.key, some borrowed.bytes)])
            (by simpa only [acquired] using later)
      | error failure =>
        simp only [collectDataAux, acquired]
        rw [cleanup_preserves (by simpa only [acquired] using later)]
        simp
      | panic reason =>
        simp only [collectDataAux, acquired]
        rw [cleanup_preserves (by simpa only [acquired] using later)]
        simp
      | malformed => simp [acquired] at safe

/-- Pure resolution never invents a malformed guard or data observation. -/
theorem resolveFailure_not_malformed (failure : Hook.ResolveFailure) :
    resolveFailure failure ≠ .malformed := by
  cases failure <;> simp [resolveFailure]

/-- Extra-meta admission is consumed at every reached collection and release,
including resolver failure and recursive account lookup paths. -/
theorem addExtraMetas_not_malformed {crypto : Address.Crypto} {additional : List Account}
    {extras : List Hook.ExtraMeta} {state : State} {prepared : Prepared}
    (ready : ExtraReady crypto additional extras state prepared) :
    (addExtraMetas crypto additional extras state prepared).1 ≠ .malformed := by
  induction extras generalizing state prepared with
  | nil => simp [addExtraMetas]
  | cons extra rest ih =>
    unfold addExtraMetas
    apply bind_not_malformed (collectDataAux_not_malformed ready.1) ready.2
    intro during collected admitted
    apply bind_not_malformed (ready := fun after item =>
      let reduced := Hook.deescalate prepared.instruction.metas item
      match additional.find? (fun info => info.key == reduced.key) with
      | none => True
      | some info => ExtraReady crypto additional rest after {
          instruction := { prepared.instruction with metas := prepared.instruction.metas ++
            [reduced] }
          accounts := prepared.accounts ++ [info] })
    · rw [cleanup_preserves admitted.1]
      cases resolved : Hook.resolve crypto prepared.instruction.data
          prepared.instruction.programId collected.2 extra with
      | ok item => simp
      | error failure => exact resolveFailure_not_malformed failure
    · exact admitted.2
    · intro after item remaining
      cases found : additional.find? (fun info =>
          info.key == (Hook.deescalate prepared.instruction.metas item).key) with
      | none => simp [found]
      | some info =>
        simp only [found] at remaining ⊢
        exact ih remaining

/-- Every admitted validation scope preserves parsing errors and all nested
extra-account outcomes, then performs its actual outer release. -/
theorem addHook_not_malformed {state : State} {args : Args} {programId : Solanalib.Runtime.Pubkey}
    {prepared : Prepared} (ready : HookReady state args programId prepared) :
    (addHook state args programId prepared).1 ≠ .malformed := by
  cases pda : Address.tryFind ⟨args.crypto, [Hook.extraAccountMetasSeed, args.mint.key.bytes],
    programId⟩ with
  | none => simp [addHook, pda]
  | some found =>
    rcases found with ⟨validationKey, bump⟩
    cases program : args.additional.find? (fun info => info.key == programId) with
    | none => simp [addHook, pda, program]
    | some programInfo =>
      cases validation : args.additional.find? (fun info => info.key == validationKey) with
      | none => simp [addHook, pda, program, validation]
      | some validationInfo =>
        simp only [HookReady, pda, program, validation] at ready
        simp only [addHook, pda, program, validation]
        apply withData_not_malformed ready
        intro during bytes bodyReady
        cases decoded : Hook.decodeValidation bytes with
        | error failure => simp [bind]
        | ok extras =>
          simp only [decoded, bind] at bodyReady ⊢
          have safe := addExtraMetas_not_malformed bodyReady
          split <;> simp_all

/-- The mint input requirement is consumed before reading bytes; each reached
hook and the final actual mint-guard release retain the local result. -/
theorem addMintExtensions_not_malformed {state : State} {args : Args} {prepared : Prepared}
    (ready : MintReady state args prepared) :
    (addMintExtensions state args prepared).1 ≠ .malformed := by
  apply withData_not_malformed ready
  intro during bytes bodyReady
  cases parsed : unpackMintWithExtensions bytes with
  | error failure => simp
  | ok mint =>
    cases hook : hookProgram mint.tlv with
    | none => simp [hook]
    | some programId =>
      simp only [parsed, hook] at bodyReady ⊢
      exact addHook_not_malformed bodyReady

/-- Local readiness rules out the erased preparation branch by composition
of reached primitive reads and releases. It does not assume a completed
preparation or require the external CPI provider to have any finite exit. -/
theorem prepare_not_malformed {state : State} {args : Args}
    (ready : PreparationReady state args) : (prepare state args).1 ≠ .malformed := by
  unfold PreparationReady at ready
  split at ready
  · rename_i error selected
    simp [prepare, selected]
  · rename_i instruction selected
    simp only [prepare, selected]
    exact bind_not_malformed (addMultisig_not_malformed ready.1) ready.2
      (fun _ _ admitted => addMintExtensions_not_malformed admitted)

end Solanalib.Specs.Core.Token.Onchain
