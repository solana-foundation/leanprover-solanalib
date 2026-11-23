/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenViews.Common
import Solanalib.Specs.PinocchioToken2022.Instructions

/-!
# pinocchio-token-2022 0.3.1 checked CPI wrappers (`pinocchio_token_2022.Instructions`)

`TransferChecked::invoke`, `TransferChecked::invoke_signed` and
`CloseAccount::invoke_signed` are families over the state, its AccountView
pool, the raw header bytes and the opaque invocation provider. The index of the checker
(`testTypes`): the state is the pool, the four raw header
bytes of each account (`is_signer`, `is_writable`, `executable`, first padding byte, exactly as
the driver wrote them into the loader buffer) and the request log of the shim; the
provider is the shim (`sol_invoke_signed_c` appends the request and returns;
`invoke_signed_unchecked` ignores its return code). The registered relations
are decided through `directV2_graph`, from the `directV2_iff` of the model.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.TokenViews.Request

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Request
open Solanalib.Specs.Core.CpiRequest.Checked
open SolanalibTest.Conformance.Library.Families.TokenViews
open Solanalib.Specs.Core.Token.Request (Types Transfer Close transferRequest closeRequest)

abbrev Sent := CpiRequest.Request Descriptor

structure TestState where
  pool : AccountView.State
  headers : List RawHeader
  shim : ShimState Sent

def zeroHeader : RawHeader := ⟨0, 0, 0, 0⟩

abbrev testTypes : Token.Request.Types where
  State := TestState
  pool := TestState.pool
  Unwind := Empty
  Terminal := TerminalObs
  rawHeader := fun s h => s.headers.getD h.cell zeroHeader

/-- The value-level CPI request a prepared request denotes in a pool: what
the shim reads through the pointers of the descriptors (its Booleans mean "byte is
nonzero"), and the copied raw header of each descriptor: the three flag bytes and
the copied padding byte (`copiedPadding`), which the shim logs as raw bytes. -/
def sentObsOf (pool : AccountView.State) (s : Sent) : CallObs × RawHeaders :=
  (⟨⟨s.instruction.programId.bytes, s.instruction.metas.map (fun m =>
      ⟨m.key.bytes, m.signerByte != 0, m.writableByte != 0⟩), s.instruction.data⟩,
    s.accounts.map (fun d => accountInfoOf pool d.account d.dataLen d.rentEpoch (d.isSigner != 0)
      (d.isWritable != 0) (d.executable != 0)),
    s.signers⟩,
   s.accounts.map fun d => d.copiedPadding.map fun p =>
     [d.isSigner.toNat, d.isWritable.toNat, d.executable.toNat, p.toNat])

/-- The observation of the shim of a provider state over a pool. -/
def sentShimObs (pool : AccountView.State) (shim : ShimState Sent) : ShimObs :=
  ⟨shim.replies, shim.log.map (sentObsOf pool)⟩

/-- The shim as the opaque provider (`shimInvoke`). -/
def logInvoke : TestState → Sent → Outcome TestState Unit Empty TerminalObs := fun s sent =>
  match shimInvoke (sentShimObs s.pool) s.shim sent with
  | .returned () shim => .returned () { s with shim }
  | .unwound r shim => .unwound r { s with shim }
  | .terminated r => .terminated r

/-- The executable form of `directV2` at `testTypes` with the shim. -/
def computedV2 (before : TestState) (request : CpiRequest.Request AccountView.Handle) :
    Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs :=
  if request.accounts.length < request.instruction.metas.length then
    .returned (.error .NotEnoughAccountKeys) before
  else
    match prepareDirectV2 (testTypes.pool before) (testTypes.rawHeader before)
        request.instruction.metas request.accounts with
    | .error error => .returned (.error error) before
    | .ok accounts => Outcome.map (fun _ => Except.ok ())
        (logInvoke before ⟨request.instruction, accounts, request.signers⟩)

theorem directV2_graph (before : TestState) (request : CpiRequest.Request AccountView.Handle)
    (o : Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs) :
    directV2 testTypes.pool testTypes.rawHeader (Callback.ofFunction logInvoke) before request o ↔
      some (computedV2 before request) = some o := by
  rw [directV2_iff]
  refine Iff.trans ?_ ⟨congrArg some, Option.some.inj⟩
  unfold computedV2
  split
  · exact eq_comm
  · cases prepareDirectV2 (testTypes.pool before) (testTypes.rawHeader before)
        request.instruction.metas request.accounts with
    | error e => exact eq_comm
    | ok accounts => exact Callback.map_ofFunction _ _ _ _ _

/-! ## Registered references at `testTypes` -/

open Solanalib.Specs.PinocchioToken2022.instructions

theorem transfer_signed_graph (before : TestState) (transfer : Transfer) (signers : List (List
  Bytes))
    (o : Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs) :
    transfer_checked.TransferChecked.invoke_signed_reference testTypes before
        ⟨transfer, signers, Callback.ofFunction logInvoke⟩ o ↔
      some (computedV2 before (transferRequest before.pool transfer signers)) = some o := by
  show directV2 testTypes.pool testTypes.rawHeader (Callback.ofFunction logInvoke) before
    (transferRequest (testTypes.pool before) transfer signers) o ↔ _
  exact directV2_graph before _ o

theorem transfer_graph (before : TestState) (transfer : Transfer)
    (o : Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs) :
    transfer_checked.TransferChecked.invoke_reference testTypes before
        ⟨transfer, Callback.ofFunction logInvoke⟩ o ↔
      some (computedV2 before (transferRequest before.pool transfer [])) = some o := by
  show directV2 testTypes.pool testTypes.rawHeader (Callback.ofFunction logInvoke) before
    (transferRequest (testTypes.pool before) transfer []) o ↔ _
  exact directV2_graph before _ o

theorem close_signed_graph (before : TestState) (close : Close) (signers : List (List Bytes))
    (o : Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs) :
    close_account.CloseAccount.invoke_signed_reference testTypes before
        ⟨close, signers, Callback.ofFunction logInvoke⟩ o ↔
      some (computedV2 before (closeRequest before.pool close signers)) = some o := by
  show directV2 testTypes.pool testTypes.rawHeader (Callback.ofFunction logInvoke) before
    (closeRequest (testTypes.pool before) close signers) o ↔ _
  exact directV2_graph before _ o

/-! ## Observations -/

structure StateObs where
  accounts : List AccountObs
  frame : RegionFrame
  shim : ShimObs
  deriving DecidableEq

/-- The observation of a test state: accounts with their raw header bytes. -/
def stateObsOf (s : TestState) : RegionFrame → StateObs := fun frame =>
  ⟨cellsObs s.pool (fun j _ => let h := s.headers.getD j zeroHeader
      (h.isSigner.toNat, h.isWritable.toNat, h.executable.toNat, h.padding.toNat)) 0 s.pool.cells,
    frame, sentShimObs s.pool s.shim⟩

def stateObs (j : Json) : Result StateObs := do
  pure ⟨(← regionOf j).1, (← regionOf j).2, ← shimObs j⟩

def stateObsJson (s : StateObs) : Json := Json.mkObj [("accounts", listJson accountObsJson
  s.accounts),
  ("frame", regionFrameJson s.frame), ("syscalls", shimObsJson s.shim)]

/-- The test state of a record: the raw header bytes from the region (any flag
bytes, a one-byte padding value; the Boolean flags of the model are "byte is
nonzero", which the checked path does not read), the script of the shim and an
empty log. -/
def testState (j : Json) : Result (TestState × RegionFrame) := do
  let (accounts, frame) ← regionOf j
  let parts ← accounts.mapM fun a => do
    unless a.padding < 256 do throw "padding bytes 1..3 are outside the raw header model"
    pure ((a, modelAccount a (a.isSigner != 0) (a.isWritable != 0) (a.executable != 0)),
      (⟨UInt8.ofNat a.isSigner, UInt8.ofNat a.isWritable, UInt8.ofNat a.executable,
        UInt8.ofNat a.padding⟩ : RawHeader))
  let s ← Runtime.syscallsOf j
  unless s.log.isEmpty do throw "the request log before the call must be empty"
  pure (⟨poolOf (parts.map (·.1)), parts.map (·.2), ⟨s.replies, []⟩⟩, frame)

def transfer (j : Json) : Result Transfer := do
  pure ⟨← pubkey (← field j "program_id"), ← handleField j "from", ← handleField j "mint",
    ← handleField j "to", ← handleField j "authority", ← natField j "amount" 64,
    ← natField j "decimals" 8⟩

def close (j : Json) : Result Close := do
  pure ⟨← pubkey (← field j "program_id"), ← handleField j "account",
    ← handleField j "destination", ← handleField j "authority"⟩

def decide2022 (c : Case) (frame : RegionFrame)
    (relation : Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs →
      Prop)
    (computed : Outcome TestState (Except Solanalib.Runtime.InstrError Unit) Empty TerminalObs)
    (graph : ∀ o, relation o ↔ some computed = some o) : Result Verdict := do
  let recorded ← parseShimOutcome (asExcept programError asUnit) stateObs noReason c.outcome
  pure (decideObserved relation (some computed) graph
    (Outcome.observe (fun v _ => v) (fun s => stateObsOf s frame) id id)
    recorded (outcomeJson (exceptObsJson programErrorJson fun _ => Json.null) stateObsJson emptyJson
      terminalObsJson))

def signers (j : Json) : Result (List (List Solanalib.Runtime.Bytes)) := asList (asList asBytes) j

def transferSignedChecker : Checker where
  function :=
    "pinocchio_token_2022::instructions::transfer_checked::TransferChecked::<'_, \
      '_>::invoke_signed"
  generics := []
  reference :=
    "Solanalib.Specs.PinocchioToken2022.instructions.transfer_checked.TransferChecked.invok\
      e_signed_reference"
  decides :=
    ["Solanalib.Specs.PinocchioToken2022.instructions.transfer_checked.TransferChecked.invo\
      ke_signed_reference"]
  check := fun c => do
    let (before, frame) ← testState c.state
    let t ← transfer c.args
    for h in [t.source, t.mint, t.destination, t.authority] do resolves before.pool.cells.length h
    let seeds ← signers (← field c.args "signers")
    decide2022 c frame (transfer_checked.TransferChecked.invoke_signed_reference testTypes before
        ⟨t, seeds, Callback.ofFunction logInvoke⟩)
      (computedV2 before (transferRequest before.pool t seeds)) (transfer_signed_graph before t
        seeds)

def transferChecker : Checker where
  function :=
    "pinocchio_token_2022::instructions::transfer_checked::TransferChecked::<'_, \
      '_>::invoke"
  generics := []
  reference :=
    "Solanalib.Specs.PinocchioToken2022.instructions.transfer_checked.TransferChecked.invok\
      e_reference"
  decides :=
    ["Solanalib.Specs.PinocchioToken2022.instructions.transfer_checked.TransferChecked.invo\
      ke_reference"]
  check := fun c => do
    let (before, frame) ← testState c.state
    let t ← transfer c.args
    for h in [t.source, t.mint, t.destination, t.authority] do resolves before.pool.cells.length h
    decide2022 c frame (transfer_checked.TransferChecked.invoke_reference testTypes before
        ⟨t, Callback.ofFunction logInvoke⟩)
      (computedV2 before (transferRequest before.pool t [])) (transfer_graph before t)

def closeSignedChecker : Checker where
  function :=
    "pinocchio_token_2022::instructions::close_account::CloseAccount::<'_, \
      '_>::invoke_signed"
  generics := []
  reference :=
    "Solanalib.Specs.PinocchioToken2022.instructions.close_account.CloseAccount.invoke_sign\
      ed_reference"
  decides :=
    ["Solanalib.Specs.PinocchioToken2022.instructions.close_account.CloseAccount.invoke_sig\
      ned_reference"]
  check := fun c => do
    let (before, frame) ← testState c.state
    let cl ← close c.args
    for h in [cl.account, cl.destination, cl.authority] do resolves before.pool.cells.length h
    let seeds ← signers (← field c.args "signers")
    decide2022 c frame (close_account.CloseAccount.invoke_signed_reference testTypes before
        ⟨cl, seeds, Callback.ofFunction logInvoke⟩)
      (computedV2 before (closeRequest before.pool cl seeds)) (close_signed_graph before cl seeds)

def checkers : List Checker := [transferChecker, transferSignedChecker, closeSignedChecker]

end SolanalibTest.Conformance.Library.Families.TokenViews.Request
