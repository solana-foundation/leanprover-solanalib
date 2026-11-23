/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import SolanalibTest.Conformance.Library.Runtime
import Solanalib.Specs.Pinocchio.Get
import Solanalib.Specs.SolanaSysvar.Get
import Solanalib.Specs.SolanaMsg.Log
import Solanalib.Specs.SolanaProgram.Log
import Solanalib.Specs.SolanaProgram.ReturnData
import Solanalib.Specs.SolanaSha256Hasher.Hashv
import Solanalib.Specs.SolanaCurve25519.Edwards

/-!
# Syscall-backed functions over the shim

Each model takes its syscall (or log sink) as an explicit provider in its family
index. The checker instantiates that provider with the behavior of the shim, as a
function of the shim state (`ShimState`: the unconsumed scripted replies and the
request log), so the decided relation is the registered reference at that index:

* the provider first logs the request in the observable form of the shim (`Logged`,
  the projection of the request of the model onto what the shim records), then
  consumes the next reply, which must answer the same syscall; a reply marked
  `terminate` ends the run with the name of the syscall as terminal reason, and a
  missing or mismatched reply ends it with reason `shim` (no record has one);
* the status of a reply is its return word; a destination value is the memory after
  the call: the bytes of the reply, which the shim copies over the initial content of the
  destination (`none` for `MaybeUninit`, `some default` for the typed
  getters of the SDK); a log sink consumes no reply.

Model request components that the shim cannot observe are not compared: the
initial `MaybeUninit` destination of `sol_get_sysvar` and `sol_sha256` (a request
field of the models, constant `none`). The initial result byte of the curve validation
(the `initialScratch` of the model) is compared with the `result_initial` of the shim.

The getter, hashing and curve references are relations through the provider;
each has a graph lemma here over `Callback.ofFunction` of the shim provider.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Runtime.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

/-! ## Shim state -/

/-- A request as the shim logs it. -/
inductive Logged where
  | getSysvar (id : Solanalib.Runtime.Bytes) (offset length : Nat)
  | typedSysvar (syscall : String)
  | log (bytes : Solanalib.Runtime.Bytes)
  | logData (fields : List Solanalib.Runtime.Bytes)
  | setReturnData (bytes : Solanalib.Runtime.Bytes) (length : Nat)
  | sha256 (fields : List Solanalib.Runtime.Bytes) (count : Nat)
  | sha512 (fields : List Solanalib.Runtime.Bytes)
  | msm (curve count : Nat) (scalars points : List Solanalib.Runtime.Bytes)
  | curveValidate (curve : Nat) (point : Solanalib.Runtime.Bytes) (resultNull : Bool)
    (resultInitial : Option Nat)
  /-- A host-target call of an overridable `program_stubs` function. -/
  | stubGetter (syscall : String)
  | stubLogData (fields : List Solanalib.Runtime.Bytes)
  | stubReturnData (bytes : Solanalib.Runtime.Bytes)
  /-- A model request with no native counterpart on the selected target. -/
  | unobservable (what : String)
  deriving DecidableEq

structure ShimState where
  replies : List Runtime.Reply
  log : List Logged
  deriving DecidableEq

def logged (r : Runtime.Request) : Result Logged := do
  if (r.fields.getObjVal? "target").toOption == some (Json.str "host_stub") then
    match r.syscall with
    | "sol_get_clock_sysvar" | "sol_get_rent_sysvar" => return .stubGetter r.syscall
    | "sol_log_data" => return .stubLogData (← r.slices "fields")
    | "sol_set_return_data" => return .stubReturnData (← r.bytes "bytes")
    | other => throw s!"unexpected host stub {other}"
  match r.syscall with
  | "sol_get_sysvar" => pure (.getSysvar (← r.bytes "sysvar_id") (← r.nat "offset") (← r.nat
    "length"))
  | "sol_get_clock_sysvar" | "sol_get_rent_sysvar" => pure (.typedSysvar r.syscall)
  | "sol_log_" => pure (.log (← r.bytes "bytes"))
  | "sol_log_data" => pure (.logData (← r.slices "fields"))
  | "sol_set_return_data" => do let b ← r.bytes "bytes"; pure (.setReturnData b b.length)
  | "sol_sha256" => do let f ← r.slices "fields"; pure (.sha256 f f.length)
  | "sol_sha512" => pure (.sha512 (← r.slices "fields"))
  | "sol_curve_multiscalar_mul" =>
    pure (.msm (← r.nat "curve_id") (← r.nat "count")
      (← r.slices "scalars") (← r.slices "points"))
  | "sol_curve_validate_point" =>
    let initial ← match ← field r.fields "result_initial" with
      | .null => pure none
      | j => do pure (some (← j.getNat?))
    pure (.curveValidate (← r.nat "curve_id") (← r.bytes "point") (← r.bool "result_null") initial)
  | other => throw s!"unexpected syscall {other}"

def shimState (state : Json) : Result ShimState := do
  let s ← Runtime.syscallsOf state
  pure ⟨s.replies, ← s.log.mapM logged⟩

def replyJson (r : Runtime.Reply) : Json :=
  Json.mkObj ([("syscall", Json.str r.syscall), ("return", natJson r.ret), ("data", bytesJson
    r.data)] ++
    (match r.terminate with | some t => [("terminate", Json.str t)] | none => []))

def loggedJson : Logged → Json
  | .getSysvar id o l => Json.mkObj [("syscall", "sol_get_sysvar"), ("sysvar_id", bytesJson id),
      ("offset", natJson o), ("length", natJson l)]
  | .typedSysvar s => Json.mkObj [("syscall", Json.str s)]
  | .log b => Json.mkObj [("syscall", "sol_log_"), ("bytes", bytesJson b)]
  | .logData f => Json.mkObj [("syscall", "sol_log_data"), ("fields", Json.arr (f.map
    bytesJson).toArray)]
  | .setReturnData b l => Json.mkObj [("syscall", "sol_set_return_data"), ("bytes", bytesJson b),
      ("length", natJson l)]
  | .sha256 f n => Json.mkObj [("syscall", "sol_sha256"), ("fields", Json.arr (f.map
    bytesJson).toArray),
      ("count", natJson n)]
  | .sha512 f => Json.mkObj [("syscall", "sol_sha512"),
      ("fields", Json.arr (f.map bytesJson).toArray)]
  | .msm curve count scalars points => Json.mkObj [("syscall", "sol_curve_multiscalar_mul"),
      ("curve_id", natJson curve), ("count", natJson count),
      ("scalars", Json.arr (scalars.map bytesJson).toArray),
      ("points", Json.arr (points.map bytesJson).toArray)]
  | .curveValidate c p n i => Json.mkObj [("syscall", "sol_curve_validate_point"), (
    "curve_id",
    natJson c),
      ("point", bytesJson p), ("result_null", Json.bool n),
      ("result_initial", match i with | some b => natJson b | none => Json.null)]
  | .stubGetter s => Json.mkObj [("syscall", Json.str s), ("target", "host_stub")]
  | .stubLogData f => Json.mkObj [("syscall", "sol_log_data"), ("target", "host_stub"),
      ("fields", Json.arr (f.map bytesJson).toArray)]
  | .stubReturnData b => Json.mkObj [("syscall", "sol_set_return_data"), ("target",
    "host_stub"),
      ("bytes", bytesJson b)]
  | .unobservable w => Json.mkObj [("unobservable", Json.str w)]

def shimStateJson (s : ShimState) : Json :=
  Json.mkObj [("syscalls", Json.mkObj [("replies", Json.arr (s.replies.map replyJson).toArray),
    ("log", Json.arr (s.log.map loggedJson).toArray)])]

/-- A terminal exit of the shim: its reason (the syscall whose reply was marked `terminate`,
or `shim` for a script error), its detail and the shim state at that point (the reply is
consumed and the request logged before the syscall ends the run). All three are compared. -/
structure ShimTerminal where
  reason : String
  detail : String
  syscalls : ShimState
  deriving DecidableEq

def detailText (j : Json) : String :=
  match j with
  | .str s => s
  | other => other.compress

def shimTerminalJson (t : ShimTerminal) : Json :=
  Json.mkObj [("reason", Json.str t.reason), ("detail", Json.str t.detail),
    ("syscalls", (shimStateJson t.syscalls).getObjValD "syscalls")]

/-- A recorded outcome of a shim case: a terminated exit is read whole (`Runtime.terminated?`),
others through `parseOutcome`; providers here never unwind. -/
def parseShimOutcome {V : Type} (value : Json → Result V) (j : Json) :
    Result (Option (Outcome ShimState V Empty ShimTerminal)) := do
  match ← Runtime.terminated? j with
  | some t =>
    let syscalls ← match t.syscalls with
      | some st => do pure (⟨st.replies, ← st.log.mapM logged⟩ : ShimState)
      | none => throw "terminated outcome without its syscall state"
    pure (some (.terminated ⟨t.reason, detailText t.detail, syscalls⟩))
  | none => parseOutcome value shimState noReason noReason j

/-- Log the request, then consume the reply for `syscall`. -/
def answer {R : Type} (s : ShimState) (request : Logged) (syscall : String)
    (reply : Runtime.Reply → R) : Outcome ShimState R Empty ShimTerminal :=
  match s.replies with
  | r :: rest =>
    let after : ShimState := ⟨rest, s.log ++ [request]⟩
    if r.syscall = syscall then
      match r.terminate with
      | some detail => .terminated ⟨syscall, detail, after⟩
      | none => .returned (reply r) after
    else .terminated ⟨"shim", "script error", s⟩
  | [] => .terminated ⟨"shim", "script error", s⟩

/-- A log sink: the request is logged, no reply is consumed. -/
def logOnly (s : ShimState) (request : Logged) : Outcome ShimState Unit Empty ShimTerminal :=
  .returned () ⟨s.replies, s.log ++ [request]⟩

/-! ## Sysvar getters -/

/-- The bytes of a sysvar value and their decoding. -/
structure Layout (V : Type) where
  size : Nat
  encode : V → Solanalib.Runtime.Bytes
  decode : Solanalib.Runtime.Bytes → V

/-- The destination after the shim copied `written` over its initial content. -/
def destination {V : Type} (layout : Layout V) (initial : Option V) (written :
  Solanalib.Runtime.Bytes) :
    Option V :=
  if layout.size ≤ written.length then some (layout.decode (written.take layout.size))
  else if written.isEmpty then initial
  else initial.map fun v => layout.decode (written ++ (layout.encode v).drop written.length)

def typedName : Solanalib.Runtime.TypedSysvar → String
  | .clock => "sol_get_clock_sysvar"
  | .rent => "sol_get_rent_sysvar"
  | .epochSchedule => "sol_get_epoch_schedule_sysvar"
  | .epochRewards => "sol_get_epoch_rewards_sysvar"
  | .lastRestartSlot => "sol_get_last_restart_slot"
  | .fees => "sol_get_fees_sysvar"

/-- The observation of the shim of a read request, the syscall it calls and the bytes it copies. -/
def readRequest {V : Type} : Sysvar.GetterTarget × Sysvar.ReadRequest V →
    Logged × String × (Solanalib.Runtime.Bytes → Solanalib.Runtime.Bytes)
  | (.solana, ⟨.generic id offset length, _⟩) =>
    (.getSysvar id.bytes offset.toNat length.toNat, "sol_get_sysvar", fun d => d.take length.toNat)
  | (.solana, ⟨.typed kind, _⟩) => (.typedSysvar (typedName kind), typedName kind, id)
  | (.hostStub, _) => (.unobservable "host stub getter", "host stub getter", id)

def readStep {V : Type} (layout : Layout V) (s : ShimState)
    (request : Sysvar.GetterTarget × Sysvar.ReadRequest V) :
    Outcome ShimState (Sysvar.ReadReply V) Empty ShimTerminal :=
  let (observed, syscall, copied) := readRequest request
  answer s observed syscall fun r =>
    ⟨UInt64.ofNat r.ret, destination layout request.2.initial (copied r.data)⟩

/-- A getter index whose provider is the graph of a function. -/
def fnGetterIndex {V S U T : Type} (target : Sysvar.GetterTarget)
    (step : S → Sysvar.GetterTarget × Sysvar.ReadRequest V → Outcome S (Sysvar.ReadReply V) U T) :
    Sysvar.GetterIndex V where
  State := S
  Unwind := U
  Terminal := T
  target := target
  read := Callback.ofFunction step

def getterIndex {V : Type} (layout : Layout V) : Sysvar.GetterIndex V :=
  fnGetterIndex .solana (readStep layout)

def forwardComputed {V S U T : Type} (config : Sysvar.GetterConfig V) :
    Outcome S (Sysvar.ReadReply V) U T → Option (Outcome S (Except ProgramError.Value V) U T)
  | .returned reply after => match config.error reply.status with
    | some e => some (.returned (.error e) after)
    | none => reply.destination.map fun v => .returned (.ok v) after
  | .unwound r s => some (.unwound r s)
  | .terminated r => some (.terminated r)

theorem forward_graph {V S U T : Type} (config : Sysvar.GetterConfig V)
    (exit : Outcome S (Sysvar.ReadReply V) U T) (o : Outcome S (Except ProgramError.Value V) U T) :
    Sysvar.forwardGetter config exit o ↔ forwardComputed config exit = some o := by
  cases exit with
  | returned reply after =>
    cases h : config.error reply.status <;> cases hd : reply.destination <;>
      simp [Sysvar.forwardGetter, forwardComputed, h, hd, eq_comm]
  | unwound r s => simp only [Sysvar.forwardGetter, forwardComputed, Option.some.injEq]; exact
    eq_comm
  | terminated r => simp only [Sysvar.forwardGetter, forwardComputed, Option.some.injEq]; exact
    eq_comm

/-- The getter at a function-provided index is the graph of `forwardComputed` of one step. -/
theorem fn_get_graph {V S U T : Type} (config : Sysvar.GetterConfig V) (target :
  Sysvar.GetterTarget)
    (step : S → Sysvar.GetterTarget × Sysvar.ReadRequest V → Outcome S (Sysvar.ReadReply V) U T)
    (before : S) (o : Outcome S (Except ProgramError.Value V) U T) :
    Sysvar.getterRun config (fnGetterIndex target step) before () o ↔
      forwardComputed config (step before (target, config.request)) = some o := by
  constructor
  · rintro ⟨exit, read, forwarded⟩
    change step before (target, config.request) = exit at read
    subst read
    exact (forward_graph config _ o).mp forwarded
  · intro h
    exact ⟨_, rfl, (forward_graph config _ o).mpr h⟩

/-- `GetterReady` at a function provider: the one reply the provider gives, if it returns,
has an error status or an initialized destination. -/
def readyExitB {V S U T : Type} (config : Sysvar.GetterConfig V) :
    Outcome S (Sysvar.ReadReply V) U T → Bool
  | .returned reply _ => (config.error reply.status).isSome || reply.destination.isSome
  | _ => true

theorem fn_ready_iff {V S U T : Type} (config : Sysvar.GetterConfig V) (target :
  Sysvar.GetterTarget)
    (step : S → Sysvar.GetterTarget × Sysvar.ReadRequest V → Outcome S (Sysvar.ReadReply V) U T)
    (before : S) :
    Sysvar.GetterReady config (fnGetterIndex target step) before ↔
      readyExitB config (step before (target, config.request)) = true := by
  unfold Sysvar.GetterReady
  constructor
  · intro h
    cases e : step before (target, config.request) with
    | returned reply after =>
      have k := h reply after e
      simp only [readyExitB, Bool.or_eq_true]
      cases he : config.error reply.status with
      | some err => exact Or.inl rfl
      | none =>
        obtain ⟨v, hv⟩ := k he
        exact Or.inr (by simp [hv])
    | unwound _ _ => rfl
    | terminated _ => rfl
  · intro h reply after read hnone
    change step before (target, config.request) = .returned reply after at read
    rw [read] at h
    simp only [readyExitB, hnone, Option.isSome_none, Bool.false_or, Option.isSome_iff_exists] at h
    exact h

/-- The precondition of the registered getter family at a function provider, decided. -/
def getterReadyDec {V S U T : Type} (config : Sysvar.GetterConfig V) (target : Sysvar.GetterTarget)
    (step : S → Sysvar.GetterTarget × Sysvar.ReadRequest V → Outcome S (Sysvar.ReadReply V) U T)
    (before : S) :
    Decidable (((Sysvar.getterFamily config).contract (fnGetterIndex target step)).requires before
      ()) :=
  decidable_of_iff _ (fn_ready_iff config target step before).symm

/-- The copied destination over an initialized default is always initialized. -/
theorem destination_isSome {V : Type} (layout : Layout V) (v : V) (written :
  Solanalib.Runtime.Bytes) :
    (destination layout (some v) written).isSome = true := by
  unfold destination
  split
  · rfl
  · split <;> rfl

/-- At the typed getters of the SDK (initial value `some default`) `GetterReady` holds in every shim
state: no record can break it. -/
theorem typed_getter_ready {V : Type} (config : Sysvar.GetterConfig V) (layout : Layout V)
    (kind : Solanalib.Runtime.TypedSysvar) (v : V) (hreq : config.request = ⟨.typed kind, some v⟩)
    (before : ShimState) : Sysvar.GetterReady config (fnGetterIndex .solana (readStep layout))
      before := by
  rw [fn_ready_iff, hreq]
  simp only [readStep, readRequest, answer]
  cases hr : before.replies with
  | nil => rfl
  | cons r rest =>
    by_cases hs : r.syscall = typedName kind
    · simp only [hs, ite_true]
      cases ht : r.terminate with
      | some _ => rfl
      | none => simp only [readyExitB, destination_isSome, Bool.or_true]
    · simp only [hs, ite_false]
      rfl

abbrev GetterOutcome (V : Type) := Outcome ShimState (Except ProgramError.Value V) Empty
  ShimTerminal

def getComputed {V : Type} (config : Sysvar.GetterConfig V) (layout : Layout V) (before :
  ShimState) :
    Option (GetterOutcome V) :=
  forwardComputed config (readStep layout before (.solana, config.request))

theorem get_graph {V : Type} (config : Sysvar.GetterConfig V) (layout : Layout V)
    (before : ShimState) (o : GetterOutcome V) :
    Sysvar.getterRun config (getterIndex layout) before () o ↔ getComputed config layout before =
      some o :=
  fn_get_graph config .solana (readStep layout) before o

/-! ### Values -/

def i64Of (n : Nat) : Int := if n < 2 ^ 63 then n else (n : Int) - 2 ^ 64

def word (b : Solanalib.Runtime.Bytes) (offset : Nat) : Nat := Solanalib.Runtime.leNat
  (Solanalib.Runtime.slice b offset 8)

def clockLayout : Layout Sysvar.Clock where
  size := 40
  encode := Solanalib.Runtime.Clock.encode
  decode := fun b => ⟨word b 0, i64Of (word b 8), word b 16, word b 24, i64Of (word b 32)⟩

def rent102Layout : Layout Sysvar.Rent102 where
  size := 16
  encode := Sysvar.Rent102.encode
  decode := fun b => ⟨UInt64.ofNat (word b 0), UInt64.ofNat (word b 8)⟩

def rent300Layout : Layout Sysvar.Rent300 where
  size := 17
  encode := fun r => Solanalib.Runtime.u64le r.lamportsPerByteYear.toNat ++ Solanalib.Runtime.u64le
    r.thresholdBits.toNat ++
    [r.burnPercent]
  decode := fun b => ⟨UInt64.ofNat (word b 0), UInt64.ofNat (word b 8), b.getD 16 0⟩

def clock (j : Json) : Result Sysvar.Clock := do
  pure ⟨← nat (← field j "slot"), ← asSInt 64 (← field j "epoch_start_timestamp"), ← nat (← field j
    "epoch"),
    ← nat (← field j "leader_schedule_epoch"), ← asSInt 64 (← field j "unix_timestamp")⟩

def clockJson (c : Sysvar.Clock) : Json := Json.mkObj [("slot", natJson c.slot),
  ("epoch_start_timestamp", toJson c.epochStartTimestamp), ("epoch", natJson c.epoch),
  ("leader_schedule_epoch", natJson c.leaderScheduleEpoch), ("unix_timestamp", toJson
    c.unixTimestamp)]

def rent102 (j : Json) : Result Sysvar.Rent102 := do
  pure ⟨← u64 (← field j "lamports_per_byte"), ← asF64Bits (← field j "exemption_threshold")⟩

def rent102Json (r : Sysvar.Rent102) : Json := Json.mkObj [("lamports_per_byte", u64Json
  r.lamportsPerByte),
  ("exemption_threshold", f64BitsJson r.thresholdBits)]

def rent300 (j : Json) : Result Sysvar.Rent300 := do
  pure ⟨← u64 (← field j "lamports_per_byte_year"), ← asF64Bits (← field j "exemption_thres\
    hold"),
    ← u8 (← field j "burn_percent")⟩

def rent300Json (r : Sysvar.Rent300) : Json := Json.mkObj [
  ("lamports_per_byte_year", u64Json r.lamportsPerByteYear),
  ("exemption_threshold", f64BitsJson r.thresholdBits), ("burn_percent", natJson
    r.burnPercent.toNat)]

theorem sdk_clock_ready (before : ShimState) :
    (Solanalib.Specs.SolanaSysvar.clock.Clock.get_contract.contract (getterIndex
      clockLayout)).requires before () :=
  typed_getter_ready Sysvar.sdkClockConfig clockLayout .clock Sysvar.zeroClock rfl before

theorem sdk_rent_ready (before : ShimState) :
    (Solanalib.Specs.SolanaSysvar.rent.Rent.get_contract.contract (getterIndex
      rent300Layout)).requires before () :=
  typed_getter_ready Sysvar.sdkRentConfig rent300Layout .rent Sysvar.defaultRent300 rfl before

/-- The decider is live at the SDK configuration: a provider that returns success without
initializing the destination is rejected (kernel-checked). Recorded SDK states cannot express
it, since the destination of the typed getters starts initialized. -/
theorem sdk_getter_uninitialized_not_ready :
    ¬ Sysvar.GetterReady Sysvar.sdkClockConfig
      (fnGetterIndex (S := Unit) (U := Empty) (T := Empty) .solana fun s _ => .returned ⟨0, none⟩
        s) () := by
  rw [fn_ready_iff]
  decide

/-- A provider that returns success without initializing the destination. -/
def uninitializedStep {V : Type} :
    Unit → Sysvar.GetterTarget × Sysvar.ReadRequest V → Outcome Unit (Sysvar.ReadReply V) Empty
      Empty :=
  fun s _ => .returned ⟨0, none⟩ s

/-- The precondition decision of the SDK getters (`getterReadyDec`, used by their checkers at the
registered contracts) rejects an uninitialized successful reply (kernel-checked). Recorded SDK
states cannot express it: the destination of the typed getters starts initialized
(`typed_getter_ready`). -/
theorem sdk_clock_decider_rejects :
    @decide ((Solanalib.Specs.SolanaSysvar.clock.Clock.get_contract.contract
        (fnGetterIndex .solana (uninitializedStep (V := Sysvar.Clock)))).requires () ())
      (getterReadyDec Sysvar.sdkClockConfig .solana uninitializedStep ()) = false := by
  decide

theorem sdk_rent_decider_rejects :
    @decide ((Solanalib.Specs.SolanaSysvar.rent.Rent.get_contract.contract
        (fnGetterIndex .solana (uninitializedStep (V := Sysvar.Rent300)))).requires () ())
      (getterReadyDec Sysvar.sdkRentConfig .solana uninitializedStep ()) = false := by
  decide

/-- A getter checker: `run` is the registered reference, `getterRun config` by definition;
`ready` decides the `requires` of the registered contract (`GetterReady`) at the shim provider. -/
def getterChecker {V : Type} [DecidableEq V] (function reference : String)
    (config : Sysvar.GetterConfig V) (run : FamilyRun (Sysvar.getterFamily config))
    (evaluated : run = Sysvar.getterRun config) (ready : ShimState → Bool)
    (layout : Layout V) (value : Json → Result V) (render : V → Json) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  decidesRequires := [reference]
  check := fun c => do
    let before ← shimState c.state
    asUnit c.args
    let recorded ← parseShimOutcome (asExcept programError value) c.outcome
    return withRequires "GetterReady" (ready before) <|
      decideOptGraph (S := ShimState) (V := Except ProgramError.Value V) (U := Empty) (T :=
        ShimTerminal)
      (run (getterIndex layout) before ()) (getComputed config layout before)
      (fun o => evaluated ▸ get_graph config layout before o) recorded
      (outcomeJson shimStateJson (exceptJson programErrorJson render) emptyJson shimTerminalJson)

def pinClockGet102 : Checker :=
  getterChecker "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get"
    "Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_run" Sysvar.pinClockConfig
    Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_run rfl
    (fun before => @decide ((Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_contract.contract
      (getterIndex clockLayout)).requires before ())
      (getterReadyDec Sysvar.pinClockConfig .solana (readStep clockLayout) before)) clockLayout
        clock clockJson

def pinRentGet102 : Checker :=
  getterChecker "<pinocchio::sysvars::rent::Rent as pinocchio::sysvars::Sysvar>::get"
    "Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.get_run" Sysvar.pinRent102Config
    Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.get_run rfl
    (fun before => @decide
      ((Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.get_contract.contract
      (getterIndex rent102Layout)).requires before ())
      (getterReadyDec Sysvar.pinRent102Config .solana (readStep rent102Layout) before))
        rent102Layout rent102 rent102Json

def pinClockGet111 : Checker :=
  getterChecker "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get"
    "Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_run" Sysvar.pinClockConfig
    Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_run rfl
    (fun before => @decide ((Solanalib.Specs.Pinocchio.sysvars.clock.Clock.get_contract.contract
      (getterIndex clockLayout)).requires before ())
      (getterReadyDec Sysvar.pinClockConfig .solana (readStep clockLayout) before)) clockLayout
        clock clockJson

def sdkClockGet : Checker :=
  getterChecker "solana_sysvar::clock::<impl solana_sysvar::Sysvar for \
    solana_clock::Clock>::get"
    "Solanalib.Specs.SolanaSysvar.clock.Clock.get_run" Sysvar.sdkClockConfig
    Solanalib.Specs.SolanaSysvar.clock.Clock.get_run rfl
    (fun before => @decide ((Solanalib.Specs.SolanaSysvar.clock.Clock.get_contract.contract
      (getterIndex clockLayout)).requires before ())
      (getterReadyDec Sysvar.sdkClockConfig .solana (readStep clockLayout) before)) clockLayout
        clock clockJson

def sdkRentGet : Checker :=
  getterChecker "solana_sysvar::rent::<impl solana_sysvar::Sysvar for \
    solana_rent::Rent>::get"
    "Solanalib.Specs.SolanaSysvar.rent.Rent.get_run" Sysvar.sdkRentConfig
    Solanalib.Specs.SolanaSysvar.rent.Rent.get_run rfl
    (fun before => @decide ((Solanalib.Specs.SolanaSysvar.rent.Rent.get_contract.contract
      (getterIndex rent300Layout)).requires before ())
      (getterReadyDec Sysvar.sdkRentConfig .solana (readStep rent300Layout) before)) rent300Layout
        rent300 rent300Json

/-! ## Logging and return data -/

def eventLogged : Log.Event → Logged
  | .text b => .log b
  | .data f => .logData f
  | .stdoutLine _ => .unobservable "stdout line"
  | .stubData _ => .unobservable "host stub data"

def logIndex : Solanalib.Specs.SolanaMsg.LogIndex where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  target := .solana
  sink := Callback.ofFunction fun s e => logOnly s (eventLogged e)

def dataIndex : Solanalib.Specs.SolanaProgram.log.DataIndex where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  target := .solana
  sink := Callback.ofFunction fun s e => logOnly s (eventLogged e)

def returnDataLogged : ReturnData.Request → Logged
  | .solana data length => .setReturnData data length.toNat
  | .hostStub _ => .unobservable "host stub return data"

def returnDataIndex : ReturnData.Index where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  target := .solanaOS
  provider := Callback.ofFunction fun s r => logOnly s (returnDataLogged r)

abbrev UnitOutcome := Outcome ShimState Unit Empty ShimTerminal

theorem sol_log_graph (before : ShimState) (message : String) (o : UnitOutcome) :
    Solanalib.Specs.SolanaMsg.sol_log_run logIndex before message o ↔
      logOnly before (.log (Log.utf8Bytes message)) = o := Iff.rfl

theorem sol_log_data_graph (before : ShimState) (fields : List Solanalib.Runtime.Bytes) (o :
  UnitOutcome) :
    Solanalib.Specs.SolanaProgram.log.sol_log_data_run dataIndex before fields o ↔
      logOnly before (.logData fields) = o := Iff.rfl

theorem set_return_data_graph (before : ShimState) (data : Solanalib.Runtime.Bytes) (o :
  UnitOutcome) :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model returnDataIndex before data o ↔
      logOnly before (.setReturnData data (UInt64.ofNat data.length).toNat) = o := Iff.rfl

def unitOutcomeJson : UnitOutcome → Json := outcomeJson shimStateJson (fun _ => Json.null)
  emptyJson shimTerminalJson

def utf8 (j : Json) : Result String := do
  let b ← asBytes j
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => pure s
  | none => throw "message is not UTF-8"

def solLog : Checker where
  function := "solana_msg::sol_log"
  generics := []
  reference := "Solanalib.Specs.SolanaMsg.sol_log_run"
  decides := ["Solanalib.Specs.SolanaMsg.sol_log_run"]
  check := fun c => do
    let before ← shimState c.state
    let message ← utf8 (← field c.args "message")
    let recorded ← parseShimOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaMsg.sol_log_run logIndex before message)
      (logOnly before (.log (Log.utf8Bytes message))) (sol_log_graph before message) recorded
        unitOutcomeJson

def fieldsOf (j : Json) (key : String) : Result (List Solanalib.Runtime.Bytes) := do
  (← (← field j key).getArr?).toList.mapM asBytes

def solLogData : Checker where
  function := "solana_program::log::sol_log_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.log.sol_log_data_run"
  decides := ["Solanalib.Specs.SolanaProgram.log.sol_log_data_run"]
  check := fun c => do
    let before ← shimState c.state
    let fields ← fieldsOf c.args "fields"
    let recorded ← parseShimOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaProgram.log.sol_log_data_run dataIndex before fields)
      (logOnly before (.logData fields)) (sol_log_data_graph before fields) recorded unitOutcomeJson

def setReturnData : Checker where
  function := "solana_program::program::set_return_data"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.program.set_return_data_model"
  decides := ["Solanalib.Specs.SolanaProgram.program.set_return_data_model"]
  check := fun c => do
    let before ← shimState c.state
    let data ← asBytes (← field c.args "data")
    let recorded ← parseShimOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaProgram.program.set_return_data_model returnDataIndex before data)
      (logOnly before (.setReturnData data (UInt64.ofNat data.length).toNat))
      (set_return_data_graph before data) recorded unitOutcomeJson

/-! ## hashv -/

def hashOutput (written : Solanalib.Runtime.Bytes) (initial : Option Hash.Value) : Option
  Hash.Value :=
  if h : written.length = 32 then some ⟨written, h⟩ else if written.isEmpty then initial else none

def hashStep (s : ShimState) (r : Hash.Syscall.Request) :
    Outcome ShimState Hash.Syscall.Reply Empty ShimTerminal :=
  answer s (.sha256 r.slices r.count.toNat) "sol_sha256" fun reply =>
    ⟨UInt64.ofNat reply.ret, hashOutput (reply.data.take 32) r.output⟩

def hashIndex : Hash.Syscall.Index where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  target := .solanaOS
  provider := Callback.ofFunction hashStep

abbrev HashOutcome := Outcome ShimState Hash.Value Empty ShimTerminal

def hashComputed (before : ShimState) (slices : List Solanalib.Runtime.Bytes) : Option HashOutcome
  :=
  match hashStep before (Hash.Syscall.request slices) with
  | .returned reply after => reply.output.map fun h => .returned h after
  | .unwound r s => some (.unwound r s)
  | .terminated r => some (.terminated r)

theorem hashv_graph (before : ShimState) (slices : List Solanalib.Runtime.Bytes) (o : HashOutcome) :
    Solanalib.Specs.SolanaSha256Hasher.hashv_model hashIndex before slices o ↔
      hashComputed before slices = some o := by
  show Callback.bind (Callback.ofFunction hashStep)
      (fun reply after outcome => ∃ hash, reply.output = some hash ∧ outcome = .returned hash after)
      before (Hash.Syscall.request slices) o ↔ _
  refine (bind_ofFunction_iff (N := Hash.Value) hashStep _ before (Hash.Syscall.request slices)
    o).trans ?_
  unfold hashComputed
  cases hashStep before (Hash.Syscall.request slices) with
  | returned reply after =>
    cases h : reply.output <;> simp [h, eq_comm]
  | unwound r s => simp only [Option.some.injEq]; exact eq_comm
  | terminated r => simp only [Option.some.injEq]; exact eq_comm

/-- `EveryReturnInitialized` at the shim provider: its one reply, if it returns, writes the
whole output. -/
def hashReadyB (before : ShimState) (slices : List Solanalib.Runtime.Bytes) : Bool :=
  match hashStep before (Hash.Syscall.request slices) with
  | .returned reply _ => reply.output.isSome
  | _ => true

theorem hashv_requires_iff (before : ShimState) (slices : List Solanalib.Runtime.Bytes) :
    (Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract hashIndex).requires before slices ↔
      hashReadyB before slices = true := by
  show Hash.Syscall.EveryReturnInitialized (Callback.ofFunction hashStep) before slices ↔ _
  unfold Hash.Syscall.EveryReturnInitialized hashReadyB
  constructor
  · intro h
    cases e : hashStep before (Hash.Syscall.request slices) with
    | returned reply after =>
      obtain ⟨hash, hh⟩ := h reply after e
      simp [hh]
    | unwound _ _ => rfl
    | terminated _ => rfl
  · intro h reply after read
    change hashStep before (Hash.Syscall.request slices) = .returned reply after at read
    rw [read] at h
    exact Option.isSome_iff_exists.mp h

instance (before : ShimState) (slices : List Solanalib.Runtime.Bytes) :
    Decidable ((Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract hashIndex).requires
      before slices) :=
  decidable_of_iff _ (hashv_requires_iff before slices).symm

def hashValue (j : Json) : Result Hash.Value := do
  let b ← bytesN 32 j
  pure ⟨b.val, b.property⟩

def hashv : Checker where
  function := "solana_sha256_hasher::hashv"
  generics := []
  reference := "Solanalib.Specs.SolanaSha256Hasher.hashv_model"
  decides := ["Solanalib.Specs.SolanaSha256Hasher.hashv_model"]
  decidesRequires := ["Solanalib.Specs.SolanaSha256Hasher.hashv_model"]
  check := fun c => do
    let before ← shimState c.state
    let slices ← fieldsOf c.args "slices"
    let recorded ← parseShimOutcome hashValue c.outcome
    return withRequires "EveryReturnInitialized"
      (decide ((Solanalib.Specs.SolanaSha256Hasher.hashv_contract.contract hashIndex).requires
        before slices)) <|
      decideOptGraph (S := ShimState) (V := Hash.Value) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaSha256Hasher.hashv_model hashIndex before slices)
      (hashComputed before slices) (hashv_graph before slices) recorded
      (outcomeJson shimStateJson (fun h => bytesJson h.bytes) emptyJson shimTerminalJson)

/-! ## validate_edwards -/

def validateStep (s : ShimState) (r : Curve.ValidationRequest) :
    Outcome ShimState Curve.ValidationReply Empty ShimTerminal :=
  answer s (.curveValidate r.curve.toNat r.point.val false (some r.initialScratch.toNat))
      "sol_curve_validate_point" fun reply =>
    ⟨UInt64.ofNat reply.ret, r.initialScratch⟩

def validationIndex : Solanalib.Specs.SolanaCurve25519.edwards.target_arch.ValidationIndex where
  State := ShimState
  Unwind := Empty
  Terminal := ShimTerminal
  validate := Callback.ofFunction validateStep

abbrev BoolOutcome := Outcome ShimState Bool Empty ShimTerminal

theorem validate_edwards_graph (before : ShimState) (point : Curve.Point) (o : BoolOutcome) :
    Solanalib.Specs.SolanaCurve25519.edwards.target_arch.validate_edwards_run validationIndex
      before point o ↔
      Outcome.map (fun reply => reply.status == 0) (validateStep before (Curve.edwardsRequest
        point)) = o :=
  Callback.map_ofFunction _ validateStep before (Curve.edwardsRequest point) o

def validateEdwards : Checker where
  function := "solana_curve25519::edwards::target_arch::validate_edwards"
  generics := []
  reference := "Solanalib.Specs.SolanaCurve25519.edwards.target_arch.validate_edwards_run"
  decides := ["Solanalib.Specs.SolanaCurve25519.edwards.target_arch.validate_edwards_run"]
  check := fun c => do
    let before ← shimState c.state
    let point ← bytesN 32 (← field c.args "point")
    let recorded ← parseShimOutcome bool c.outcome
    return decideGraph (S := ShimState) (V := Bool) (U := Empty) (T := ShimTerminal)
      (Solanalib.Specs.SolanaCurve25519.edwards.target_arch.validate_edwards_run validationIndex
        before point)
      (Outcome.map (fun reply => reply.status == 0) (validateStep before (Curve.edwardsRequest
        point)))
      (validate_edwards_graph before point) recorded
      (outcomeJson shimStateJson Json.bool emptyJson shimTerminalJson)

end SolanalibTest.Conformance.Library.Families.Runtime.Syscalls
