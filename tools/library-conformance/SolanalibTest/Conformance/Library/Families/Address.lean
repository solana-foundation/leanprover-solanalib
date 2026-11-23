/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.SolanaAddress

/-!
# Family `Address`: solana-address 2.6.0 and 2.6.1

Drivers `rust/address-2.6.0`, `rust/address-2.6.1` (selected Solana branch,
`--cfg target_os="solana"`) and `rust/address-2.6.0-host`,
`rust/address-2.6.1-host` (plain host branch, feature `curve25519`).

* Value operations (`new_from_array`, `as_array`, `as_ref`, `to_bytes`,
  `default`, `eq`) are registered as `contract.RealizedBy model`; the checker
  decides `returnsOf model` of the registered `*_model` itself. State is `()`.
* The pure observations `find_program_address_contract` (both versions) and
  `is_on_curve_contract` (2.6.0) take an explicit `Crypto`. They are recorded
  on the host branch, which computes SHA-256 and Ed25519 decompression in
  process; each record carries the `Crypto` as a table over the points the
  model queries (see `rust/address-common/host.rs`), and a record whose table
  misses a query of the search is rejected (`CryptoTable.covers`). `is_on_curve_model` is
  decided through its graph; `find_program_address` through the postcondition of the registered
  contract (`find_post_iff`), because its registered
  reference `findReference` fixes the aborting panic strategy, while a native
  `panic = "unwind"` build records the panic as an unwind, which the contract
  admits (`find_reference_returned_iff` shows that the two agree on every
  returned outcome).
* The selected-Solana syscall families (`try_find_program_address_solana`,
  `find_program_address_solana`, `is_on_curve_solana`) are recorded through
  the `sol_*` shim and decided at the index `shimTypes` (shim state, panic
  payload, shim terminal exit) with the syscalls of the shim as function providers
  (`pdaProvider`, `curveProvider`) and the host panic as `panicProvider`:
  `tryRun_ofFunction`, `findRun_ofFunction` and `curveRun_ofFunction` show
  that the registered run relation of each family then admits exactly the computed
  outcome (`try_*_evaluated`, `find_*_evaluated`, `curve_260_evaluated`). The
  PDA checkers decide the `requires` of each registered contract (`SuccessInitialized`)
  at the record through the `*_admission` theorems and reject a record outside
  it (`decidesRequires`). The requests of the models are compared as the shim logs them:
  seeds (the first `seedCount`), program id, the bump slot before the call,
  curve id, point and the result destination (null, or its byte before the
  call); the uninitialized
  address slot is not observable natively and is not compared.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.SolanaAddress

namespace SolanalibTest.Conformance.Library.Families.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Address (Value Array32 Crypto SearchArgs SearchPanic tryFind)

/-! ## Values -/

def pubkey (j : Json) : Result Value := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkeyJson (k : Value) : Json := bytesJson k.bytes

def array32 (j : Json) : Result Array32 := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"[u8; 32] must have 32 bytes, got \
    {b.length}"

def array32Json (a : Array32) : Json := bytesJson a.val

def asBool (j : Json) : Result Bool := j.getBool?

def selfArg (j : Json) : Result Value := do pubkey (← field j "self")

def pairArg (j : Json) : Result (Value × Value) := do
  pure (← pubkey (← field j "self"), ← pubkey (← field j "other"))

def arrayArg (j : Json) : Result Array32 := do array32 (← field j "array")

/-! ## Value operations: the graph of the registered `*_model` -/

/-- A `RealizedBy` member: decide the graph of its registered model function. -/
def valueChecker {A V : Type} [DecidableEq V] (function reference : String)
    (model : Unit → A → V × Unit) (args : Json → Result A) (value : Json → Result V)
    (render : V → Json) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    decideReturns (returnsOf model) model rfl (← asUnit c.state) (← args c.args) value asUnit render
      (fun _ => Json.null) c.outcome

def NEW_FROM_ARRAY := "solana_address::Address::new_from_array"
def AS_ARRAY := "solana_address::Address::as_array"
def AS_REF := "<solana_address::Address as core::convert::AsRef<[u8]>>::as_ref"
def TO_BYTES := "solana_address::Address::to_bytes"
def DEFAULT := "<solana_address::Address as core::default::Default>::default"
def EQ := "<solana_address::Address as core::cmp::PartialEq>::eq"
def FIND := "solana_address::syscalls::<impl solana_address::Address>::find_program_address"
def TRY_FIND := "solana_address::syscalls::<impl \
  solana_address::Address>::try_find_program_address"
def IS_ON_CURVE := "solana_address::Address::is_on_curve"

namespace V260
open Address

def valueCheckers : List Checker := [
  valueChecker NEW_FROM_ARRAY "Solanalib.Specs.SolanaAddress.Address.new_from_array_model"
    new_from_array_model
    arrayArg pubkey pubkeyJson,
  valueChecker AS_ARRAY "Solanalib.Specs.SolanaAddress.Address.as_array_model" as_array_model
    selfArg array32 array32Json,
  valueChecker AS_REF "Solanalib.Specs.SolanaAddress.Address.as_ref_model" as_ref_model selfArg
    asBytes bytesJson,
  valueChecker TO_BYTES "Solanalib.Specs.SolanaAddress.Address.to_bytes_model" to_bytes_model
    selfArg array32 array32Json,
  valueChecker DEFAULT "Solanalib.Specs.SolanaAddress.Address.default_model" default_model asUnit
    pubkey pubkeyJson,
  valueChecker EQ "Solanalib.Specs.SolanaAddress.Address.eq_model" eq_model pairArg asBool toJson]

end V260

namespace V261
open Address

def valueCheckers : List Checker := [
  valueChecker NEW_FROM_ARRAY "Solanalib.Specs.SolanaAddress.Address.new_from_array_model"
    new_from_array_model
    arrayArg pubkey pubkeyJson,
  valueChecker AS_ARRAY "Solanalib.Specs.SolanaAddress.Address.as_array_model" as_array_model
    selfArg array32 array32Json,
  valueChecker AS_REF "Solanalib.Specs.SolanaAddress.Address.as_ref_model" as_ref_model selfArg
    asBytes bytesJson,
  valueChecker TO_BYTES "Solanalib.Specs.SolanaAddress.Address.to_bytes_model" to_bytes_model
    selfArg array32 array32Json,
  valueChecker DEFAULT "Solanalib.Specs.SolanaAddress.Address.default_model" default_model asUnit
    pubkey pubkeyJson,
  valueChecker EQ "Solanalib.Specs.SolanaAddress.Address.eq_model" eq_model pairArg asBool toJson]

end V261

/-! ## Pure observations over an explicit `Crypto` (host branch) -/

/-- The recorded `Crypto` table: SHA-256 digests and curve answers at the
points the model queries. Every digest and every point has 32 bytes. -/
structure CryptoTable where
  sha256 : List (Solanalib.Runtime.Bytes × Solanalib.Runtime.Bytes)
  onCurve : List (Solanalib.Runtime.Bytes × Bool)

/-- The decided `Crypto`: the table, and outside it an empty digest that is
on the curve (the bump fails). -/
def CryptoTable.crypto (t : CryptoTable) : Crypto :=
  ⟨{ sha256 := fun b => (t.sha256.lookup b).getD [],
     onCurve := fun b => (t.onCurve.lookup b).getD true }⟩

/-- The same table with the opposite answer outside it: an empty digest that
is off the curve (the bump succeeds). Used only to detect a missed query. -/
def CryptoTable.cryptoOpen (t : CryptoTable) : Crypto :=
  ⟨{ sha256 := fun b => (t.sha256.lookup b).getD [],
     onCurve := fun b => (t.onCurve.lookup b).getD false }⟩

/-- Whether the table answers every query of the PDA search at these inputs.
The two `Crypto`s agree on the table, so the searches agree up to the first
query outside it. There `cryptoOpen` stops at that bump (an empty digest is
never a table point, as every point has 32 bytes), while `crypto` either
stops at a later bump or fails. So the two results are equal exactly when no
query misses the table. A miss therefore rejects the record whatever its exit,
not only when the native call returned. -/
def CryptoTable.covers (t : CryptoTable) (seeds : List Solanalib.Runtime.Bytes) (programId : Value)
  : Bool :=
  decide (tryFind ⟨t.crypto, seeds, programId⟩ = tryFind ⟨t.cryptoOpen, seeds, programId⟩)

def pairOf {α β : Type} (a : Json → Result α) (b : Json → Result β) (j : Json) : Result (α × β) :=
  do
  match (← j.getArr?).toList with
  | [x, y] => pure (← a x, ← b y)
  | _ => throw s!"expected a pair, got {j.compress}"

def cryptoTable (j : Json) : Result CryptoTable := do
  let sha ← (← (← field j "sha256").getArr?).toList.mapM (pairOf asBytes asBytes)
  let curve ← (← (← field j "on_curve").getArr?).toList.mapM (pairOf asBytes asBool)
  unless sha.all (·.2.length == 32) && curve.all (·.1.length == 32) do
    throw "a Crypto table digest or curve point does not have 32 bytes"
  pure ⟨sha, curve⟩

def asU8 (j : Json) : Result UInt8 := do pure (UInt8.ofNat (← asUInt 8 j))

def foundJson (r : Value × UInt8) : Json :=
  Json.mkObj [("address", pubkeyJson r.1), ("bump", toJson r.2.toNat)]

def asFound (j : Json) : Result (Value × UInt8) := do
  pure (← pubkey (← field j "address"), ← asU8 (← field j "bump"))

/-- The panic of `find_program_address` after a failed search; the native
payload is the fixed panic-site message of the model. -/
def searchPanic (reason : String) : Option SearchPanic :=
  if reason = Solanalib.Specs.Core.Address.Syscall.panicMessage then some .noViableProgramAddress
    else none

abbrev SearchOutcome := Outcome Unit (Value × UInt8) SearchPanic SearchPanic

def searchOutcomeJson : SearchOutcome → Json
  | .returned r () => returnedJson (foundJson r) Json.null
  | .unwound _ () => Json.mkObj [("exit", "unwound"),
      ("reason", Json.str Solanalib.Specs.Core.Address.Syscall.panicMessage), ("state", Json.null)]
  | .terminated _ => Json.mkObj [("exit", "terminated"),
      ("reason", Json.str Solanalib.Specs.Core.Address.Syscall.panicMessage)]

/-- Executable form of the pure search postcondition `Address.findPost`. -/
def findPostB (args : SearchArgs) : SearchOutcome → Bool
  | .returned r _ => decide (tryFind args = some r)
  | .unwound .noViableProgramAddress _ => (tryFind args).isNone
  | .terminated .noViableProgramAddress => (tryFind args).isNone

theorem findPostB_iff (args : SearchArgs) (o : SearchOutcome) :
    Solanalib.Specs.Core.Address.findPost args o ↔ findPostB args o = true := by
  cases o with
  | returned r s => simp [Solanalib.Specs.Core.Address.findPost, findPostB]
  | unwound p s => cases p; simp [Solanalib.Specs.Core.Address.findPost, findPostB,
    Option.isNone_iff_eq_none]
  | terminated p => cases p; simp [Solanalib.Specs.Core.Address.findPost, findPostB,
    Option.isNone_iff_eq_none]

/-- The postconditions of the registered contracts are `findPost` (both versions). -/
theorem find_post_260_evaluated (args : SearchArgs) (o : SearchOutcome) :
    Address.find_program_address_contract.post () args o ↔ findPostB
      args o = true :=
  findPostB_iff args o

theorem find_post_261_evaluated (args : SearchArgs) (o : SearchOutcome) :
    Address.find_program_address_contract.post () args o ↔ findPostB
      args o = true :=
  findPostB_iff args o

/-- On returned outcomes the registered reference and the contract agree. -/
theorem find_reference_returned_iff (args : SearchArgs) (r : Value × UInt8) :
    Address.find_program_address_run () args (.returned r ()) ↔
      Address.find_program_address_contract.post () args (.returned r
        ()) := by
  show _ = Solanalib.Specs.Core.Address.findOutcome args ↔ tryFind args = some r
  unfold Solanalib.Specs.Core.Address.findOutcome
  cases tryFind args with
  | none => simp
  | some v => simp [eq_comm]

/-- The search arguments, with the `Crypto` of the table; the table must answer
every query of the search (`CryptoTable.covers`). -/
def searchArgs (j : Json) : Result SearchArgs := do
  let seeds ← (← (← field j "seeds").getArr?).toList.mapM asBytes
  let programId ← pubkey (← field j "program_id")
  let table ← cryptoTable (← field j "crypto")
  unless table.covers seeds programId do
    throw "the Crypto table misses a point the model queries"
  pure ⟨table.crypto, seeds, programId⟩

/-- Decide `relation recorded` through an executable characterization. -/
def decideBy {O : Type} (relation : O → Prop) (b : O → Bool) (iff : ∀ o, relation o ↔ b o = true)
    (recorded : Option O) (expected : Json) : Verdict :=
  match recorded with
  | some o =>
    have : Decidable (relation o) := decidable_of_iff _ (iff o).symm
    ⟨decide (relation o), expected⟩
  | none => ⟨false, expected⟩

def findObservationChecker
    (post : Unit → SearchArgs → SearchOutcome → Prop)
    (graph : ∀ args o, post () args o ↔ findPostB args o = true) : Checker where
  function := FIND
  generics := []
  reference := "Solanalib.Specs.SolanaAddress.Address.find_program_address_contract"
  decides := ["Solanalib.Specs.SolanaAddress.Address.find_program_address_contract"]
  check := fun c => do
    let _ ← asUnit c.state
    let args ← searchArgs c.args
    let recorded ← parseOutcome asFound asUnit searchPanic noReason c.outcome
    pure (decideBy (post () args) (findPostB args) (graph args) recorded
      (searchOutcomeJson (Solanalib.Specs.Core.Address.findOutcome args)))

/-- `Address::is_on_curve` on the host branch against `is_on_curve_model`
(2.6.0): the table must answer for the address itself. -/
def isOnCurveObservationChecker : Checker where
  function := IS_ON_CURVE
  generics := []
  reference := "Solanalib.Specs.SolanaAddress.Address.is_on_curve_model"
  decides := ["Solanalib.Specs.SolanaAddress.Address.is_on_curve_model"]
  check := fun c => do
    let address ← selfArg c.args
    let table ← cryptoTable (← field c.args "crypto")
    if (table.onCurve.lookup address.bytes).isNone then
      throw "the Crypto table has no curve answer for self"
    decideReturns (returnsOf Address.is_on_curve_model)
      Address.is_on_curve_model rfl (← asUnit c.state) (table.crypto,
        address)
      asBool asUnit toJson (fun _ => Json.null) c.outcome

/-! ## Selected-Solana syscall families at a function provider -/

namespace Syscall
open Solanalib.Specs.Core.Address.Syscall

/-- Executable local decoding: `none` when no result is admitted (status zero
without an initialized address output). -/
def decodeFn (reply : PdaReply) : Option (Option (Value × UInt8)) :=
  if reply.status = 0 then reply.addressOutput.map fun a => some (a, reply.bumpOutput) else some
    none

theorem decodePda_iff (reply : PdaReply) (result : Option (Value × UInt8)) :
    decodePda reply result ↔ decodeFn reply = some result := by
  unfold decodePda decodeFn
  by_cases h : reply.status = 0
  · simp only [h, ↓reduceIte]
    cases reply.addressOutput with
    | none => simp
    | some a => simp [eq_comm]
  · simp [h, eq_comm]

def tryOutcome {S U T : Type} : Outcome S PdaReply U T → Option (Outcome S (Option (Value × UInt8))
  U T)
  | .returned reply after => (decodeFn reply).map fun r => .returned r after
  | .unwound r s => some (.unwound r s)
  | .terminated r => some (.terminated r)

theorem tryRun_ofFunction {S U T : Type} (sys : S → PdaRequest → Outcome S PdaReply U T)
    (before : S) (inputs : PdaInputs) (o : Outcome S (Option (Value × UInt8)) U T) :
    tryRun (Callback.ofFunction sys) before inputs o ↔ tryOutcome (sys before (pdaRequest inputs))
      = some o := by
  unfold tryRun Callback.bind Callback.ofFunction
  constructor
  · rintro ⟨i, hi, h⟩
    subst hi
    cases hs : sys before (pdaRequest inputs) with
    | returned reply after =>
      rw [hs] at h
      obtain ⟨r, hd, rfl⟩ := h
      simp [tryOutcome, (decodePda_iff reply r).1 hd]
    | unwound r s => rw [hs] at h; simp [tryOutcome, h]
    | terminated r => rw [hs] at h; simp [tryOutcome, h]
  · intro h
    refine ⟨_, rfl, ?_⟩
    cases hs : sys before (pdaRequest inputs) with
    | returned reply after =>
      rw [hs] at h
      simp only [tryOutcome, Option.map_eq_some_iff] at h
      obtain ⟨r, hd, rfl⟩ := h
      exact ⟨r, (decodePda_iff reply r).2 hd, rfl⟩
    | unwound r s => rw [hs] at h; simp only [tryOutcome, Option.some.injEq] at h; exact h.symm
    | terminated r => rw [hs] at h; simp only [tryOutcome, Option.some.injEq] at h; exact h.symm

def finishOutcome {S U T : Type} (panic : S → SearchPanic → Outcome S Empty U T)
    (r : Option (Value × UInt8)) (after : S) : Outcome S (Value × UInt8) U T :=
  match r with
  | some v => .returned v after
  | none => Outcome.map (fun impossible : Empty => nomatch impossible) (panic after
    .noViableProgramAddress)

def findOutcome {S U T : Type} (panic : S → SearchPanic → Outcome S Empty U T)
    (o : Outcome S PdaReply U T) : Option (Outcome S (Value × UInt8) U T) :=
  (tryOutcome o).map fun t => Outcome.bind t (finishOutcome panic)

theorem finishFind_ofFunction {S U T : Type} (panic : S → SearchPanic → Outcome S Empty U T)
    (r : Option (Value × UInt8)) (after : S) (o : Outcome S (Value × UInt8) U T) :
    finishFind (Callback.ofFunction panic) r after o ↔ finishOutcome panic r after = o := by
  cases r with
  | some v => simp only [finishFind, finishOutcome]; exact eq_comm
  | none =>
    simp only [finishFind, finishOutcome]
    exact Callback.map_ofFunction _ panic after .noViableProgramAddress o

theorem findRun_ofFunction {S U T : Type} (sys : S → PdaRequest → Outcome S PdaReply U T)
    (panic : S → SearchPanic → Outcome S Empty U T)
    (before : S) (inputs : PdaInputs) (o : Outcome S (Value × UInt8) U T) :
    findRun (Callback.ofFunction sys) (Callback.ofFunction panic) before inputs o ↔
      findOutcome panic (sys before (pdaRequest inputs)) = some o := by
  unfold findRun findOutcome
  constructor
  · rintro ⟨t, ht, h⟩
    rw [(tryRun_ofFunction sys before inputs t).1 ht]
    simp only [Option.map_some, Option.some.injEq]
    cases t with
    | returned r after => exact (finishFind_ofFunction panic r after o).1 h
    | unwound r s => exact h.symm
    | terminated r => exact h.symm
  · intro h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, hb⟩ := h
    refine ⟨t, (tryRun_ofFunction sys before inputs t).2 ht, ?_⟩
    cases t with
    | returned r after => exact (finishFind_ofFunction panic r after o).2 hb
    | unwound r s => exact hb.symm
    | terminated r => exact hb.symm

theorem curveRun_ofFunction {S U T : Type} (sys : S → CurveRequest → Outcome S UInt64 U T)
    (before : S) (address : Value) (o : Outcome S Bool U T) :
    curveRun (Callback.ofFunction sys) before address o ↔
      Outcome.map (fun status => status == 0) (sys before (curveRequest address)) = o :=
  Callback.map_ofFunction _ sys before (curveRequest address) o

/-- Executable form of the admission of the families `SuccessInitialized` at a
function provider. -/
def successInitializedB {S U T : Type} : Outcome S PdaReply U T → Bool
  | .returned reply _ => reply.status != 0 || reply.addressOutput.isSome
  | _ => true

theorem successInitialized_ofFunction {S U T : Type} (sys : S → PdaRequest → Outcome S PdaReply U T)
    (before : S) (inputs : PdaInputs) :
    SuccessInitialized (Callback.ofFunction sys) before inputs ↔
      successInitializedB (sys before (pdaRequest inputs)) = true := by
  unfold SuccessInitialized Callback.ofFunction
  cases hs : sys before (pdaRequest inputs) with
  | returned reply after =>
    simp only [successInitializedB, Bool.or_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists]
    constructor
    · intro h
      by_cases z : reply.status = 0
      · exact Or.inr (h reply after rfl z)
      · exact Or.inl z
    · rintro h reply' after' e z
      cases e
      exact h.resolve_left (fun n => n z)
  | unwound r s =>
    simp only [successInitializedB, iff_true]
    intro reply after e; cases e
  | terminated r =>
    simp only [successInitializedB, iff_true]
    intro reply after e; cases e

/-! ### The `sol_*` test shim as a provider

The family index is `⟨ShimState, String, ShimTerminal⟩`: the state of the shim is
its unconsumed replies and its request log; an unwind carries the Rust panic
payload; a terminal exit carries the reason of the shim (the syscall name), its
detail and the shim state at that point. `pdaProvider` and `curveProvider`
are the syscalls of the shim as functions (test choices, like the borsh writers):
each pops the next reply, logs the request as the shim observes it, and
returns the reply (or terminates, for a reply marked `terminate`). -/

structure ShimReply where
  syscall : String
  ret : UInt64
  data : Solanalib.Runtime.Bytes
  bump : Option UInt8
  terminate : Option String
  deriving DecidableEq

/-- A logged request, as the shim reads it from the arguments of the call. -/
inductive Request where
  /-- `sol_try_find_program_address`: the `seeds_len` seed slices, the
  program id and the bump byte before the call. -/
  | tryFind (seeds : List Solanalib.Runtime.Bytes) (programId : Value) (bump : UInt8)
  /-- `sol_curve_validate_point`: curve id, the 32 point bytes, and the result
  destination (null, or the byte behind it before the call). -/
  | curve (curveId : UInt64) (point : Value) (output : CurveOutput)
  deriving DecidableEq

structure ShimState where
  replies : List ShimReply
  log : List Request
  deriving DecidableEq

structure ShimTerminal where
  reason : String
  detail : String
  syscalls : ShimState
  deriving DecidableEq

def shimTypes : Types := ⟨ShimState, String, ShimTerminal⟩

def TRY_FIND_SYSCALL := "sol_try_find_program_address"
def CURVE_SYSCALL := "sol_curve_validate_point"

/-- The shim writes `min(data.len, 32)` reply bytes to the address output;
only a full write initializes it. -/
def addressOut (data : Solanalib.Runtime.Bytes) : Option Value :=
  if h : 32 ≤ data.length then some ⟨data.take 32, by simp [List.length_take]; omega⟩ else none

def scriptError (st : ShimState) {V : Type} : Outcome ShimState V String ShimTerminal :=
  .terminated ⟨"shim", "script error", st⟩

def pdaProvider (st : ShimState) (req : PdaRequest) : Outcome ShimState PdaReply String
  ShimTerminal :=
  match st.replies with
  | r :: rest =>
    if r.syscall = TRY_FIND_SYSCALL then
      let after : ShimState :=
        ⟨rest, st.log ++ [.tryFind (req.seeds.take req.seedCount.toNat) req.programId
          req.bumpOutput]⟩
      match r.terminate with
      | some detail => .terminated ⟨TRY_FIND_SYSCALL, detail, after⟩
      | none => .returned ⟨r.ret, addressOut r.data, r.bump.getD req.bumpOutput⟩ after
    else scriptError st
  | [] => scriptError st

def curveProvider (st : ShimState) (req : CurveRequest) : Outcome ShimState UInt64 String
  ShimTerminal :=
  match st.replies with
  | r :: rest =>
    if r.syscall = CURVE_SYSCALL then
      let after : ShimState := ⟨rest, st.log ++ [.curve req.curve req.point req.output]⟩
      match r.terminate with
      | some detail => .terminated ⟨CURVE_SYSCALL, detail, after⟩
      | none => .returned r.ret after
    else scriptError st
  | [] => scriptError st

/-- The host panic machinery under `panic = "unwind"`: the message of the panic site as payload, the
shim state unchanged. -/
def panicProvider (st : ShimState) (_ : SearchPanic) : Outcome ShimState Empty String ShimTerminal
  :=
  .unwound panicMessage st

/-! ### The registered families at the shim providers -/

abbrev ShimOutcome (V : Type) := Outcome ShimState V String ShimTerminal

def tryCall (inputs : PdaInputs) : TryCall shimTypes := ⟨inputs, Callback.ofFunction pdaProvider⟩
def findCall (inputs : PdaInputs) : FindCall shimTypes :=
  ⟨tryCall inputs, Callback.ofFunction panicProvider⟩
def curveCall (address : Value) : CurveCall shimTypes := ⟨address, Callback.ofFunction
  curveProvider⟩

theorem try_260_evaluated (before : ShimState) (inputs : PdaInputs) (o : ShimOutcome (Option (Value
  × UInt8))) :
    Address.try_find_program_address_solana_run shimTypes before
      (tryCall inputs) o ↔
      tryOutcome (pdaProvider before (pdaRequest inputs)) = some o :=
  tryRun_ofFunction pdaProvider before inputs o

theorem try_261_evaluated (before : ShimState) (inputs : PdaInputs) (o : ShimOutcome (Option (Value
  × UInt8))) :
    Address.try_find_program_address_solana_run shimTypes before
      (tryCall inputs) o ↔
      tryOutcome (pdaProvider before (pdaRequest inputs)) = some o :=
  tryRun_ofFunction pdaProvider before inputs o

theorem find_260_evaluated (before : ShimState) (inputs : PdaInputs) (o : ShimOutcome (Value ×
  UInt8)) :
    Address.find_program_address_solana_run shimTypes before
      (findCall inputs) o ↔
      findOutcome panicProvider (pdaProvider before (pdaRequest inputs)) = some o :=
  findRun_ofFunction pdaProvider panicProvider before inputs o

theorem find_261_evaluated (before : ShimState) (inputs : PdaInputs) (o : ShimOutcome (Value ×
  UInt8)) :
    Address.find_program_address_solana_run shimTypes before
      (findCall inputs) o ↔
      findOutcome panicProvider (pdaProvider before (pdaRequest inputs)) = some o :=
  findRun_ofFunction pdaProvider panicProvider before inputs o

theorem curve_260_evaluated (before : ShimState) (address : Value) (o : ShimOutcome Bool) :
    Address.is_on_curve_solana_run shimTypes before (curveCall
      address) o ↔
      Outcome.map (fun status => status == 0) (curveProvider before (curveRequest address)) = o :=
  curveRun_ofFunction curveProvider before address o

/-- The admission of the PDA families at the shim provider is the bit the checkers
require (`successInitializedB`): a record outside it is rejected. -/
theorem try_260_admission (before : ShimState) (inputs : PdaInputs) :
    (Address.try_find_program_address_solana_contract.contract
      shimTypes).requires
        before (tryCall inputs) ↔
      successInitializedB (pdaProvider before (pdaRequest inputs)) = true :=
  successInitialized_ofFunction pdaProvider before inputs

theorem try_261_admission (before : ShimState) (inputs : PdaInputs) :
    (Address.try_find_program_address_solana_contract.contract
      shimTypes).requires
        before (tryCall inputs) ↔
      successInitializedB (pdaProvider before (pdaRequest inputs)) = true :=
  successInitialized_ofFunction pdaProvider before inputs

theorem find_260_admission (before : ShimState) (inputs : PdaInputs) :
    (Address.find_program_address_solana_contract.contract
      shimTypes).requires
        before (findCall inputs) ↔
      successInitializedB (pdaProvider before (pdaRequest inputs)) = true :=
  successInitialized_ofFunction pdaProvider before inputs

theorem find_261_admission (before : ShimState) (inputs : PdaInputs) :
    (Address.find_program_address_solana_contract.contract
      shimTypes).requires
        before (findCall inputs) ↔
      successInitializedB (pdaProvider before (pdaRequest inputs)) = true :=
  successInitialized_ofFunction pdaProvider before inputs

/-! ### Record parsing -/

def asU64 (j : Json) : Result UInt64 := do pure (UInt64.ofNat (← asUInt 64 j))

def optField {α : Type} (j : Json) (key : String) (value : Json → Result α) : Result (Option α) :=
  match j.getObjVal? key with
  | .ok v => do pure (some (← value v))
  | .error _ => pure none

def shimReply (j : Json) : Result ShimReply := do
  pure ⟨← (← field j "syscall").getStr?, ← asU64 (← field j "return"), ← asBytes (← field j
    "data"),
    ← optField j "bump" asU8, ← optField j "terminate" (·.getStr?)⟩

/-- `result_null` with `result_initial`: a null pointer has no initial byte. -/
def curveOutput (j : Json) : Result CurveOutput := do
  match ← (← field j "result_null").getBool?, ← field j "result_initial" with
  | true, .null => pure .nullPointer
  | false, .null => throw "a non-null curve result pointer without its initial byte"
  | false, b => pure (.initializedByte (← asU8 b))
  | true, b => throw s!"a null curve result pointer with an initial byte {b.compress}"

def curveOutputFields : CurveOutput → List (String × Json)
  | .nullPointer => [("result_null", toJson true), ("result_initial", Json.null)]
  | .initializedByte b => [("result_null", toJson false), ("result_initial", toJson b.toNat)]

def request (j : Json) : Result Request := do
  match ← (← field j "syscall").getStr? with
  | "sol_try_find_program_address" =>
    pure (.tryFind (← (← (← field j "seeds").getArr?).toList.mapM asBytes) (← pubkey (← field j
      "program_id"))
      (← asU8 (← field j "bump")))
  | "sol_curve_validate_point" =>
    pure (.curve (← asU64 (← field j "curve_id")) (← pubkey (← field j "point")) (← curveOutput j))
  | other => throw s!"the shim logged {other}, which the Address models do not issue"

def shimState (j : Json) : Result ShimState := do
  let s ← field j "syscalls"
  pure ⟨← (← (← field s "replies").getArr?).toList.mapM shimReply,
    ← (← (← field s "log").getArr?).toList.mapM request⟩

def shimReplyJson (r : ShimReply) : Json :=
  Json.mkObj ([("syscall", Json.str r.syscall), ("return", toJson r.ret.toNat), ("data", bytesJson
    r.data)] ++
    (r.bump.map fun b => [("bump", toJson b.toNat)]).getD [] ++
    (r.terminate.map fun t => [("terminate", Json.str t)]).getD [])

def requestJson : Request → Json
  | .tryFind seeds pid bump => Json.mkObj [("syscall", Json.str TRY_FIND_SYSCALL),
      ("seeds", Json.arr (seeds.map bytesJson).toArray), ("program_id", pubkeyJson pid), (
        "bump",
        toJson bump.toNat)]
  | .curve id point output => Json.mkObj ([("syscall", Json.str CURVE_SYSCALL), ("curve_id", toJson
    id.toNat),
      ("point", pubkeyJson point)] ++ curveOutputFields output)

def shimStateJson (s : ShimState) : Json :=
  Json.mkObj [("replies", Json.arr (s.replies.map shimReplyJson).toArray),
    ("log", Json.arr (s.log.map requestJson).toArray)]

def stateJson (s : ShimState) : Json := Json.mkObj [("syscalls", shimStateJson s)]

/-- A recorded outcome of a shim case: `returned`/`unwound` with `state`, or
`terminated` with `reason`, `detail` and `syscalls`. -/
def shimOutcome {V : Type} (value : Json → Result V) (j : Json) : Result (ShimOutcome V) := do
  match ← (← field j "exit").getStr? with
  | "returned" => pure (.returned (← value (← field j "result")) (← shimState (← field j
    "state")))
  | "unwound" => pure (.unwound (← (← field j "reason").getStr?) (← shimState (← field j
    "state")))
  | "terminated" =>
    pure (.terminated ⟨← (← field j "reason").getStr?, ← (← field j "detail").getStr?, ← shimState
      j⟩)
  | other => throw s!"unknown exit {other}"

def shimOutcomeJson {V : Type} (render : V → Json) : ShimOutcome V → Json
  | .returned v s => returnedJson (render v) (stateJson s)
  | .unwound r s => Json.mkObj [("exit", "unwound"), ("reason", Json.str r), ("state", stateJson s)]
  | .terminated t => Json.mkObj [("exit", "terminated"), ("reason", Json.str t.reason),
      ("detail", Json.str t.detail), ("syscalls", shimStateJson t.syscalls)]

/-- `Option` is `null` or `{"some": v}` (README, corpus format). -/
def asOptionFound (j : Json) : Result (Option (Value × UInt8)) :=
  match j with
  | .null => pure none
  | _ => do pure (some (← asFound (← field j "some")))

def optionFoundJson : Option (Value × UInt8) → Json
  | none => Json.null
  | some r => Json.mkObj [("some", foundJson r)]

def pdaInputs (j : Json) : Result PdaInputs := do
  pure ⟨← (← (← field j "seeds").getArr?).toList.mapM asBytes, ← pubkey (← field j
    "program_id")⟩

/-- Decide `relation recorded` given `relation o ↔ computed = some o`. -/
def decideOpt {V : Type} [DecidableEq V] (relation : ShimOutcome V → Prop) (computed : Option
  (ShimOutcome V))
    (graph : ∀ o, relation o ↔ computed = some o) (recorded : ShimOutcome V)
    (render : V → Json) : Verdict :=
  have : Decidable (relation recorded) := decidable_of_iff _ (graph recorded).symm
  ⟨decide (relation recorded),
    match computed with
    | some o => shimOutcomeJson render o
    | none => Json.str "no outcome (status zero without an initialized address)"⟩

/-- Decide the precondition of the family at the record (the `requires` of the registered contract
at `shimTypes`, through its admission theorem); a record outside it
fails. -/
def checkRequires {S U T : Type} (precondition : Prop) (exit : Outcome S PdaReply U T)
    (admission : precondition ↔ successInitializedB exit = true) : Result Unit :=
  have : Decidable precondition := decidable_of_iff _ admission.symm
  if decide precondition then pure ()

else throw "outside the precondition (SuccessInitialized: status zero without an initialized \
      address)"

def tryChecker
    (relation : ShimState → PdaInputs → ShimOutcome (Option (Value × UInt8)) → Prop)
    (graph : ∀ before inputs o, relation before inputs o ↔ tryOutcome (pdaProvider before
      (pdaRequest inputs)) = some o)
    (precondition : ShimState → PdaInputs → Prop)
    (admission : ∀ before inputs,
      precondition before inputs ↔ successInitializedB (pdaProvider before (pdaRequest inputs)) =
        true) :
    Checker where
  function := TRY_FIND
  generics := []
  reference := "Solanalib.Specs.SolanaAddress.Address.try_find_program_address_solana_run"
  decides := ["Solanalib.Specs.SolanaAddress.Address.try_find_program_address_solana_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAddress.Address.try_find_program_address_solan\
    a_run"]
  check := fun c => do
    let before ← shimState c.state
    let inputs ← pdaInputs c.args
    checkRequires (precondition before inputs) _ (admission before inputs)
    pure (decideOpt (relation before inputs) (tryOutcome (pdaProvider before (pdaRequest inputs)))
      (graph before inputs) (← shimOutcome asOptionFound c.outcome) optionFoundJson)

def findChecker
    (relation : ShimState → PdaInputs → ShimOutcome (Value × UInt8) → Prop)
    (graph : ∀ before inputs o,
      relation before inputs o ↔ findOutcome panicProvider (pdaProvider before (pdaRequest inputs))
        = some o)
    (precondition : ShimState → PdaInputs → Prop)
    (admission : ∀ before inputs,
      precondition before inputs ↔ successInitializedB (pdaProvider before (pdaRequest inputs)) =
        true) :
    Checker where
  function := FIND
  generics := []
  reference := "Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run"
  decides := ["Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run"]
  decidesRequires := ["Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_ru\
    n"]
  check := fun c => do
    let before ← shimState c.state
    let inputs ← pdaInputs c.args
    checkRequires (precondition before inputs) _ (admission before inputs)
    pure (decideOpt (relation before inputs) (findOutcome panicProvider (pdaProvider before
      (pdaRequest inputs)))
      (graph before inputs) (← shimOutcome asFound c.outcome) foundJson)

def curveChecker : Checker where
  function := IS_ON_CURVE
  generics := []
  reference := "Solanalib.Specs.SolanaAddress.Address.is_on_curve_solana_run"
  decides := ["Solanalib.Specs.SolanaAddress.Address.is_on_curve_solana_run"]
  check := fun c => do
    let before ← shimState c.state
    let address ← selfArg c.args
    let computed := Outcome.map (fun status => status == 0) (curveProvider before (curveRequest
      address))
    pure (decideOpt (V := Bool)
      (Address.is_on_curve_solana_run shimTypes before (curveCall
        address))
      (some computed) (fun o => (curve_260_evaluated before address o).trans ⟨congrArg some,
        Option.some.inj⟩)
      (← shimOutcome asBool c.outcome) toJson)

def syscallCheckers260 : List Checker :=
  [tryChecker _ (fun before inputs o => try_260_evaluated before inputs o)
     _ (fun before inputs => try_260_admission before inputs),
   findChecker _ (fun before inputs o => find_260_evaluated before inputs o)
     _ (fun before inputs => find_260_admission before inputs),
   curveChecker]

def syscallCheckers261 : List Checker :=
  [tryChecker _ (fun before inputs o => try_261_evaluated before inputs o)
     _ (fun before inputs => try_261_admission before inputs),
   findChecker _ (fun before inputs o => find_261_evaluated before inputs o)
     _ (fun before inputs => find_261_admission before inputs)]

end Syscall

/-! ## Registration -/

def corpora : List (String × List Checker) := [
  ("solana_address_2_6_0_api", V260.valueCheckers ++ Syscall.syscallCheckers260),
  ("solana_address_2_6_1_api", V261.valueCheckers ++ Syscall.syscallCheckers261),
  ("solana_address_2_6_0_host",
    [findObservationChecker Address.find_program_address_contract.post
      find_post_260_evaluated, isOnCurveObservationChecker]),
  ("solana_address_2_6_1_host",
    [findObservationChecker Address.find_program_address_contract.post
      find_post_261_evaluated])
]

end SolanalibTest.Conformance.Library.Families.Address
