/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import Solanalib.Specs.SolanaInstruction.Capabilities
import Solanalib.Specs.SolanaSystemInterface.Capabilities

/-!
# Family `Instructions`: operational instruction constructors

`Instruction::new_with_bincode`/`new_with_wincode` (solana-instruction 3.4.0) and the
operational `create_account`/`transfer` models (solana-system-interface 3.2.0) are relations
over explicit providers: metadata/byte vectors, the serializer, the `unwrap` failure and the
double-unwind policy. When every consulted provider is the graph of a function, the registered
relation is the graph of `runFn`/`allocFn` below (`run_iff`, `allocateRun_iff`), proved from the
definitions of the models.

The checked index (`typesOf Data`): state `()`, metadata and byte "resources" that carry their
own contents (`current` is the identity), errors as their `Debug` text, unwinds as panic
messages and a terminal reason for a destructor panic during unwinding. The serializer is
interpreted per `T` by its bincode/wincode encoding or by the script of the record; `unwrap`
panics with the Rust `called `Result::unwrap()` on an `Err` value: {e:?}` message. Allocation
and the drop of the retained accounts are not observable natively and change nothing in this
state. -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Instructions.Builder

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.InstructionBuilder
open SolanalibTest.Conformance.Library.Borsh

universe u

/-! ## Function forms of the providers, and the graph lemmas -/

/-- The providers consulted by `run`/`allocateRun`, as functions. -/
structure Fns (types : Types) where
  fromList : types.State → List Instruction.Meta →
    Outcome types.State types.MetaResource types.Unwind types.Terminal
  drop : types.State → types.MetaResource → Outcome types.State Unit types.Unwind types.Terminal
  serialize : types.State → Format × types.Data →
    Outcome types.State (Except types.Error types.ByteResource) types.Unwind types.Terminal
  unwrap : types.State → types.Error → Outcome types.State Empty types.Unwind types.Terminal
  double : types.State → types.Unwind → types.Unwind → types.Terminal

/-- The providers `p` consult exactly the functions `f`. -/
structure Fns.Realizes {types : Types} (f : Fns types) (p : Providers types) : Prop where
  fromList : p.metaVec.fromList = Callback.ofFunction f.fromList
  drop : p.metaVec.drop = Callback.ofFunction f.drop
  serialize : p.serialize = Callback.ofFunction f.serialize
  unwrap : p.unwrapFailure = Callback.ofFunction f.unwrap
  double : p.doubleUnwind = fun state first later terminal => terminal = f.double state first later

variable {types : Types}

/-- Serialization, then either the moved result or the non-returning `unwrap`. -/
def rawFn (f : Fns types) (format : Format) (args : Args types) (before : types.State) :
    Outcome types.State (Value types) types.Unwind types.Terminal :=
  match f.serialize before (format, args.data) with
  | .returned (.ok data) after => .returned ⟨args.programId, args.accounts, data⟩ after
  | .returned (.error e) after => Outcome.map (fun impossible : Empty => nomatch impossible)
    (f.unwrap after e)
  | .unwound reason state => .unwound reason state
  | .terminated reason => .terminated reason

/-- Unwind protection of the retained accounts vector. -/
def protectFn (f : Fns types) (accounts : types.MetaResource) :
    Outcome types.State (Value types) types.Unwind types.Terminal →
      Outcome types.State (Value types) types.Unwind types.Terminal
  | .returned value state => .returned value state
  | .unwound reason state =>
    match f.drop state accounts with
    | .returned () after => .unwound reason after
    | .unwound later after => .terminated (f.double after reason later)
    | .terminated terminal => .terminated terminal
  | .terminated reason => .terminated reason

def runFn (f : Fns types) (format : Format) (before : types.State) (args : Args types) :
    Outcome types.State (Value types) types.Unwind types.Terminal :=
  protectFn f args.accounts (rawFn f format args before)

def allocFn (f : Fns types) (format : Format) (before : types.State) (args : AllocateArgs types) :
    Outcome types.State (Value types) types.Unwind types.Terminal :=
  match f.fromList before args.accounts with
  | .returned accounts after => runFn f format after ⟨args.programId, args.data, accounts,
    args.providers⟩
  | .unwound reason state => .unwound reason state
  | .terminated reason => .terminated reason

theorem rawRun_iff (f : Fns types) (format : Format) (args : Args types) (h : f.Realizes
  args.providers)
    (before : types.State) (pending : Outcome types.State (Value types) types.Unwind
      types.Terminal) :
    rawRun types format args before () pending ↔ rawFn f format args before = pending := by
  simp only [rawRun, rawFn, Callback.bind, h.serialize, h.unwrap, Callback.ofFunction]
  constructor
  · rintro ⟨intermediate, hi, hm⟩
    subst hi
    revert hm
    cases f.serialize before (format, args.data) with
    | returned result state =>
      cases result with
      | ok data => intro hm; exact hm.symm
      | error e => intro hm; exact (Callback.map_ofFunction _ _ _ _ _).mp hm
    | unwound reason state => intro hm; exact hm.symm
    | terminated reason => intro hm; exact hm.symm
  · intro hp
    refine ⟨_, rfl, ?_⟩
    revert hp
    cases f.serialize before (format, args.data) with
    | returned result state =>
      cases result with
      | ok data => intro hp; exact hp.symm
      | error e => intro hp; exact (Callback.map_ofFunction _ _ _ _ _).mpr hp
    | unwound reason state => intro hp; exact hp.symm
    | terminated reason => intro hp; exact hp.symm

theorem onUnwind_iff (f : Fns types) (p : Providers types) (h : f.Realizes p)
    (accounts : types.MetaResource)
    (pending final : Outcome types.State (Value types) types.Unwind types.Terminal) :
    Owned.onUnwind p.doubleUnwind [p.metaVec.dropAction accounts] pending final ↔
      protectFn f accounts pending = final := by
  cases pending with
  | returned value state => exact eq_comm
  | terminated reason => exact eq_comm
  | unwound reason state =>
    simp only [Owned.onUnwind, Owned.cleanup, Owned.VectorOps.dropAction, h.drop, h.double,
      Callback.ofFunction, protectFn]
    constructor
    · rintro ⟨dropped, hd, hm⟩
      subst hd
      revert hm
      cases f.drop state accounts with
      | returned u after => cases u; intro hm; exact hm.symm
      | unwound later after => rintro ⟨t, ht, hf⟩; rw [hf, ht]
      | terminated t => intro hm; exact hm.symm
    · intro hp
      refine ⟨_, rfl, ?_⟩
      revert hp
      cases f.drop state accounts with
      | returned u after => cases u; intro hp; exact hp.symm
      | unwound later after => intro hp; exact ⟨_, rfl, hp.symm⟩
      | terminated t => intro hp; exact hp.symm

/-- The registered constructor relation, at function-form providers, is the graph of `runFn`. -/
theorem run_iff (f : Fns types) (format : Format) (before : types.State) (args : Args types)
    (h : f.Realizes args.providers) (o : Outcome types.State (Value types) types.Unwind
      types.Terminal) :
    run types format before args o ↔ runFn f format before args = o := by
  constructor
  · rintro ⟨pending, hraw, hprotect⟩
    rw [rawRun_iff f format args h] at hraw
    subst hraw
    exact (onUnwind_iff f args.providers h args.accounts _ o).mp hprotect
  · intro hrun
    exact ⟨_, (rawRun_iff f format args h before _).mpr rfl,
      (onUnwind_iff f args.providers h args.accounts _ o).mpr hrun⟩

/-- `vec![...]` allocation followed by the constructor, as the graph of `allocFn`. -/
theorem allocateRun_iff (f : Fns types) (format : Format) (before : types.State)
    (args : AllocateArgs types) (h : f.Realizes args.providers)
    (o : Outcome types.State (Value types) types.Unwind types.Terminal) :
    allocateRun types format before args o ↔ allocFn f format before args = o := by
  simp only [allocateRun, allocFn, Callback.bind, h.fromList, Callback.ofFunction]
  constructor
  · rintro ⟨intermediate, hi, hm⟩
    subst hi
    revert hm
    cases f.fromList before args.accounts with
    | returned accounts after => intro hm; exact (run_iff f format after _ h o).mp hm
    | unwound reason state => intro hm; exact hm.symm
    | terminated reason => intro hm; exact hm.symm
  · intro hp
    refine ⟨_, rfl, ?_⟩
    revert hp
    cases f.fromList before args.accounts with
    | returned accounts after => intro hp; exact (run_iff f format after _ h o).mpr hp
    | unwound reason state => intro hp; exact hp.symm
    | terminated reason => intro hp; exact hp.symm

/-! ## The checked index -/

abbrev Meta := Instruction.Meta

/-- The `Debug`-text error of the serializer, unwrapped by the constructor. -/
def unwrapMessage (e : String) : String := "called `Result::unwrap()` on an `Err` value: " ++ e

/-- Rust aborts when a destructor panics during unwinding. Never reached here: drops return. -/
def doublePanic : String := "panic in a destructor during cleanup"

/-- Vectors whose resource is their contents. Only `fromList`, `drop` and `current` are
consulted by these constructors; the operations they never call unwind. -/
def contentsVec (Element : Type) : Owned.VectorOps Unit Element (List Element) String String where
  current := fun _ values => some values
  empty := fun s => ([], s)
  withCapacity := Callback.ofFunction fun s _ => .returned [] s
  fromList := Callback.ofFunction fun s values => .returned values s
  push := Callback.ofFunction fun s _ => .unwound "push is not called by these constructors" s
  extend := Callback.ofFunction fun s _ => .unwound "extend is not called by these \
    constructors" s
  drop := Callback.ofFunction fun s _ => .returned () s

abbrev typesOf (Data : Type) : Types := ⟨Unit, Data, List Meta, Solanalib.Runtime.Bytes, String,
  String, String⟩

abbrev Encode (Data : Type) := Format → Data → Outcome Unit (Except String Solanalib.Runtime.Bytes)
  String String

def providers {Data : Type} (encode : Encode Data) : Providers (typesOf Data) where
  metaVec := contentsVec Meta
  byteVec := contentsVec UInt8
  serialize := Callback.ofFunction fun _ (format, data) => encode format data
  unwrapFailure := Callback.ofFunction fun s e => .unwound (unwrapMessage e) s
  doubleUnwind := fun _ _ _ terminal => terminal = doublePanic

def fns {Data : Type} (encode : Encode Data) : Fns (typesOf Data) where
  fromList := fun s values => .returned values s
  drop := fun s _ => .returned () s
  serialize := fun _ (format, data) => encode format data
  unwrap := fun s e => .unwound (unwrapMessage e) s
  double := fun _ _ _ => doublePanic

theorem fns_realizes {Data : Type} (encode : Encode Data) : (fns encode).Realizes (providers
  encode) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Records -/

abbrev Out (Data : Type) := Outcome Unit (Value (typesOf Data)) String String

def valueOf (j : Json) : Result (Instruction.OwnedValue (List Meta) Solanalib.Runtime.Bytes) := do
  pure ⟨← keyField j "program_id", ← asList metaOf (← field j "accounts"), ← asBytes (← field j
    "data")⟩

def valueJson (v : Instruction.OwnedValue (List Meta) Solanalib.Runtime.Bytes) : Json :=
  instructionJson ⟨v.programId, v.metas, v.data⟩

def outJson {Data : Type} : Out Data → Json
  | .returned v () => returnedJson (valueJson v) Json.null
  | .unwound reason () => Json.mkObj [("exit", "unwound"), ("reason", Json.str reason), (
    "state",
    Json.null)]
  | .terminated reason => Json.mkObj [("exit", "terminated"), ("reason", Json.str reason)]

instance : DecidableEq (Instruction.OwnedValue (List Meta) Solanalib.Runtime.Bytes) := fun a b =>
  if h : a.programId = b.programId ∧ a.metas = b.metas ∧ a.data = b.data then
    isTrue (by cases a; cases b; simp only at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl, rfl⟩)

def recorded {Data : Type} (j : Json) : Result (Option (Out Data)) :=
  parseOutcome valueOf asUnit (fun r => some r) noReason j

/-! ## solana-instruction 3.4.0 `new_with_bincode` / `new_with_wincode` -/

theorem new_with_bincode_evaluated {Data : Type} (encode : Encode Data) (args : Args (typesOf Data))
    (h : args.providers = providers encode) (o : Out Data) :
    Solanalib.Specs.SolanaInstruction.Instruction.new_with_bincode_run (typesOf Data) () args o ↔
      runFn (fns encode) .bincode () args = o :=
  run_iff (fns encode) .bincode () args (h ▸ fns_realizes encode) o

theorem new_with_wincode_evaluated {Data : Type} (encode : Encode Data) (args : Args (typesOf Data))
    (h : args.providers = providers encode) (o : Out Data) :
    Solanalib.Specs.SolanaInstruction.Instruction.new_with_wincode_run (typesOf Data) () args o ↔
      runFn (fns encode) .wincode () args = o :=
  run_iff (fns encode) .wincode () args (h ▸ fns_realizes encode) o

/-- A `T` at which a constructor is recorded: its argument parser and serializer encoding. -/
structure DataTy where
  rust : String
  Data : Type
  parse : Json → Result Data
  encode : Encode Data

/-- Program id, data and accounts of a constructor record. -/
def builderArgs (t : DataTy) (j : Json) : Result (Solanalib.Runtime.Pubkey × t.Data × List Meta) :=
  do
  pure (← keyField j "program_id", ← t.parse (← field j "data"), ← asList metaOf (← field j
    "accounts"))

def newWithBincodeChecker (t : DataTy) : Checker where
  function := "solana_instruction::Instruction::new_with_bincode"
  generics := [("T", t.rust)]
  reference := "Solanalib.Specs.SolanaInstruction.Instruction.new_with_bincode_run"
  decides := ["Solanalib.Specs.SolanaInstruction.Instruction.new_with_bincode_run"]
  check := fun c => do
    asUnit c.state
    let (programId, data, accounts) ← builderArgs t c.args
    let a : Args (typesOf t.Data) := ⟨programId, data, accounts, providers t.encode⟩
    pure (decideGraph _ (runFn (fns t.encode) .bincode () a)
      (new_with_bincode_evaluated t.encode a rfl) (← recorded c.outcome) outJson)

def newWithWincodeChecker (t : DataTy) : Checker where
  function := "solana_instruction::Instruction::new_with_wincode"
  generics := [("T", t.rust)]
  reference := "Solanalib.Specs.SolanaInstruction.Instruction.new_with_wincode_run"
  decides := ["Solanalib.Specs.SolanaInstruction.Instruction.new_with_wincode_run"]
  check := fun c => do
    asUnit c.state
    let (programId, data, accounts) ← builderArgs t c.args
    let a : Args (typesOf t.Data) := ⟨programId, data, accounts, providers t.encode⟩
    pure (decideGraph _ (runFn (fns t.encode) .wincode () a)
      (new_with_wincode_evaluated t.encode a rfl) (← recorded c.outcome) outJson)

/-- The test serializer script (`ScriptedSerialize` in the drivers). -/
inductive Scripted where
  | emit (bytes : Solanalib.Runtime.Bytes)
  | fail (message : String)
  | panic (message : String)

def scripted (j : Json) : Result Scripted :=
  match j.getObjVal? "emit", j.getObjVal? "fail", j.getObjVal? "panic" with
  | .ok b, _, _ => do pure (.emit (← asBytes b))
  | _, .ok m, _ => do pure (.fail (← m.getStr?))
  | _, _, .ok m => do pure (.panic (← m.getStr?))
  | _, _, _ => throw s!"unknown serializer script {j.compress}"

/-- `u64`: eight little-endian bytes in both formats. -/
def u64Ty : DataTy := ⟨"u64", UInt64, u64Parse, fun _ n => .returned (.ok (Solanalib.Runtime.u64le
  n.toNat)) ()⟩

/-- `Vec<u8>`: a `u64` length prefix and the bytes, in the default configurations of both formats.
-/
def vecU8Ty : DataTy := ⟨"alloc::vec::Vec<u8>", Solanalib.Runtime.Bytes, asBytes,
  fun _ b => .returned (.ok (Solanalib.Runtime.u64le b.length ++ b)) ()⟩

/-- The scripted serializer. `fail` errors are rendered as the `Debug` text of each format. -/
def scriptedTy (rust : String) (failure : Format → String → String) : DataTy :=
  ⟨rust, Scripted, scripted, fun format s => match s with
    | .emit b => .returned (.ok b) ()
    | .fail m => .returned (.error (failure format m)) ()
    | .panic m => .unwound m ()⟩

/-! ## solana-system-interface 3.2.0 operational constructors -/

open Solanalib.Specs.SolanaSystemInterface.instruction

def opTypes : OperationalTypes := ⟨Unit, List Meta, Solanalib.Runtime.Bytes, String, String, String⟩

theorem opTypes_builder : opTypes.builder = typesOf SystemData := rfl

/-- The serializer interpretation: the tagged little-endian encoding of `SystemData`, which is the
encoding of the two `SystemInstruction` variants in both bincode and wincode. -/
def systemEncode : Encode SystemData := fun _ d => .returned (.ok d.bytes) ()

theorem create_account_operational_evaluated (format : Format) (source : CreateAccountArgs)
    (o : Out SystemData) :
    create_account_operational_run opTypes () ⟨source, format, providers systemEncode⟩ o ↔
      allocFn (fns systemEncode) format () (createAccountAllocation opTypes ⟨source, format,
        providers systemEncode⟩) = o :=
  allocateRun_iff (fns systemEncode) format () _ (fns_realizes systemEncode) o

theorem transfer_operational_evaluated (format : Format) (source : TransferArgs) (o : Out
  SystemData) :
    transfer_operational_run opTypes () ⟨source, format, providers systemEncode⟩ o ↔
      allocFn (fns systemEncode) format () (transferAllocation opTypes ⟨source, format, providers
        systemEncode⟩) = o :=
  allocateRun_iff (fns systemEncode) format () _ (fns_realizes systemEncode) o

def createAccountArgs (j : Json) : Result CreateAccountArgs := do
  pure ⟨← keyField j "from", ← keyField j "to", ← natField j "lamports" 64, ← natField j
    "space" 64,
    ← keyField j "owner"⟩

def transferArgs (j : Json) : Result TransferArgs := do
  pure ⟨← keyField j "from", ← keyField j "to", ← natField j "lamports" 64⟩

def formatName : Format → String
  | .bincode => "bincode"
  | .wincode => "wincode"

def createAccountOperationalChecker (format : Format) : Checker where
  function := "solana_system_interface::instruction::create_account"
  generics := []
  reference := "Solanalib.Specs.SolanaSystemInterface.instruction.create_account_operationa\
    l_run"
  decides := ["Solanalib.Specs.SolanaSystemInterface.instruction.create_account_operational\
    _run"]
  check := fun c => do
    asUnit c.state
    let source ← createAccountArgs c.args
    pure (decideGraph _ _ (create_account_operational_evaluated format source) (← recorded
      c.outcome) outJson)

def transferOperationalChecker (format : Format) : Checker where
  function := "solana_system_interface::instruction::transfer"
  generics := []
  reference := "Solanalib.Specs.SolanaSystemInterface.instruction.transfer_operational_run"
  decides := ["Solanalib.Specs.SolanaSystemInterface.instruction.transfer_operational_run"]
  check := fun c => do
    asUnit c.state
    let source ← transferArgs c.args
    pure (decideGraph _ _ (transfer_operational_evaluated format source) (← recorded c.outcome)
      outJson)

end SolanalibTest.Conformance.Library.Families.Instructions.Builder
