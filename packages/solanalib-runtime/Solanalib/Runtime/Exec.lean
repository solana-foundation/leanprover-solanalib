/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.System
public import Solanalib.Runtime.LoaderEffects

@[expose] public section

/-!
# Execution of instructions

The runtime layer R of the report: instruction semantics as a relation
`ProcInstr W ts f r`, which holds when processing instruction `f` in transaction state
`ts` can end in `r`.
The relation is defined together with the run of a program and with the runtime answers
to its events, since a CPI runs its callee through `ProcInstr` again.

An application program is the set of its runs (`Program`): the sequences of events it can
produce, each with the reply it received, and a final exit or fault.
An implementation semantics or an explicit behavior contract supplies this set.
`Invoke` accepts a run when every reply is the reply of the runtime, and its result is
the read-back on exit 0, the error of the exit code, or the error of a failing step.

Compute is outside the model: `RunProgram.compute` and `Invoke.compute` let every
instruction and every step end with a compute error. This is the nondeterministic
abort that stands for runs cut off by the meter.

See the [model report](../../README.md#model-report) for program execution, and the
[current source justification](../../source-notes/agave-4.3.2.md#execution-and-commit)
for the correspondence conditions and the abstraction of intermediate error states.
-/

namespace Solanalib.Runtime

/-- An event of a program run. -/
inductive Event where
  /-- A load of `n` bytes at a VM address of the input region. -/
  | load (addr n : Nat)
  /-- A store at a VM address of the input region. -/
  | store (addr : Nat) (bs : Bytes)
  /-- A syscall. -/
  | sys (req : SysReq)
  deriving Repr

/-- The reply that the runtime gives to an event. -/
inductive Reply where
  | bytes (bs : Bytes)
  | unit
  | sys (ans : SysAns)
  deriving Repr

/-- The end of a run: an exit with the value of r0, or a fault of the VM outside the input
region and outside syscalls (stack, heap, division by zero, invalid instruction). -/
inductive Final where
  | exit (r0 : Nat)
  | fault
  deriving DecidableEq, Repr

/-- A run of a program. -/
structure Run where
  steps : List (Event × Reply)
  final : Final

/-- The entry registers: r1 holds `MM_INPUT_START`, and r2 the VM address of the
instruction data when the profile sets it. Agave 4.3.2 sets both in
`program-runtime/src/vm.rs::execute`; see
[serialization](../../source-notes/agave-4.3.2.md#serialization-and-read-back). -/
structure Entry where
  r1 : Nat
  r2 : Option Nat
  deriving DecidableEq, Repr

/-- A loaded program: the runs it can produce from its entry registers, for the replies
recorded in the run. -/
def Program := Entry → Run → Prop

/-- The program that admits every run, which stands for a program about which nothing
is known. Its behaviors are exactly those that the runtime checks admit. -/
def anyProgram : Program := fun _ _ => True

/-- The builtin programs. -/
inductive Builtin where
  | system
  /-- The compute budget program, which does nothing at execution
  (`solana-compute-budget-program`). -/
  | computeBudget
  /-- A builtin whose effects the model leaves open within the runtime checks: the
  management instructions of the loaders, the vote, stake, config, address lookup table
  and zk proof programs. -/
  | unmodelled (id : Pubkey)
  deriving DecidableEq, Repr

/-- Concrete builtin meanings are assigned only to their actual program ids.
The identity of an otherwise opaque builtin is retained explicitly. -/
def Builtin.ValidAt (key : Pubkey) : Builtin → Prop
  | .system => key = Ids.systemProgram
  | .computeBudget => key = Ids.computeBudget
  | .unmodelled id => id = key ∧ key ≠ Ids.systemProgram ∧ key ≠ Ids.computeBudget

/-- The mandatory builtins, with any additional registered native programs
represented by their declared opaque meanings. -/
def builtinTable (additional : Pubkey → Bool) (key : Pubkey) : Option Builtin :=
  if key = Ids.systemProgram then some .system
  else if key = Ids.computeBudget then some .computeBudget
  else if additional key then some (.unmodelled key) else none

structure BuiltinsWF (table : Pubkey → Option Builtin) : Prop where
  system : table Ids.systemProgram = some .system
  computeBudget : table Ids.computeBudget = some .computeBudget
  valid : ∀ key builtin, table key = some builtin → builtin.ValidAt key

theorem builtinTable_wf (additional : Pubkey → Bool) : BuiltinsWF (builtinTable additional) := by
  refine ⟨by simp [builtinTable], ?_, ?_⟩
  · have different : Ids.computeBudget ≠ Ids.systemProgram := by decide
    simp [builtinTable, different]
  · intro key builtin chosen
    unfold builtinTable at chosen
    split at chosen
    · rename_i same
      cases chosen
      exact same
    · rename_i notSystem
      split at chosen
      · rename_i same
        cases chosen
        exact same
      · rename_i notCompute
        split at chosen
        · cases chosen
          exact ⟨rfl, notSystem, notCompute⟩
        · cases chosen

/-- An entry of the program cache for a program owned by a BPF loader. -/
inductive ProgramEntry where
  /-- A `Loaded` entry. -/
  | sbf (prog : Program)
  /-- A missing entry or a tombstone: `FailedVerification`, `Closed` or `DelayVisibility`.
  The cache correspondence is an explicit boundary; see
  [execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
  | notDeployed

/-- The environment of the instructions of a transaction: profile, primitives, sysvars,
epoch stakes, heap size and the initial program cache. Transaction-local cache
modifications are carried by `TxState.modifiedPrograms`. -/
structure World where
  prof : Profile
  prims : Prims
  sysvars : Sysvars
  epochStake : Option Pubkey → Nat
  heapSize : Nat
  builtins : Pubkey → Option Builtin
  programs : Pubkey → ProgramEntry

/-- Coherence of the fixed runtime configuration. Program semantics and
cryptographic assumptions remain separate explicit parameters. -/
structure World.WF (world : World) : Prop where
  profile : world.prof.WF
  sysvars : world.sysvars.WF
  rent : world.sysvars.rent = world.prof.rent.toSysvar
  builtins : BuiltinsWF world.builtins

/-- The result of dispatch. -/
inductive Dispatch where
  | builtin (b : Builtin)
  | sbf (abi : Abi) (prog : Program)
  | unsupported

/-- The represented dispatch of `process_executable_chain` in Agave 4.3.2:
the owner of the program account selects the native builtin or the loader, and the
loader executes a `Loaded` entry. The executable flag is not read. Agave 4.3.2
has no loader-v4 builtin; the 3.1.12 branch retains its historical feature gate.
Matching the supplied program cache and native builtin table to the runtime is
an explicit premise; see
[execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
def dispatch (W : World) (ts : TxState) (f : Frame) : Dispatch :=
  let pid := ts.key f.programIdx
  let owner := (ts.acct f.programIdx).owner
  if owner = Ids.nativeLoader then
    match W.builtins pid with
    | some b => .builtin b
    | none => .unsupported
  else if owner = Ids.loaderV4 ∧ !(W.prof.release == .agave_3_1_12 && W.prof.features.loaderV4) then
    .unsupported
  else if owner ∈ Ids.bpfLoaders then
    match ts.modifiedPrograms.lookup pid with
    | some _ => .unsupported
    | none =>
      match W.programs pid with
      | .sbf prog => .sbf (abiOfOwner owner) prog
      | .notDeployed => .unsupported
  else .unsupported

/-- The invocation context of an SBF program. -/
def invCtxOf (W : World) (abi : Abi) (ts : TxState) (f : Frame) : InvCtx :=
  { abi := abi, cfg := W.prof.memConfig, frame := f, layout := layout abi W.prof ts f,
    heapSize := W.heapSize, release := W.prof.release }

/-- The initial invocation state: the serialized input buffer. -/
def invStateOf (W : World) (abi : Abi) (ts : TxState) (f : Frame) : InvState :=
  { ts := ts, buf := serialize abi W.prof ts f, heapPos := 0, logs := [] }

/-- The entry registers of an SBF program. -/
def entryOf (W : World) (abi : Abi) (ts : TxState) (f : Frame) : Entry :=
  { r1 := MM_INPUT_START,
    r2 := if W.prof.instrDataInR2 then some (MM_INPUT_START + instrDataOffset abi W.prof ts f)
      else none }

/-- A setter call of an opaque builtin. -/
inductive SetterOp where
  | lamports (v : Nat)
  | dataFromSlice (d : Bytes)
  | dataLength (n : Nat)
  | owner (o : Pubkey)
  | executable (b : Bool)
  deriving Repr

def applySetter (r : RentParams) : SetterOp → TxState → SetterCtx → Except InstrError TxState
  | .lamports v, ts, sc => setLamports ts sc v
  | .dataFromSlice d, ts, sc => setDataFromSlice ts sc d
  | .dataLength n, ts, sc => setDataLength ts sc n
  | .owner o, ts, sc => setOwner ts sc o
  | .executable b, ts, sc => setExecutable ts r sc b

/-- The judgments of the execution relation:
`procInstr` is `process_instruction` of a frame, `runProgram` the program after push and
dispatch, `havoc` a builtin that the model leaves open, and `invoke` the acceptance of
the rest of a run of an SBF program. -/
inductive Judgment where
  | procInstr (ts : TxState) (f : Frame) (r : Except InstrError TxState)
  | runProgram (ts : TxState) (f : Frame) (r : Except InstrError TxState)
  | havoc (ts : TxState) (f : Frame) (r : Except InstrError TxState)
  | invoke (c : InvCtx) (st : InvState) (evs : List (Event × Reply)) (fin : Final)
      (r : Except InstrError TxState)

/-- The execution relation, one inductive predicate over the judgments, so that one
induction covers instructions, programs, builtins and runs. The invocation context `c`
is bound implicitly in the constructors of runs. -/
inductive Exec (W : World) : Judgment → Prop
  /-- `InvokeContext::process_instruction` in Agave 4.3.2 with a failing push. -/
  | pushFail {ts : TxState} {f : Frame} {e : InstrError} :
      push W.prof ts f = .error e → Exec W (.procInstr ts f (.error e))
  /-- The modeled outcome of `InvokeContext::process_instruction`: push, return-data
  reset, program execution and pop. `resetReturnData` and `afterProgram` document
  the abstraction of intermediate runtime states on errors. -/
  | run {ts ts1 : TxState} {f : Frame} {r : Except InstrError TxState} :
      push W.prof ts f = .ok ts1 → Exec W (.runProgram (resetReturnData ts1) f r) →
      Exec W (.procInstr ts f (afterProgram r))
  | compute {ts : TxState} {f : Frame} {e : InstrError} :
      IsComputeError e → Exec W (.runProgram ts f (.error e))
  | unsupported {ts : TxState} {f : Frame} :
      dispatch W ts f = .unsupported → Exec W (.runProgram ts f (.error .UnsupportedProgramId))
  /-- Program-input serialization can fail before any program trace is run. -/
  | serializationFailed {ts : TxState} {f : Frame} {abi : Abi} {prog : Program} {error :
    InstrError} :
      dispatch W ts f = .sbf abi prog → serializationAccountCheck f = .error error →
      Exec W (.runProgram ts f (.error error))
  | system {ts : TxState} {f : Frame} {r : Except InstrError TxState} :
      dispatch W ts f = .builtin .system → systemProcess W.prof W.prims ts f = some r →
      Exec W (.runProgram ts f r)
  | systemNonce {ts : TxState} {f : Frame} {r : Except InstrError TxState} :
      dispatch W ts f = .builtin .system → systemProcess W.prof W.prims ts f = none →
      Exec W (.havoc ts f r) → Exec W (.runProgram ts f r)
  | computeBudget {ts : TxState} {f : Frame} :
      dispatch W ts f = .builtin .computeBudget → Exec W (.runProgram ts f (.ok ts))
  | unmodelled {ts : TxState} {f : Frame} {k : Pubkey} {r : Except InstrError TxState} :
      dispatch W ts f = .builtin (.unmodelled k) → k ≠ Ids.bpfLoaderUpgradeable →
      Exec W (.havoc ts f r) →
      Exec W (.runProgram ts f r)
  /-- Loader-v3 account operations remain opaque, but every successful return
  includes its mandatory cache write. The generic builtin rule cannot bypass it. -/
  | loaderV3 {ts : TxState} {f : Frame} {bodyResult r : Except InstrError TxState} :
      dispatch W ts f = .builtin (.unmodelled Ids.bpfLoaderUpgradeable) →
      Exec W (.havoc ts f bodyResult) →
      finishLoaderV3 W.sysvars.clock.slot ts f bodyResult = r →
      LoaderV3ResultContract W.sysvars.clock.slot ts f bodyResult →
      Exec W (.runProgram ts f r)
  | sbf {ts : TxState} {f : Frame} {abi : Abi} {prog : Program} {run : Run}
      {r : Except InstrError TxState} :
      dispatch W ts f = .sbf abi prog → serializationAccountCheck f = .ok () →
      prog (entryOf W abi ts f) run →
      Exec W (.invoke (invCtxOf W abi ts f) (invStateOf W abi ts f) run.steps run.final r) →
      Exec W (.runProgram ts f r)
  /-- A builtin that the model leaves open ends at any point, with success or an error. -/
  | havocDone {ts : TxState} {f : Frame} : Exec W (.havoc ts f (.ok ts))
  | havocFail {ts : TxState} {f : Frame} {e : InstrError} : Exec W (.havoc ts f (.error e))
  /-- The native return-data API permits an explicit program tag, requires no
  instruction-account membership and has no SBF 1024-byte restriction. -/
  | havocReturnData {ts : TxState} {f : Frame} {r : Except InstrError TxState}
      (programId : Pubkey) (data : Bytes) :
      Exec W (.havoc (setNativeReturnData ts programId data) f r) →
      Exec W (.havoc ts f r)
  /-- A setter call of an open builtin through one of its instruction accounts. -/
  | havocSetter {ts ts' : TxState} {f : Frame} {r : Except InstrError TxState} (op : SetterOp)
      (ia : InstrAcct) :
      ia ∈ f.accounts → applySetter W.prof.rent op ts (setterCtxOf ts f.programIdx ia
        W.prof.release) = .ok ts' →
      Exec W (.havoc ts' f r) → Exec W (.havoc ts f r)
  /-- A native invocation of an open builtin, with the checks of
  `prepare_next_instruction` and PDA signers of the builtin. -/
  | havocInvoke {ts ts' : TxState} {f g : Frame} {r : Except InstrError TxState}
      (ix : CpiInstruction) (seeds : List (List Bytes)) (pdas : List Pubkey) :
      pdaSigners W.prims (ts.key f.programIdx) seeds = .ok pdas →
      prepareCallee ts f ix pdas = .ok g → Exec W (.procInstr ts g (.ok ts')) →
      Exec W (.havoc ts' f r) → Exec W (.havoc ts f r)
  /-- An exit with r0 = 0: read-back. -/
  | exit0 {c : InvCtx} {st : InvState} {r : Except InstrError TxState} :
      readBack c.abi c.cfg c.frame.programIdx st.buf st.ts c.layout c.release = r →
      Exec W (.invoke c st [] (.exit 0) r)
  | exitErr {c : InvCtx} {st : InvState} {n : Nat} :
      n ≠ 0 → Exec W (.invoke c st [] (.exit n) (.error (InstrError.fromU64 n)))
  | fault {c : InvCtx} {st : InvState} : Exec W (.invoke c st [] .fault (.error
    .ProgramFailedToComplete))
  | invCompute {c : InvCtx} {st : InvState} {evs : List (Event × Reply)} {fin : Final} {e :
    InstrError} :
      IsComputeError e → Exec W (.invoke c st evs fin (.error e))
  | load {c : InvCtx} {st : InvState} {a n : Nat} {bs : Bytes} {rest : List (Event × Reply)} {fin :
    Final}
      {r : Except InstrError TxState} :
      loadRegion c st a n = .ok bs → Exec W (.invoke c st rest fin r) →
      Exec W (.invoke c st ((.load a n, .bytes bs) :: rest) fin r)
  | loadFail {c : InvCtx} {st : InvState} {a n : Nat} {rep : Reply} {rest : List (Event × Reply)}
    {fin : Final}
      {e : InstrError} :
      loadRegion c st a n = .error e →
      Exec W (.invoke c st ((.load a n, rep) :: rest) fin (.error e))
  | store {c : InvCtx} {st st' : InvState} {a : Nat} {bs : Bytes} {rest : List (Event × Reply)}
    {fin : Final}
      {r : Except InstrError TxState} :
      storeRegion c st a bs = .ok st' → Exec W (.invoke c st' rest fin r) →
      Exec W (.invoke c st ((.store a bs, .unit) :: rest) fin r)
  | storeFail {c : InvCtx} {st : InvState} {a : Nat} {bs : Bytes} {rep : Reply} {rest : List (Event
    × Reply)}
      {fin : Final} {e : InstrError} :
      storeRegion c st a bs = .error e →
      Exec W (.invoke c st ((.store a bs, rep) :: rest) fin (.error e))
  | unregistered {c : InvCtx} {st : InvState} {req : SysReq} {rep : Reply} {rest : List (Event ×
    Reply)}
      {fin : Final} :
      req.registered W.prof = false →
      Exec W (.invoke c st ((.sys req, rep) :: rest) fin (.error .ProgramFailedToComplete))
  | sys {c : InvCtx} {st st' : InvState} {req : SysReq} {ans : SysAns} {rest : List (Event × Reply)}
      {fin : Final} {r : Except InstrError TxState} :
      req.registered W.prof = true →
      sysStep W.prof W.prims W.sysvars W.epochStake c st req = .ok (ans, st') →
      Exec W (.invoke c st' rest fin r) → Exec W (.invoke c st ((.sys req, .sys ans) :: rest) fin r)
  | sysFail {c : InvCtx} {st : InvState} {req : SysReq} {rep : Reply} {rest : List (Event × Reply)}
      {fin : Final} {e : InstrError} :
      req.registered W.prof = true → (∀ q, req ≠ .invoke q) → req ≠ .remainingComputeUnits →
      sysStep W.prof W.prims W.sysvars W.epochStake c st req = .error e →
      Exec W (.invoke c st ((.sys req, rep) :: rest) fin (.error e))
  | remainingComputeUnits {c : InvCtx} {st : InvState} {v : Nat} {rest : List (Event × Reply)} {fin
    : Final}
      {r : Except InstrError TxState} :
      SysReq.registered W.prof .remainingComputeUnits = true → Exec W (.invoke c st rest fin r) →
      Exec W (.invoke c st ((.sys .remainingComputeUnits, .sys ⟨v, []⟩) :: rest) fin r)
  /-- A successful CPI: preparation, `update_callee_account`, the callee,
  `update_caller_account`, following `cpi_common` in Agave 4.3.2. See
  [CPI](../../source-notes/agave-4.3.2.md#cpi). -/
  | cpi {c : InvCtx} {st st1 st2 : InvState} {req : CpiReq} {prep : CpiPrep} {ts2 : TxState}
      {lens : List (Nat × Nat)} {rest : List (Event × Reply)} {fin : Final}
      {r : Except InstrError TxState} :
      cpiPrepare W.prof W.prims c st.ts req = .ok prep →
      updateCallee W.prof c st prep.translated = .ok st1 →
      Exec W (.procInstr st1.ts prep.callee (.ok ts2)) →
      updateCaller W.prof c { st1 with ts := ts2 } prep.translated = .ok (st2, lens) →
      Exec W (.invoke c st2 rest fin r) →
      Exec W (.invoke c st
        ((.sys (.invoke req), .sys (cpiAnswer st2 req lens prep.translated)) :: rest) fin r)
  | cpiPrepareFail {c : InvCtx} {st : InvState} {req : CpiReq} {rep : Reply} {rest : List (Event ×
    Reply)}
      {fin : Final} {e : InstrError} :
      cpiPrepare W.prof W.prims c st.ts req = .error e →
      Exec W (.invoke c st ((.sys (.invoke req), rep) :: rest) fin (.error e))
  | cpiCalleeSyncFail {c : InvCtx} {st : InvState} {req : CpiReq} {prep : CpiPrep} {rep : Reply}
      {rest : List (Event × Reply)} {fin : Final} {e : InstrError} :
      cpiPrepare W.prof W.prims c st.ts req = .ok prep →
      updateCallee W.prof c st prep.translated = .error e →
      Exec W (.invoke c st ((.sys (.invoke req), rep) :: rest) fin (.error e))
  | cpiCalleeFail {c : InvCtx} {st st1 : InvState} {req : CpiReq} {prep : CpiPrep} {rep : Reply}
      {rest : List (Event × Reply)} {fin : Final} {e : InstrError} :
      cpiPrepare W.prof W.prims c st.ts req = .ok prep →
      updateCallee W.prof c st prep.translated = .ok st1 →
      Exec W (.procInstr st1.ts prep.callee (.error e)) →
      Exec W (.invoke c st ((.sys (.invoke req), rep) :: rest) fin (.error e))
  | cpiCallerSyncFail {c : InvCtx} {st st1 : InvState} {req : CpiReq} {prep : CpiPrep} {ts2 :
    TxState}
      {rep : Reply} {rest : List (Event × Reply)} {fin : Final} {e : InstrError} :
      cpiPrepare W.prof W.prims c st.ts req = .ok prep →
      updateCallee W.prof c st prep.translated = .ok st1 →
      Exec W (.procInstr st1.ts prep.callee (.ok ts2)) →
      updateCaller W.prof c { st1 with ts := ts2 } prep.translated = .error e →
      Exec W (.invoke c st ((.sys (.invoke req), rep) :: rest) fin (.error e))

/-- `InvokeContext::process_instruction` of frame `f` in state `ts`, ending in `r`. -/
abbrev ProcInstr (W : World) (ts : TxState) (f : Frame) (r : Except InstrError TxState) : Prop :=
  Exec W (.procInstr ts f r)

/-- The program of the current instruction, after push and dispatch. -/
abbrev RunProgram (W : World) (ts : TxState) (f : Frame) (r : Except InstrError TxState) : Prop :=
  Exec W (.runProgram ts f r)

/-- An oversized serialized invocation fails without needing a program-run witness. -/
theorem RunProgram.serialization_accounts_exceeded {world : World} {state : TxState}
    {frame : Frame} {abi : Abi} {program : Program}
    (loaded : dispatch world state frame = .sbf abi program)
    (exceeded : MAX_ACCOUNTS_PER_INSTRUCTION < frame.accounts.length) :
    RunProgram world state frame (.error .MaxAccountsExceeded) :=
  Exec.serializationFailed loaded (serializationAccountCheck_exceeded exceeded)

/-- Successful execution of a serialized program necessarily passed its account-count check. -/
theorem RunProgram.serialization_admitted {world : World} {before after : TxState}
    {frame : Frame} {abi : Abi} {program : Program}
    (loaded : dispatch world before frame = .sbf abi program)
    (execution : RunProgram world before frame (.ok after)) :
    serializationAccountCheck frame = .ok () := by
  cases execution with
  | system dispatched _ => cases dispatched.symm.trans loaded
  | systemNonce dispatched _ _ => cases dispatched.symm.trans loaded
  | computeBudget dispatched => cases dispatched.symm.trans loaded
  | unmodelled dispatched _ _ => cases dispatched.symm.trans loaded
  | loaderV3 dispatched _ _ _ => cases dispatched.symm.trans loaded
  | sbf _ admitted _ _ => exact admitted

/-- A successful loader-v3 invocation cannot bypass its required cache write,
regardless of the chosen opaque account effects. -/
theorem RunProgram.loaderV3_cache {world : World} {before after : TxState} {frame : Frame}
    {key : Pubkey} {entry : ModifiedProgram}
    (selected : dispatch world before frame = .builtin (.unmodelled Ids.bpfLoaderUpgradeable))
    (effect : loaderV3CacheEffect world.sysvars.clock.slot before frame = some (key, entry))
    (execution : RunProgram world before frame (.ok after)) :
    after.modifiedPrograms.lookup key = some entry := by
  cases execution with
  | system dispatched _ => cases dispatched.symm.trans selected
  | systemNonce dispatched _ _ => cases dispatched.symm.trans selected
  | computeBudget dispatched => cases dispatched.symm.trans selected
  | unmodelled dispatched different _ =>
    cases dispatched.symm.trans selected
    exact (different rfl).elim
  | loaderV3 _ _ finished _ =>
    obtain ⟨returned, _, rfl⟩ := finishLoaderV3_ok finished
    exact applyLoaderV3Effect_lookup effect
  | sbf dispatched _ _ _ => cases dispatched.symm.trans selected

/-- Both source kinds of transaction-local cache modification reject loader
invocation. The initial loaded program cannot override a more recent write. -/
theorem dispatch_modified {world : World} {state : TxState} {frame : Frame}
    {entry : ModifiedProgram}
    (native : (state.acct frame.programIdx).owner ≠ Ids.nativeLoader)
    (loader : (state.acct frame.programIdx).owner ∈ Ids.bpfLoaders)
    (modified : state.modifiedPrograms.lookup (state.key frame.programIdx) = some entry) :
    dispatch world state frame = .unsupported := by
  simp only [dispatch, native, ite_false]
  split
  · rfl
  · simp [modified]

/-- A builtin that the model leaves open. -/
abbrev Havoc (W : World) (ts : TxState) (f : Frame) (r : Except InstrError TxState) : Prop :=
  Exec W (.havoc ts f r)

/-- The acceptance of the rest of a run of an SBF program, and its result. -/
abbrev Invoke (W : World) (c : InvCtx) (st : InvState) (evs : List (Event × Reply)) (fin : Final)
    (r : Except InstrError TxState) : Prop :=
  Exec W (.invoke c st evs fin r)

/-- The instruction semantics of a frame, the interface C of the report: the outcomes of
processing it as a CPI callee or as a top-level instruction. -/
def InstrSem (W : World) (ts : TxState) (f : Frame) (r : Except InstrError TxState) : Prop :=
  ProcInstr W ts f r

end Solanalib.Runtime
