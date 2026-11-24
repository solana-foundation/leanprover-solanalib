/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenViews.Common
import Solanalib.Specs.PinocchioToken.Instructions

/-!
# pinocchio-token 0.6.0 Batch preparation (`pinocchio_token.Instructions`)

`Batch::new` and the specialized `TransferChecked::new` are total references;
their graphs are decided directly. `IntoBatch::into_batch` and
`Batch::invoke_signed` are families over callbacks: the checker instantiates
the `AsRef` callback and the opaque invocation provider with the function
forms of the scripts of the driver and decides the registered relations through
the graph lemmas `intoBatch_ofFunction` and `invokeSigned_ofFunction`, proved
here from the definitions of the model.

Instantiations (family indices):
- `MultisigSigner = &AccountView`: `as_ref` returns its own account and has no
  effect (`Ambient = Unit`).
- `MultisigSigner = ScriptedSigner`: every `as_ref` appends the id of the signer to
  a log (the ambient state) and then follows the script of the record by call
  number: return account `j`, or panic (unwind) with a fixed message.
- `invoke_signed`: the `sol_invoke_signed_c` of the shim appends the request it
  receives to a log (the ambient state) and returns; its return code is
  ignored by `invoke_signed_unchecked`, so the provider returns unit.

Buffers are pre-initialized by the driver (every slot `some`). Committed
lengths are private fields of `Batch`; the driver reads them from the memory of the value (see the
`batch_lengths` of the driver).
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.PinocchioToken

namespace SolanalibTest.Conformance.Library.Families.TokenViews.Batch

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Batch
open SolanalibTest.Conformance.Library.Families.TokenViews

/-! ## Graph lemmas for function-form callbacks -/

section Graphs

variable {S A V W U T : Type}

theorem bind_graph (run : Callback.Run S A V U T) (runFn : S → A → Outcome S V U T)
    (hrun : ∀ st a i, run st a i ↔ runFn st a = i)
    (next : V → S → Outcome S W U T → Prop) (nextFn : V → S → Outcome S W U T)
    (hnext : ∀ v st o, next v st o ↔ nextFn v st = o) (st : S) (a : A) (o : Outcome S W U T) :
    Callback.bind run next st a o ↔ Outcome.bind (runFn st a) nextFn = o := by
  constructor
  · rintro ⟨i, hi, h⟩
    rw [(hrun st a i).1 hi]
    cases i with
    | returned v s => exact (hnext v s o).1 h
    | unwound r s => exact h.symm
    | terminated r => exact h.symm
  · intro h
    refine ⟨runFn st a, (hrun st a _).2 rfl, ?_⟩
    revert h
    cases runFn st a with
    | returned v s => exact (hnext v s o).2
    | unwound r s => exact Eq.symm
    | terminated r => exact Eq.symm

theorem map_graph (g : V → W) (run : Callback.Run S A V U T) (runFn : S → A → Outcome S V U T)
    (hrun : ∀ st a i, run st a i ↔ runFn st a = i) (st : S) (a : A) (o : Outcome S W U T) :
    Callback.map g run st a o ↔ Outcome.map g (runFn st a) = o :=
  ⟨fun ⟨i, hi, ho⟩ => by rw [(hrun st a i).1 hi]; exact ho, fun ho => ⟨_, (hrun st a _).2 rfl, ho⟩⟩

end Graphs

section Batch

variable {types : Types}

/-- A function-form `as_ref`. -/
abbrev AsRefFn (types : Types) :=
  Context types.Ambient → types.Signer → Outcome (Context types.Ambient) AccountView.Handle
    types.Unwind types.Terminal

theorem framed_ofFunction (f : AsRefFn types) (before : State types.Ambient) (s : types.Signer)
    (i : Outcome (State types.Ambient) AccountView.Handle types.Unwind types.Terminal) :
    framedAsRef (types := types) (Callback.ofFunction f) before s i ↔
      liftContext before (f before.context s) = i :=
  ⟨fun ⟨_, ha, hl⟩ => by rw [ha]; exact hl, fun h => ⟨_, rfl, h⟩⟩

def signerPassFn (f : AsRefFn types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient) :
    State types.Ambient → Nat → List types.Signer →
      Outcome (State types.Ambient) Unit types.Unwind types.Terminal
  | before, _, [] => .returned () before
  | before, offset, s :: rest =>
    Outcome.bind (liftContext before (f before.context s))
      fun h current => signerPassFn f write (write current offset h) (offset + 1) rest

theorem signerPass_ofFunction (f : AsRefFn types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (signers : List types.Signer) (before : State types.Ambient) (offset : Nat)
    (o : Outcome (State types.Ambient) Unit types.Unwind types.Terminal) :
    signerPass (Callback.ofFunction f) write before offset signers o ↔
      signerPassFn f write before offset signers = o := by
  induction signers generalizing before offset o with
  | nil => exact eq_comm
  | cons s rest ih =>
    exact bind_graph (framedAsRef (Callback.ofFunction f))
      (fun st sg => liftContext st (f st.context sg)) (framed_ofFunction f) _ _
      (fun h current o => ih (write current offset h) (offset + 1) o) before s o

def writeAccountsFn (f : AsRefFn types) (before : State types.Ambient)
    (args : Transfer types.Signer) :
    Outcome (State types.Ambient) (Except Error Nat) types.Unwind types.Terminal :=
  let expected := 4 + args.multisigSigners.length
  if before.buffers.accounts.length - before.lengths.accounts < expected then
    .returned (.error .InvalidArgument) before
  else if AccountView.isBorrowed before.context.world args.fromAccount ||
      AccountView.isBorrowed before.context.world args.toAccount then
    .returned (.error .AccountBorrowFailed) before
  else
    Outcome.map (fun _ => Except.ok expected)
      (signerPassFn f writeAccount (writeBaseAccounts before args) (before.lengths.accounts + 4)
        args.multisigSigners)

theorem writeAccounts_ofFunction (f : AsRefFn types) (before : State types.Ambient)
    (args : Transfer types.Signer)
    (o : Outcome (State types.Ambient) (Except Error Nat) types.Unwind types.Terminal) :
    writeAccounts (Callback.ofFunction f) before args o ↔ writeAccountsFn f before args = o := by
  unfold writeAccounts writeAccountsFn
  dsimp only
  split
  · exact eq_comm
  · split
    · exact eq_comm
    · exact map_graph _ (fun current (_ : Unit) => signerPass (Callback.ofFunction f) writeAccount
        current (before.lengths.accounts + 4) args.multisigSigners)
        (fun current _ => signerPassFn f writeAccount current (before.lengths.accounts + 4)
          args.multisigSigners)
        (fun current _ i => signerPass_ofFunction f writeAccount _ current _ i) _ () o

def writeMetasFn (f : AsRefFn types) (before : State types.Ambient)
    (args : Transfer types.Signer) :
    Outcome (State types.Ambient) (Except Error Nat) types.Unwind types.Terminal :=
  let expected := 4 + args.multisigSigners.length
  if before.buffers.instructionAccounts.length - before.lengths.instructionAccounts < expected then
    .returned (.error .InvalidArgument) before
  else
    Outcome.map (fun _ => Except.ok expected)
      (signerPassFn f (fun state offset handle => writeMeta state offset handle true false)
        (writeBaseMetas before args) (before.lengths.instructionAccounts + 4) args.multisigSigners)

theorem writeMetas_ofFunction (f : AsRefFn types) (before : State types.Ambient)
    (args : Transfer types.Signer)
    (o : Outcome (State types.Ambient) (Except Error Nat) types.Unwind types.Terminal) :
    writeMetas (Callback.ofFunction f) before args o ↔ writeMetasFn f before args = o := by
  unfold writeMetas writeMetasFn
  dsimp only
  split
  · exact eq_comm
  · exact map_graph _ (fun current (_ : Unit) => signerPass (Callback.ofFunction f)
      (fun state offset handle => writeMeta state offset handle true false)
      current (before.lengths.instructionAccounts + 4) args.multisigSigners)
      (fun current _ => signerPassFn f (fun state offset handle => writeMeta state offset handle
        true false)
        current (before.lengths.instructionAccounts + 4) args.multisigSigners)
      (fun current _ i => signerPass_ofFunction f _ _ current _ i) _ () o

def afterMetasFn (dataCount accountCount : Nat) (metaResult : Except Error Nat)
    (afterMetas : State types.Ambient) :
    Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal :=
  match metaResult with
  | .error reason => .returned (.error reason) afterMetas
  | .ok metaCount => .returned (.ok ()) (commit afterMetas dataCount accountCount metaCount)

def afterAccountsFn (f : AsRefFn types) (args : Transfer types.Signer) (dataCount : Nat)
    (accountResult : Except Error Nat) (afterAccounts : State types.Ambient) :
    Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal :=
  match accountResult with
  | .error reason => .returned (.error reason) afterAccounts
  | .ok accountCount =>
    Outcome.bind (writeMetasFn f afterAccounts args) (afterMetasFn dataCount accountCount)

/-- The executable form of `intoBatch` for a function-form callback. -/
def intoBatchFn (f : AsRefFn types) (before : State types.Ambient) (args : Transfer types.Signer) :
    Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal :=
  if before.buffers.data.length < before.lengths.data + 2 then
    .returned (.error .InvalidArgument) before
  else
    match writeData before args with
    | (.error reason, afterData) => .returned (.error reason) afterData
    | (.ok dataCount, afterData) =>
      Outcome.bind (writeAccountsFn f afterData args) (afterAccountsFn f args dataCount)

theorem intoBatch_ofFunction (f : AsRefFn types) (before : State types.Ambient)
    (args : Transfer types.Signer)
    (o : Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal) :
    intoBatch (Callback.ofFunction f) before args o ↔ intoBatchFn f before args = o := by
  unfold intoBatch intoBatchFn
  split
  · exact eq_comm
  · cases writeData before args with
    | mk dataResult afterData =>
      cases dataResult with
      | error reason => exact eq_comm
      | ok dataCount =>
        refine bind_graph _ _ (writeAccounts_ofFunction f) _ _ ?_ afterData args o
        intro accountResult afterAccounts next
        cases accountResult with
        | error reason => exact eq_comm
        | ok accountCount =>
          refine bind_graph _ _ (writeMetas_ofFunction f) _ _ ?_ afterAccounts args next
          intro metaResult afterMetas last
          cases metaResult with
          | error reason => exact eq_comm
          | ok metaCount => exact eq_comm

/-- A function-form opaque invocation provider. -/
abbrev InvokeFn (types : Types) :=
  Context types.Ambient → Request → Outcome (Context types.Ambient) Unit types.Unwind types.Terminal

/-- The executable form of `invokeSigned`: `none` when the committed prefixes
do not decode (no request exists and the relation admits no outcome). -/
def invokeComputed (g : InvokeFn types) (before : State types.Ambient) (signers : List (List
  Bytes)) :
    Option (Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal) :=
  (request before signers).map fun sent =>
    Outcome.map (fun _ => Except.ok ()) (liftContext before (g before.context sent))

theorem invokeSigned_ofFunction (g : InvokeFn types) (before : State types.Ambient)
    (signers : List (List Bytes))
    (o : Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal) :
    invokeSigned before ⟨signers, Callback.ofFunction g⟩ o ↔ invokeComputed g before signers = some
      o := by
  unfold invokeSigned invokeComputed
  cases request before signers with
  | none => exact ⟨fun ⟨_, h, _⟩ => (by cases h), fun h => (by cases h)⟩
  | some sent =>
    constructor
    · rintro ⟨s, hs, actual, ha, ho⟩
      cases hs
      rw [← ha] at ho
      exact congrArg some ho
    · intro h
      exact ⟨sent, rfl, _, rfl, Option.some.inj h⟩

end Batch

/-! ## Observations -/

structure MetaObs where
  account : Nat
  isSigner : Bool
  isWritable : Bool
  deriving DecidableEq

def metaObsOf (m : Meta) : MetaObs := ⟨m.address.account.cell, m.isSigner, m.isWritable⟩

/-- The fields of a fixed-width numeric tuple `[n₀, n₁, …]`. -/
def tuple (j : Json) (width : Nat) : Result (List Nat) := do
  let xs ← asList (asUInt 64) j
  unless xs.length = width do throw s!"expected {width} numbers, got {j.compress}"
  pure xs

/-- An `InstructionAccount` in a buffer, `[account, is_signer, is_writable]`:
its address reference resolved by the driver to the address field of an account
and its two flags (Rust `bool`s, 0/1). -/
def metaObs (j : Json) : Result MetaObs := do
  match ← tuple j 3 with
  | [a, s, w] => pure ⟨a, ← flag "is_signer" s, ← flag "is_writable" w⟩
  | _ => throw "unreachable"

def metaObsJson (m : MetaObs) : Json :=
  toJson [m.account, boolByte m.isSigner, boolByte m.isWritable]

def metaOfObs (m : MetaObs) : Meta := ⟨⟨⟨m.account⟩⟩, m.isSigner, m.isWritable⟩

/-- A `CpiAccount` in a buffer (a `repr(C)` value read by the driver),
`[account, data_len, rent_epoch, is_signer, is_writable, executable, padding]`:
its four pointer fields resolved to one account, its copied scalars and flag
bytes. The copied padding byte must be zero (the Boolean world has zero
padding). -/
def cpiAccount (j : Json) : Result CpiAccount := do
  match ← tuple j 7 with
  | [a, len, rent, s, w, x, pad] =>
    unless pad = 0 do throw "nonzero copied padding byte"
    pure ⟨⟨a⟩, len, rent, ← flag "is_signer" s, ← flag "is_writable" w, ← flag "executable" x⟩
  | _ => throw "unreachable"

def cpiAccountJson (a : CpiAccount) : Json :=
  toJson [a.account.cell, a.dataLen, a.rentEpoch, boolByte a.isSigner, boolByte a.isWritable,
    boolByte a.executable, 0]

structure BuffersObs where
  data : List (Option UInt8)
  accounts : List (Option CpiAccount)
  instructionAccounts : List (Option MetaObs)
  deriving DecidableEq

def buffersObsOf (b : Buffers) : BuffersObs :=
  ⟨b.data, b.accounts, b.instructionAccounts.map (·.map metaObsOf)⟩

/-- Recorded buffers are fully initialized (`some` everywhere). -/
def buffersObs (state : Json) : Result BuffersObs := do
  let j ← field state "buffers"
  pure ⟨(← asBytes (← field j "data")).map some, (← asList cpiAccount (← field j "accounts")).map
    some,
    (← asList metaObs (← field j "instruction_accounts")).map some⟩

def buffersOfObs (b : BuffersObs) : Buffers :=
  ⟨b.data, b.accounts, b.instructionAccounts.map (·.map metaOfObs)⟩

def slotJson {α : Type} (render : α → Json) : Option α → Json
  | some a => render a
  | none => Json.null

def buffersObsJson (b : BuffersObs) : Json := Json.mkObj [
  ("data", listJson (slotJson fun (x : UInt8) => toJson x.toNat) b.data),
  ("accounts", listJson (slotJson cpiAccountJson) b.accounts),
  ("instruction_accounts", listJson (slotJson metaObsJson) b.instructionAccounts)]

/-- Every account a buffer entry refers to is an account of the region. -/
def buffersResolve (count : Nat) (b : BuffersObs) : Result Unit := do
  for e in b.accounts do
    if let some a := e then resolves count a.account
  for e in b.instructionAccounts do
    if let some m := e then resolves count ⟨m.account⟩

def transferResolves {Signer : Type} (count : Nat) (t : Transfer Signer) : Result Unit := do
  for h in [t.fromAccount, t.mint, t.toAccount, t.authority] do resolves count h

def lengths (state : Json) : Result Lengths := do
  let j ← field state "lengths"
  pure ⟨← natField j "data" 64, ← natField j "accounts" 64, ← natField j "instruction_accou\
    nts" 64⟩

def lengthsJson (l : Lengths) : Json := Json.mkObj [("data", toJson l.data),
  ("accounts", toJson l.accounts), ("instruction_accounts", toJson l.instructionAccounts)]

/-! ## `Batch::new` -/

/-- The buffers are the state of the model; the region and syscalls are frame. -/
structure NewObs where
  buffers : BuffersObs
  pool : PoolObs
  deriving DecidableEq

def newObs (state : Json) : Result NewObs := do pure ⟨← buffersObs state, ← poolObs state⟩

def newObsJson (s : NewObs) : Json :=
  Json.mkObj [("buffers", buffersObsJson s.buffers), ("pool", poolObsJson s.pool)]

def newChecker : Checker where
  function := "pinocchio_token::instructions::batch::Batch::<'account, 'state>::new"
  generics := []
  reference := "Solanalib.Specs.PinocchioToken.instructions.batch.Batch.new_reference"
  decides := ["Solanalib.Specs.PinocchioToken.instructions.batch.Batch.new_reference"]
  check := fun c => do
    let run := instructions.batch.Batch.new_reference
    let buffers ← buffersObs c.state
    let frame ← poolObs c.state
    buffersResolve frame.accounts.length buffers
    let before := buffersOfObs buffers
    let recorded ← parseOutcome (asExcept programError lengths') newObs noReason noReason c.outcome
    pure (decideObserved (returnsOf (Unwind := Empty) (Terminal := Empty) run before ())
      (some (.returned (run before ()).1 (run before ()).2)) (returnsOf_graph run before ())
      (Outcome.observe (fun v _ => v) (fun b => ⟨buffersObsOf b, frame⟩) id id) recorded
      (outcomeJson (exceptObsJson programErrorJson lengthsJson) newObsJson emptyJson emptyJson))
where
  lengths' (j : Json) : Result Lengths := do
    pure ⟨← natField j "data" 64, ← natField j "accounts" 64, ← natField j "instruction_acc\
      ounts"
      64⟩

/-! ## `TransferChecked::new` (single owner) -/

def singleTransfer (j : Json) : Result SingleTransfer := do
  pure ⟨← handleField j "from", ← handleField j "mint", ← handleField j "to",
    ← handleField j "authority", ← natField j "amount" 64, ← natField j "decimals" 8⟩

structure TransferObs where
  fromAccount : Nat
  mint : Nat
  toAccount : Nat
  authority : Nat
  multisigSigners : List Nat
  amount : Nat
  decimals : Nat
  deriving DecidableEq

def transferObsOf (t : Transfer AccountView.Handle) : TransferObs :=
  ⟨t.fromAccount.cell, t.mint.cell, t.toAccount.cell, t.authority.cell,
    t.multisigSigners.map (·.cell), t.amount, t.decimals⟩

def transferObs (j : Json) : Result TransferObs := do
  pure ⟨← natField j "from" 64, ← natField j "mint" 64, ← natField j "to" 64,
    ← natField j "authority" 64, ← asList (asUInt 64) (← field j "multisig_signers"),
    ← natField j "amount" 64, ← natField j "decimals" 8⟩

def transferObsJson (t : TransferObs) : Json := Json.mkObj [("from", toJson t.fromAccount),
  ("mint", toJson t.mint), ("to", toJson t.toAccount), ("authority", toJson t.authority),
  ("multisig_signers", toJson t.multisigSigners), ("amount", toJson t.amount),
  ("decimals", toJson t.decimals)]

/-- The state of the model is `Unit`; the region and syscalls are frame. The account references of
the returned struct are resolved by the driver. -/
def transferNewChecker : Checker where
  function :=
    "pinocchio_token::instructions::transfer_checked::TransferChecked::<'account, '_, \
      &'account solana_account_view::AccountView>::new"
  generics := []
  reference :=
    "Solanalib.Specs.PinocchioToken.instructions.transfer_checked.TransferChecked.new_refer\
      ence"
  decides :=
    ["Solanalib.Specs.PinocchioToken.instructions.transfer_checked.TransferChecked.new_refe\
      rence"]
  check := fun c => do
    let run :=
      instructions.transfer_checked.TransferChecked.new_reference
    let frame ← poolObs c.state
    let args ← singleTransfer c.args
    for h in [args.fromAccount, args.mint, args.toAccount, args.authority] do
      resolves frame.accounts.length h
    let recorded ← parseOutcome transferObs poolObs noReason noReason c.outcome
    pure (decideObserved (returnsOf (Unwind := Empty) (Terminal := Empty) run () args)
      (some (.returned (run () args).1 (run () args).2)) (returnsOf_graph run () args)
      (Outcome.observe (fun v _ => transferObsOf v) (fun _ => frame) id id) recorded
      (outcomeJson transferObsJson poolObsJson emptyJson emptyJson))

/-! ## Batch states -/

/-- The observation of a Batch state: the accounts of the world, the frame `F`, the
callback-owned ambient observation, the buffers and committed lengths. -/
structure BatchObs (F AO : Type) where
  accounts : List AccountObs
  frame : F
  ambient : AO
  buffers : BuffersObs
  lengths : Lengths
  deriving DecidableEq

def batchObsOf {F A AO : Type} (frame : F) (ambient : AccountView.State → A → AO) (s : State A) :
    BatchObs F AO :=
  ⟨booleanPoolObs s.context.world, frame, ambient s.context.world s.context.ambient,
    buffersObsOf s.buffers, s.lengths⟩

def batchObs {F AO : Type} (frame : Json → Result F) (ambient : Json → Result AO) (j : Json) :
    Result (BatchObs F AO) := do
  pure ⟨(← regionOf j).1, ← frame j, ← ambient j, ← buffersObs j, ← lengths j⟩

def batchObsJson {F AO : Type} (frame : F → Json) (ambient : AO → Json) (s : BatchObs F AO) : Json
  :=
  Json.mkObj [("accounts", listJson accountObsJson s.accounts), ("frame", frame s.frame),
    ("ambient", ambient s.ambient), ("buffers", buffersObsJson s.buffers),
    ("lengths", lengthsJson s.lengths)]

def batchState {A : Type} (ambient : Json → Result A) (j : Json) : Result (State A) := do
  pure ⟨⟨← booleanPool (← regionOf j).1, ← ambient j⟩, buffersOfObs (← buffersObs j), ← lengths j⟩

/-! ## `IntoBatch::into_batch` -/

/-- `&AccountView`: `as_ref` returns the account of the signer, no effect. -/
abbrev identityTypes : Types := ⟨Unit, AccountView.Handle, Empty, Empty⟩

def identityAsRef : AsRefFn identityTypes := fun ctx h => .returned h ctx

/-- One step of a scripted `as_ref`: return account `j`, or panic. -/
inductive Step where
  | ret (account : Nat)
  | panic
  deriving DecidableEq

def step (j : Json) : Result Step :=
  match j.getStr? with
  | .ok "panic" => pure .panic
  | _ => do pure (.ret (← natField j "return" 64))

def panicMessage : String := "scripted as_ref panic"
def exhaustedMessage : String := "as_ref script exhausted"

/-- `ScriptedSigner`: the log of signer ids is the ambient state. -/
abbrev scriptedTypes : Types := ⟨List Nat, Nat, String, Empty⟩

def scriptedAsRef (script : List Step) : AsRefFn scriptedTypes := fun ctx id =>
  let after : Context (List Nat) := { ctx with ambient := ctx.ambient ++ [id] }
  match script[ctx.ambient.length]? with
  | some (.ret j) => .returned ⟨j⟩ after
  | some .panic => .unwound panicMessage after
  | none => .unwound exhaustedMessage after

def transferArgs {Signer : Type} (signer : Json → Result Signer) (j : Json) : Result (Transfer
  Signer) := do
  pure ⟨← singleTransfer j, ← asList signer (← field j "multisig_signers")⟩

/-- The `as_ref` log of the record state (`"asref_log"`). -/
def asRefLog (state : Json) : Result (List Nat) := do asList (asUInt 64) (← field state
  "asref_log")

def noAsRefLog (state : Json) : Result Unit := do
  unless (← asRefLog state).isEmpty do throw "MultisigSigner = &AccountView has no as_ref \
    log"

structure IntoInstance where
  types : Types
  generic : String
  ambientObs : Type
  [decAmbient : DecidableEq ambientObs]
  [decUnwind : DecidableEq types.Unwind]
  [decTerminal : DecidableEq types.Terminal]
  observeAmbient : types.Ambient → ambientObs
  parseAmbient : Json → Result types.Ambient
  parseAmbientObs : Json → Result ambientObs
  renderAmbient : ambientObs → Json
  signer : Json → Result types.Signer
  asRef : Json → Result (AsRefFn types)
  /-- Accounts the callback can return (identity: the signers; scripted: the accounts of the
  script). -/
  argHandles : Json → Result (List Borrow.Handle)
  unwind : String → Option types.Unwind
  renderUnwind : types.Unwind → Json
  renderTerminal : types.Terminal → Json

attribute [instance] IntoInstance.decAmbient IntoInstance.decUnwind IntoInstance.decTerminal

def identityInstance : IntoInstance where
  types := identityTypes
  generic := "&solana_account_view::AccountView"
  ambientObs := Unit
  observeAmbient := id
  parseAmbient := noAsRefLog
  parseAmbientObs := noAsRefLog
  renderAmbient := fun _ => Json.arr #[]
  signer := handle
  asRef := fun _ => pure identityAsRef
  argHandles := fun args => do asList handle (← field args "multisig_signers")
  unwind := noReason
  renderUnwind := emptyJson
  renderTerminal := emptyJson

def scriptedInstance : IntoInstance where
  types := scriptedTypes
  generic := "conformance_token_views::ScriptedSigner"
  ambientObs := List Nat
  observeAmbient := id
  parseAmbient := asRefLog
  parseAmbientObs := asRefLog
  renderAmbient := toJson
  signer := asUInt 64
  asRef := fun args => do pure (scriptedAsRef (← asList step (← field args "script")))
  argHandles := fun args => do
    pure ((← asList step (← field args "script")).filterMap fun
      | .ret j => some ⟨j⟩
      | .panic => none)
  unwind := fun r => some r
  renderUnwind := Json.str
  renderTerminal := emptyJson

/-- The registered reference at the index and callback of this instance. -/
def intoChecker (i : IntoInstance) : Checker where
  function :=
    "<pinocchio_token::instructions::transfer_checked::TransferChecked<'_, '_, \
      MultisigSigner> as pinocchio_token::instructions::batch::IntoBatch>::into_batch"
  generics := [("MultisigSigner", i.generic)]
  reference :=
    "Solanalib.Specs.PinocchioToken.instructions.transfer_checked.TransferChecked.into_batc\
      h_reference"
  decides :=
    ["Solanalib.Specs.PinocchioToken.instructions.transfer_checked.TransferChecked.into_bat\
      ch_reference"]
  check := fun c => do
    let before ← batchState i.parseAmbient c.state
    let frame ← frameOf c.state
    let transfer ← transferArgs i.signer c.args
    let f ← i.asRef c.args
    let count := before.context.world.cells.length
    transferResolves count transfer
    for h in ← i.argHandles c.args do resolves count h
    buffersResolve count (buffersObsOf before.buffers)
    let relation : Outcome (State i.types.Ambient) (Except Error Unit) i.types.Unwind
      i.types.Terminal →
        Prop :=
      instructions.transfer_checked.TransferChecked.into_batch_reference
        i.types before ⟨transfer, Callback.ofFunction f⟩
    let recorded ← parseOutcome (asExcept programError asUnit) (batchObs frameOf i.parseAmbientObs)
      i.unwind noReason c.outcome
    pure (decideObserved relation (some (intoBatchFn f before transfer))
      (fun o => (intoBatch_ofFunction f before transfer o).trans ⟨congrArg some, Option.some.inj⟩)
      (Outcome.observe (fun v _ => v) (batchObsOf frame fun _ a => i.observeAmbient a) id id)
        recorded
      (outcomeJson (exceptObsJson programErrorJson fun _ => Json.null)
        (batchObsJson frameJson i.renderAmbient) i.renderUnwind i.renderTerminal))

/-! ## `Batch::invoke_signed` -/

/-- The value-level CPI request a pointer-bearing request denotes in a world:
what the shim reads through its pointers. -/
def callObsOf (world : AccountView.State) (r : Request) : CallObs :=
  ⟨⟨r.programId.bytes, r.instructionAccounts.map (fun m =>
      ⟨(world.account m.address.account).metadata.address.bytes, m.isSigner, m.isWritable⟩),
        r.data⟩,
    r.accounts.map (fun c =>
      accountInfoOf world c.account c.dataLen c.rentEpoch c.isSigner c.isWritable c.executable),
    r.signers⟩

/-- The observation of the shim of the Batch provider state. A the raw
header of `CpiAccount` is its copied flag bytes and the copied padding byte, which is zero in
a Boolean world (its region padding is zero). -/
def shimObsOf (world : AccountView.State) (s : ShimState Request) : ShimObs :=
  ⟨s.replies, s.log.map fun r => (callObsOf world r, r.accounts.map fun c =>
    some [boolByte c.isSigner, boolByte c.isWritable, boolByte c.executable, 0])⟩

/-- The shim as the opaque provider: its reply script and request log are
the ambient state. -/
abbrev shimTypes : Types := ⟨ShimState Request, Unit, Empty, TerminalObs⟩

def shimInvokeFn : InvokeFn shimTypes := fun ctx sent =>
  match shimInvoke (shimObsOf ctx.world) ctx.ambient sent with
  | .returned () s => .returned () { ctx with ambient := s }
  | .unwound r s => .unwound r { ctx with ambient := s }
  | .terminated r => .terminated r

/-- The shim state before a call: the script, an empty log. -/
def shimBefore (state : Json) : Result (ShimState Request) := do
  let s ← Runtime.syscallsOf state
  unless s.log.isEmpty do throw "the request log before the call must be empty"
  pure ⟨s.replies, []⟩

def regionFrame (state : Json) : Result RegionFrame := do pure (← regionOf state).2

/-- The admission of a committed prefix is decidable (bound and initialized slots). -/
instance prefixReadyDec {Value : Type} (buffer : List (Option Value)) (length : Nat) :
    Decidable (PrefixReady buffer length) :=
  inferInstanceAs (Decidable (length ≤ buffer.length ∧ (buffer.take length).all Option.isSome =
    true))

/-- `InvocationReady`, the `requires` of the invocation family, is decidable. -/
instance invocationReadyDec {Ambient : Type} (before : State Ambient) : Decidable (InvocationReady
  before) :=
  inferInstanceAs (Decidable (PrefixReady before.buffers.data before.lengths.data ∧
    PrefixReady before.buffers.accounts before.lengths.accounts ∧
    PrefixReady before.buffers.instructionAccounts before.lengths.instructionAccounts))

/-- The decider of the checker for the `requires` of the invocation contract at the shim
index (`InvocationReady`). -/
instance invokeRequiresDec (before : State (ShimState Request)) (args : InvokeCall shimTypes) :
    Decidable
      ((instructions.batch.Batch.invoke_signed_contract.contract
      shimTypes).requires before args) :=
  decidable_of_iff (InvocationReady before) Iff.rfl

/-- A state for the kernel-checked cases below: an empty world and shim, the
given buffers and committed lengths. -/
def readyCase (data : List (Option UInt8)) (length : Nat) : State (ShimState Request) :=
  ⟨⟨⟨[], []⟩, ⟨[], []⟩⟩, ⟨data, [], []⟩, ⟨length, 0, 0⟩⟩

def noSigners : InvokeCall shimTypes := ⟨[], Callback.ofFunction shimInvokeFn⟩

/-- The decider of the checker rejects an uninitialized committed slot (which no
recorded buffer can express: every recorded slot is initialized). -/
theorem invokeRequires_rejects_hole :
    decide ((instructions.batch.Batch.invoke_signed_contract.contract
      shimTypes).requires (readyCase [some 255, none] 2) noSigners) = false := by decide

/-- The decider of the checker rejects a committed length beyond its buffer. -/
theorem invokeRequires_rejects_long_prefix :
    decide ((instructions.batch.Batch.invoke_signed_contract.contract
      shimTypes).requires (readyCase [some 255] 2) noSigners) = false := by decide

/-- The decider of the checker admits a committed, initialized prefix with an
uninitialized suffix. -/
theorem invokeRequires_admits_committed :
    decide ((instructions.batch.Batch.invoke_signed_contract.contract
      shimTypes).requires (readyCase [some 255, none] 1) noSigners) = true := by decide

/-- The `requires` of the invocation contract at the shim index: a record outside it
(a committed prefix out of bounds or uninitialized) is rejected. -/
def invokeChecker : Checker where
  function := "pinocchio_token::instructions::batch::Batch::<'account, \
    'state>::invoke_signed"
  generics := []
  reference := "Solanalib.Specs.PinocchioToken.instructions.batch.Batch.invoke_signed_refer\
    ence"
  decides := ["Solanalib.Specs.PinocchioToken.instructions.batch.Batch.invoke_signed_refere\
    nce"]
  decidesRequires :=
    ["Solanalib.Specs.PinocchioToken.instructions.batch.Batch.invoke_signed_reference"]
  check := fun c => do
    let before ← batchState shimBefore c.state
    let frame ← regionFrame c.state
    buffersResolve before.context.world.cells.length (buffersObsOf before.buffers)
    let seeds ← asList (asList asBytes) (← field c.args "signers")
    let args : InvokeCall shimTypes := ⟨seeds, Callback.ofFunction shimInvokeFn⟩
    unless @decide
      ((instructions.batch.Batch.invoke_signed_contract.contract
        shimTypes).requires before args) (invokeRequiresDec before args) do
      return ⟨false, Json.str "outside the precondition InvocationReady"⟩
    let relation : Outcome (State (ShimState Request)) (Except Error Unit) Empty TerminalObs → Prop
      :=
      instructions.batch.Batch.invoke_signed_reference
        shimTypes before ⟨seeds, Callback.ofFunction shimInvokeFn⟩
    let recorded ← parseShimOutcome (asExcept programError asUnit) (batchObs regionFrame shimObs)
      noReason c.outcome
    pure (decideObserved relation (invokeComputed shimInvokeFn before seeds)
      (invokeSigned_ofFunction shimInvokeFn before seeds)
      (Outcome.observe (fun v _ => v) (batchObsOf frame shimObsOf) id id) recorded
      (outcomeJson (exceptObsJson programErrorJson fun _ => Json.null)
        (batchObsJson regionFrameJson shimObsJson) emptyJson terminalObsJson))

def checkers : List Checker :=
  [newChecker, transferNewChecker, intoChecker identityInstance, intoChecker scriptedInstance,
    invokeChecker]

end SolanalibTest.Conformance.Library.Families.TokenViews.Batch
