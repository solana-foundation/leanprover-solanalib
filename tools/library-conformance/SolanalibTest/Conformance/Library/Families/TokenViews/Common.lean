/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import SolanalibTest.Conformance.Library.Runtime
import Solanalib.Specs.Core.AccountView
import Solanalib.Runtime.Error

/-!
# Shared vocabulary of the `TokenViews` checkers

Every record of the `token-views` driver runs in the forked child of the shim over
a loader input region (`rust/accounts`). Its state holds:

* `region`: the region read back (`Region::read_back`) right before and right
  after the call. Account `j` (no duplicates) is the cell handle of the model `⟨j⟩`.
  The marker byte is the borrow state of account-view 2.0.0.
* `syscalls`: the reply script and request log of the shim.
* the buffers or callback logs of the family (`Batch`).

**Before-states.** A pool is built canonically from the region: cell `j`
holds the header and data of the account (`backing` = the data, `entryLen` = the
data length, no resize, owner epoch 0) under the AccountView policy. Its live
guards follow the marker: `255` none, `0` one exclusive guard, any other value
`255 - b` shared guards over the whole data. A typed reference held by the
driver (a `Ref<Account>`/`Ref<Mint>`) is the first shared guard of its
account, after its one `Ref::map` (generation 1, the mapped view).

**Observations.** Guard identities and generations are not observable
natively. Each checker decides, through a graph lemma of the registered
relation, whether the relation admits an outcome whose *observation* equals
the recorded one: per account the header, data and the marker derived from
the live guards (`0` if an exclusive guard is live, else `255 -` the number of
shared guards); for returned references the account, offset and length they
denote in the after-state. Region parts the models do not represent (rent
epochs, spare bytes after the data, instruction data, program id) and, for
models without syscalls, the syscall state form the *frame*: the after-state
must carry the frame of the before-state.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.TokenViews

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! ## Deciding a relation up to an observation -/

/-- A relation with a graph lemma admits an outcome with a given observation
exactly when its computed outcome has that observation. -/
theorem observed_iff {O Obs : Type} (relation : O → Prop) (computed : Option O)
    (graph : ∀ o, relation o ↔ computed = some o) (project : O → Obs) (observed : Obs) :
    (∃ o, relation o ∧ project o = observed) ↔ computed.map project = some observed := by
  constructor
  · rintro ⟨o, admitted, rfl⟩
    rw [(graph o).1 admitted]
    rfl
  · intro h
    cases hc : computed with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      exact ⟨c, (graph c).2 hc, Option.some.inj h⟩

/-- Decide `∃ o, relation o ∧ project o = observed` for the recorded
observation, through the graph lemma of the relation. A record whose exit kind the
family cannot represent (`none`) is rejected. -/
def decideObserved {O Obs : Type} [DecidableEq Obs] (relation : O → Prop) (computed : Option O)
    (graph : ∀ o, relation o ↔ computed = some o) (project : O → Obs)
    (observed : Option Obs) (render : Obs → Json) : Verdict :=
  let expected := match computed.map project with
    | some o => render o
    | none => Json.str "no outcome (the reference admits none at this input)"
  match observed with
  | some ob =>
    have : Decidable (∃ o, relation o ∧ project o = ob) :=
      decidable_of_iff _ (observed_iff relation computed graph project ob).symm
    ⟨decide (∃ o, relation o ∧ project o = ob), expected⟩
  | none => ⟨false, expected⟩

/-- The graph of a total reference, in the form `decideObserved` uses. -/
theorem returnsOf_graph {S A V U T : Type} (run : S → A → V × S) (before : S) (args : A)
    (o : Outcome S V U T) :
    returnsOf run before args o ↔
      some (Outcome.returned (run before args).1 (run before args).2) = some o := by
  rw [returnsOf_iff]
  exact ⟨fun h => by rw [h], fun h => Option.some.inj h⟩

/-- Project every component of an outcome; the observation of a value may read the
after-state (for example the guard a returned reference denotes). -/
def Outcome.observe {S V U T SO VO UO TO : Type} (value : V → S → VO) (state : S → SO)
    (unwind : U → UO) (terminal : T → TO) : Outcome S V U T → Outcome SO VO UO TO
  | .returned v s => .returned (value v s) (state s)
  | .unwound r s => .unwound (unwind r) (state s)
  | .terminated r => .terminated (terminal r)

def outcomeJson {S V U T : Type} (value : V → Json) (state : S → Json) (unwind : U → Json)
    (terminal : T → Json) : Outcome S V U T → Json
  | .returned v s => Json.mkObj [("exit", "returned"), ("result", value v), ("state", state s)]
  | .unwound r s => Json.mkObj [("exit", "unwound"), ("reason", unwind r), ("state", state s)]
  | .terminated r => Json.mkObj [("exit", "terminated"), ("reason", terminal r)]

def emptyJson (e : Empty) : Json := nomatch e

/-! ## Values -/

def natField (j : Json) (k : String) (bits : Nat) : Result Nat := do asUInt bits (← field j k)

def toPubkey (b : Solanalib.Runtime.Bytes) : Result Solanalib.Runtime.Pubkey :=
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkey (j : Json) : Result Solanalib.Runtime.Pubkey := do toPubkey (← asBytes j)

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

def asList {α : Type} (parse : Json → Result α) (j : Json) : Result (List α) := do
  (← j.getArr?).toList.mapM parse

def listJson {α : Type} (render : α → Json) (xs : List α) : Json := Json.arr (xs.map render).toArray

/-- `ProgramError` variants by their `Debug` names, as the drivers record them. -/
def programErrors : List (String × Solanalib.Runtime.InstrError) := [
  ("InvalidArgument", .InvalidArgument), ("InvalidInstructionData", .InvalidInstructionData),
  ("InvalidAccountData", .InvalidAccountData), ("AccountDataTooSmall", .AccountDataTooSmall),
  ("InsufficientFunds", .InsufficientFunds), ("IncorrectProgramId", .IncorrectProgramId),
  ("MissingRequiredSignature", .MissingRequiredSignature),
  ("AccountAlreadyInitialized", .AccountAlreadyInitialized),
  ("UninitializedAccount", .UninitializedAccount), ("NotEnoughAccountKeys", .NotEnoughAccountKeys),
  ("AccountBorrowFailed", .AccountBorrowFailed), ("MaxSeedLengthExceeded", .MaxSeedLengthExceeded),
  ("InvalidSeeds", .InvalidSeeds), ("BorshIoError", .BorshIoError),
  ("AccountNotRentExempt", .AccountNotRentExempt), ("UnsupportedSysvar", .UnsupportedSysvar),
  ("IllegalOwner", .IllegalOwner),
  ("MaxAccountsDataAllocationsExceeded", .MaxAccountsDataAllocationsExceeded),
  ("InvalidRealloc", .InvalidRealloc),
  ("MaxInstructionTraceLengthExceeded", .MaxInstructionTraceLengthExceeded),
  ("BuiltinProgramsMustConsumeComputeUnits", .BuiltinProgramsMustConsumeComputeUnits),
  ("InvalidAccountOwner", .InvalidAccountOwner), ("ArithmeticOverflow", .ArithmeticOverflow),
  ("Immutable", .Immutable), ("IncorrectAuthority", .IncorrectAuthority)]

def programError (j : Json) : Result Solanalib.Runtime.InstrError := do
  let s ← j.getStr?
  match programErrors.find? (·.1 == s) with
  | some (_, e) => pure e
  | none =>
    if s.startsWith "Custom(" && s.endsWith ")" then
      match ((s.drop 7).dropEnd 1).toString.toNat? with
      | some n => pure (.Custom n)
      | none => throw s!"unknown ProgramError {s}"
    else throw s!"unknown ProgramError {s}"

def programErrorJson (e : Solanalib.Runtime.InstrError) : Json :=
  match e with
  | .Custom n => Json.str s!"Custom({n})"
  | _ => match programErrors.find? (·.2 == e) with
    | some (s, _) => Json.str s
    | none => Json.str s!"{repr e}"

def optionJson {α : Type} (render : α → Json) : Option α → Json
  | some a => render a
  | none => Json.str "none"

def exceptObsJson {ε α : Type} (error : ε → Json) (value : α → Json) : Except ε α → Json
  | .ok v => okJson (value v)
  | .error e => errJson (error e)

/-- A handle argument: the position of the account in the region. -/
def handle (j : Json) : Result Borrow.Handle := do pure ⟨← asUInt 64 j⟩

def handleField (j : Json) (k : String) : Result Borrow.Handle := do handle (← field j k)

/-- A handle must name an account of the region (`count` accounts): safe Rust
holds only references to real accounts. The total models answer a dangling
handle with a fallback, which no native run can produce. -/
def resolves (count : Nat) (h : Borrow.Handle) : Result Unit := do
  unless h.cell < count do
    throw s!"handle {h.cell} names no account of the region ({count} accounts)"

/-! ## Accounts of the region -/

/-- The modeled observation of one account: its header bytes (flags and the
4-byte padding, raw), address, owner, lamports, data and marker. -/
structure AccountObs where
  address : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  lamports : Nat
  data : Solanalib.Runtime.Bytes
  isSigner : Nat
  isWritable : Nat
  executable : Nat
  padding : Nat
  borrowState : Nat
  deriving DecidableEq

def accountObsJson (a : AccountObs) : Json := Json.mkObj [
  ("key", pubkeyJson a.address), ("owner", pubkeyJson a.owner), ("lamports", toJson a.lamports),
  ("data", bytesJson a.data), ("is_signer", toJson a.isSigner), ("is_writable", toJson
    a.isWritable),
  ("executable", toJson a.executable), ("padding", toJson a.padding),
  ("marker", toJson a.borrowState)]

/-- Region parts no model here represents. -/
structure RegionFrame where
  /-- Per account: rent epoch and the first nonzero spare byte after the data. -/
  accounts : List (Nat × Option Nat)
  instructionData : Solanalib.Runtime.Bytes
  programId : Solanalib.Runtime.Bytes
  deriving DecidableEq

def regionFrameJson (f : RegionFrame) : Json := Json.mkObj [
  ("accounts", listJson (fun (p : Nat × Option Nat) => Json.mkObj [("rent_epoch", toJson p.1),
    ("spare_nonzero_at", match p.2 with | some n => toJson n | none => Json.null)]) f.accounts),
  ("instruction_data", bytesJson f.instructionData), ("program_id", bytesJson f.programId)]

def accountOf : Runtime.RegionEntry → Result (AccountObs × Nat × Option Nat)
  | .duplicate i => throw s!"duplicate region entry (of {i}) is not used by these records"
  | .account a => do
    unless a.dataLen = a.data.length do
      throw s!"data_len {a.dataLen} differs from the {a.data.length} bytes read back"
    -- Native widths: the marker and flags are bytes, the padding a u32, the rest u64.
    for (name, v) in [("marker", a.marker), ("is_signer", a.isSigner), ("is_writable",
      a.isWritable),
        ("executable", a.executable)] do
      unless v < 256 do throw s!"{name} {v} is not a byte"
    unless a.padding < 2 ^ 32 do throw s!"padding {a.padding} is not a u32"
    for (name, v) in [("lamports", a.lamports), ("data_len", a.dataLen), ("rent_epoch",
      a.rentEpoch)] do
      unless v < 2 ^ 64 do throw s!"{name} {v} is not a u64"
    pure (⟨← toPubkey a.key, ← toPubkey a.owner, a.lamports, a.data, a.isSigner, a.isWritable,
      a.executable, a.padding, a.marker⟩, a.rentEpoch, a.spareNonzeroAt)

/-- The region of a state: its modeled accounts and its frame. -/
def regionOf (state : Json) : Result (List AccountObs × RegionFrame) := do
  let r ← Runtime.region (← field state "region")
  let entries ← r.entries.mapM accountOf
  pure (entries.map (·.1), ⟨entries.map (·.2), r.instructionData, r.programId⟩)

/-- A Boolean flag byte. The AccountView model keeps flags as Booleans, so a
noncanonical byte is outside its representation and the record is rejected. -/
def flag (name : String) (b : Nat) : Result Bool :=
  if b = 0 then pure false else if b = 1 then pure true
  else throw s!"{name} byte {b} is not 0 or 1; the Boolean AccountView model cannot \
    represent it"

/-- The model account of a native observation (flags already decoded). -/
def modelAccount (a : AccountObs) (signer writable executable : Bool) : AccountView.Account where
  metadata := ⟨a.address, signer, writable, executable⟩
  owner := a.owner
  lamports := a.lamports
  dataLen := a.data.length
  entryLen := a.data.length
  backing := a.data
  resizeDelta := 0
  ownerEpoch := 0

/-- The live guards of account `j` with marker `b`, over the whole data. -/
def guardsOf (j : Nat) (a : AccountObs) : List (Option (Borrow.Slot AccountView.Slice)) :=
  if a.borrowState = 0 then [some ⟨⟨j⟩, .exclusive, 0, ⟨0, a.data.length⟩⟩]
  else List.replicate (255 - a.borrowState) (some ⟨⟨j⟩, .shared, 0, ⟨0, a.data.length⟩⟩)

def guardsFrom (j : Nat) : List AccountObs → List (Option (Borrow.Slot AccountView.Slice))
  | [] => []
  | a :: rest => guardsOf j a ++ guardsFrom (j + 1) rest

/-- The canonical pool of a list of accounts with explicit model accounts. -/
def poolOf (accounts : List (AccountObs × AccountView.Account)) : AccountView.State :=
  ⟨accounts.map fun (_, m) => ⟨m, Borrow.Policy.accountView⟩, guardsFrom 0 (accounts.map (·.1))⟩

/-- The canonical pool of accounts with canonical (0/1) flags and zero padding. -/
def booleanPool (accounts : List AccountObs) : Result AccountView.State := do
  let models ← accounts.mapM fun a => do
    unless a.padding = 0 do throw "nonzero padding is outside the AccountView \
      representation"
    pure (a, modelAccount a (← flag "is_signer" a.isSigner) (← flag "is_writable" a.isWritable)
      (← flag "executable" a.executable))
  pure (poolOf models)

/-- The native borrow byte of a pool cell, from its live guards. -/
def borrowByte (s : AccountView.State) (h : Borrow.Handle) : Nat :=
  if s.exclusiveCount h ≠ 0 then 0 else 255 - s.sharedCount h

def boolByte (b : Bool) : Nat := if b then 1 else 0

def cellsObs (s : AccountView.State) (header : Nat → AccountView.Account → Nat × Nat × Nat × Nat) :
    Nat → List (Borrow.Cell AccountView.Account) → List AccountObs
  | _, [] => []
  | j, c :: rest =>
    let (signer, writable, executable, padding) := header j c.value
    { address := c.value.metadata.address, owner := c.value.owner, lamports := c.value.lamports,
      data := c.value.bytes, isSigner := signer, isWritable := writable, executable,
      padding, borrowState := borrowByte s ⟨j⟩ } :: cellsObs s header (j + 1) rest

/-- The observation of a pool whose flags are the Booleans of the model. -/
def booleanPoolObs (s : AccountView.State) : List AccountObs :=
  cellsObs s (fun _ a => (boolByte a.metadata.signer, boolByte a.metadata.writable,
    boolByte a.metadata.executable, 0)) 0 s.cells

/-- The index of the first live shared guard of cell `j`. -/
def firstShared (slots : List (Option (Borrow.Slot AccountView.Slice))) (j : Nat) : Option Nat :=
  slots.findIdx? fun
    | some slot => slot.cell == ⟨j⟩ && slot.mode == .shared
    | none => false

/-- A typed view held by the driver: the first shared guard of its account,
mapped once to the view `⟨offset, length⟩`. Returns the pool and the guard. -/
def withMappedGuard (s : AccountView.State) (j offset length : Nat) :
    Result (AccountView.State × Borrow.Guard) := do
  let some id := firstShared s.slots j
    | throw s!"account {j} has no live shared borrow for the typed reference"
  let mapped : Borrow.Slot AccountView.Slice := ⟨⟨j⟩, .shared, 1, ⟨offset, length⟩⟩
  pure ({ s with slots := s.slots.set id (some mapped) }, ⟨id, 1⟩)

/-- What a guard denotes in a state: its account, view offset and length. -/
structure ViewObs where
  account : Nat
  offset : Nat
  length : Nat
  deriving DecidableEq

def viewObs (j : Json) : Result ViewObs := do
  pure ⟨← natField j "account" 64, ← natField j "offset" 64, ← natField j "len" 64⟩

def viewObsJson (v : ViewObs) : Json :=
  Json.mkObj [("account", toJson v.account), ("offset", toJson v.offset), ("len", toJson v.length)]

/-- The view a guard denotes, if it is live in `s`. -/
def guardView (s : AccountView.State) (g : Borrow.Guard) : Option ViewObs :=
  (s.resolve g).map fun slot => ⟨slot.cell.cell, slot.view.offset, slot.view.length⟩

/-! ## Syscalls -/

/-- The syscall state of a model without syscalls: it stays in the frame. -/
structure SyscallFrame where
  replies : List Runtime.Reply
  calls : List String
  deriving DecidableEq

def syscallFrame (state : Json) : Result SyscallFrame := do
  let s ← Runtime.syscallsOf state
  pure ⟨s.replies, s.log.map (·.syscall)⟩

def syscallFrameJson (f : SyscallFrame) : Json :=
  Json.mkObj [("replies", toJson f.replies.length), ("calls", toJson f.calls)]

/-- The full frame of a model without syscalls. -/
structure Frame where
  region : RegionFrame
  syscalls : SyscallFrame
  deriving DecidableEq

def frameOf (state : Json) : Result Frame := do
  pure ⟨(← regionOf state).2, ← syscallFrame state⟩

def frameJson (f : Frame) : Json :=
  Json.mkObj [("region", regionFrameJson f.region), ("syscalls", syscallFrameJson f.syscalls)]

/-- The observed state of a model without syscalls: the accounts and the frame. -/
structure PoolObs where
  accounts : List AccountObs
  frame : Frame
  deriving DecidableEq

def poolObs (state : Json) : Result PoolObs := do pure ⟨(← regionOf state).1, ← frameOf state⟩

def poolObsJson (s : PoolObs) : Json :=
  Json.mkObj [("accounts", listJson accountObsJson s.accounts), ("frame", frameJson s.frame)]

/-- The Boolean pool of a state, and its frame. -/
def poolState (state : Json) : Result (AccountView.State × Frame) := do
  pure (← booleanPool (← regionOf state).1, ← frameOf state)

/-- The reply script and request log of the shim, as a provider state. -/
structure ShimState (Req : Type) where
  replies : List Runtime.Reply
  log : List Req

/-- The value-level observation of a CPI request, as the shim logs it. -/
abbrev CallObs := Runtime.CpiCall

def callObsJson (c : CallObs) : Json := Json.mkObj [
  ("program_id", bytesJson c.instruction.programId),
  ("accounts", listJson (fun (m : Runtime.CpiMeta) => Json.mkObj [("pubkey", bytesJson m.pubkey),
    ("is_signer", toJson m.isSigner), ("is_writable", toJson m.isWritable)])
      c.instruction.accounts),
  ("data", bytesJson c.instruction.data),
  ("account_infos", listJson (fun (a : Runtime.CpiAccountInfo) => Json.mkObj [
    ("key", bytesJson a.key), ("lamports", toJson a.lamports), ("data", bytesJson a.data),
    ("owner", bytesJson a.owner), ("rent_epoch", toJson a.rentEpoch),
    ("is_signer", toJson a.isSigner), ("is_writable", toJson a.isWritable),
    ("executable", toJson a.executable)]) c.accountInfos),
  ("signers_seeds", listJson (listJson bytesJson) c.signersSeeds)]

/-- The four raw header bytes of each CPI account info (`is_signer`,
`is_writable`, `executable`, padding), which the driver asks the shim to log
(`shim::log_cpi_raw_header`): every path here initializes its CPI accounts
with the `init_from_account_view` of solana-instruction-view 2.1.0, which copies
the four bytes as one word. -/
abbrev RawHeaders := List (Option (List Nat))

structure ShimObs where
  replies : List Runtime.Reply
  log : List (CallObs × RawHeaders)
  deriving DecidableEq

def shimObs (state : Json) : Result ShimObs := do
  let s ← Runtime.syscallsOf state
  pure ⟨s.replies, ← s.log.mapM fun r => do pure (← Runtime.cpiCall r, ← Runtime.cpiRawHeaders r)⟩

def rawHeadersJson (h : RawHeaders) : Json := listJson (optionJson toJson) h

def shimObsJson (s : ShimObs) : Json :=
  Json.mkObj [("replies", toJson s.replies.length), ("log", listJson (fun (p : CallObs ×
    RawHeaders) =>
    Json.mkObj [("call", callObsJson p.1), ("headers", rawHeadersJson p.2)]) s.log)]

/-- A terminal exit of a case, as the shim reports it: the reason, the text of the
terminating reply and the syscall state at that point (unconsumed
replies and every request, including the one that did not return). The model
carries no post-state for a terminal exit, so the `Terminal` type of the test
carries this observation and it is compared exactly. -/
structure TerminalObs where
  reason : String
  detail : Option String
  syscalls : ShimObs
  deriving DecidableEq

def terminalObs (outcome : Json) : Result TerminalObs := do
  let detail := match outcome.getObjVal? "detail" with
    | .ok (.str d) => some d
    | _ => none
  pure ⟨← (← field outcome "reason").getStr?, detail, ← shimObs outcome⟩

def terminalObsJson (t : TerminalObs) : Json := Json.mkObj [("reason", Json.str t.reason),
  ("detail", match t.detail with | some d => Json.str d | none => Json.null),
  ("syscalls", shimObsJson t.syscalls)]

/-- `parseOutcome`, with a terminal exit read as a `TerminalObs`. -/
def parseShimOutcome {S V U : Type} (value : Json → Result V) (state : Json → Result S)
    (unwind : String → Option U) (j : Json) : Result (Option (Outcome S V U TerminalObs)) := do
  match ← (← field j "exit").getStr? with
  | "terminated" => return some (.terminated (← terminalObs j))
  | _ => parseOutcome value state unwind noReason j

/-- The `sol_invoke_signed_c` of the shim: logs the request and consumes the next
reply. A reply marked `terminate` ends the case: a terminal exit with reason
`sol_invoke_signed_c`, the text of the reply and the syscall state, whose log
includes this request (`observe` renders the provider state as the shim
logs it). Any other reply returns unit (the return code is ignored by
`invoke_signed_unchecked`). A missing, mismatched or effectful reply is a
script error (`shim`), which the recorder never writes. -/
def shimInvoke {Req : Type} (observe : ShimState Req → ShimObs) (s : ShimState Req) (sent : Req) :
    Outcome (ShimState Req) Unit Empty TerminalObs :=
  match s.replies with
  | r :: rest =>
    if r.syscall = "sol_invoke_signed_c" ∧ r.writes = [] then
      match r.terminate with
      | some detail => .terminated ⟨"sol_invoke_signed_c", some detail, observe ⟨rest, s.log ++
        [sent]⟩⟩
      | none => .returned () ⟨rest, s.log ++ [sent]⟩
    else .terminated ⟨"shim", none, observe s⟩
  | [] => .terminated ⟨"shim", none, observe s⟩

/-- The CPI account info a pointer-bearing entry denotes in a pool: the
shim reads the key, lamports, owner and `data_len` data bytes through its
pointers, all of which denote `account`. -/
def accountInfoOf (pool : AccountView.State) (account : Borrow.Handle) (dataLen rentEpoch : Nat)
    (signer writable executable : Bool) : Runtime.CpiAccountInfo :=
  let a := pool.account account
  ⟨a.metadata.address.bytes, a.lamports, Solanalib.Runtime.slice a.backing 0 dataLen,
    a.owner.bytes, rentEpoch,
    signer, writable, executable⟩

end SolanalibTest.Conformance.Library.Families.TokenViews
