/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc
import Solanalib.Specs.Core.TokenRequestAllocatedOnchain

/-!
# The closed index of the Token-2022 onchain operational model

`Token.OnchainAllocated.family` is indexed by `Types` (storage types and
primitive dependency relations) and `Dependencies` (the collection and CPI
dependencies). This module fixes one index, `Index env`, driven by a native
record through `env : Env`, and bundles the computed form of every primitive
of that index (`prims env : Prims (Index env).types`).

**Environment.** `Env` holds what the record scripts: the owner table (read by
`ownerAt`), the replies of the PDA syscall, in order, and the reply of the CPI
syscall.

**State.** `Extra` holds one reference ledger (`Owned.VectorState`) per vector
kind, the Rc strong count of each cell (`rc`, indexed like the `counts` of the record: cell `2i` is
account the lamports of `i`, `2i + 1` its data) and the logs
of the PDA and CPI syscalls. `initialWorld` builds the initial world from the borrow world of the
record and `state.counts`.

**Primitives.**
- `bytes`, `metas`, `paddingBytes`, the seed literals and `discriminators` are
  `Owned.vectorReference` focused on their ledger; the three byte vectors share
  the byte ledger, since they share `ByteResource`.
- `infos` is `OnchainRc.rcInfosOps` over the info ledger: `extend` clones
  through `rc`, and `drop` drops each current element first.
- `guards` drops the `DataRef` of each element before retiring the slot
  (`OnchainPrims.dropEachOps`).
- The seed and seed-reference vectors are empty-only (`emptyOnlyOps`), as in
  `Witness.emptyOnlyOps`: a ledger of `BytesView State` would make `Extra`
  refer to itself.
- The literal provider answers `.evaluate` while the prefix is shorter than the
  count and `.finish` at equality (`noAgain`); it completes with
  `infos.fromList`, cleans in index order and retires nothing.
- `cloneRc` and `dropRc` add or remove one owner at `rc[cell]`; a cell with no
  owner or out of range has no outcome.
- The PDA syscall answers `pdaReplies[pdaLog.length]?` and logs the request.
- The CPI follows the provider of the value checker (`Onchain.providerF`): the borrow
  pre-check, then the scripted reply, logged with the Rc counts at the call.
- `raise` unwinds with the panic, `doubleUnwind` terminates with the pair of
  reasons, and `writeMeta` is the graph of a `List.set` on the metadata ledger.
- Collection is `AllocatedCollect.protocolProvider collectProtocol`, with no
  internal chunks and `guards.fromList` as completion.

The scripted primitives are defined as the graphs of their computed forms, so
their `Fn` lemmas are immediate.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainIndex

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

/-! ## Exits, environment and state -/

/-- Unwind reasons of the index: the local panics of the source. -/
abbrev Unwind := Onchain.Panic

/-- Terminal reasons of the index: a destructor that unwinds during an unwind,
recorded as the original and the later reason. -/
abbrev Terminal := Onchain.Panic × Onchain.Panic

/-- What a native record scripts for one call. -/
structure Env where
  /-- The owner of each owner reference: entry `i` is the owner of account `i`. -/
  owners : List Solanalib.Runtime.Pubkey
  /-- The replies of the PDA syscall, in call order. -/
  pdaReplies : List Address.Syscall.PdaReply
  /-- The return value of the CPI syscall, if the record has one. -/
  cpiReply : Option Nat

/-- The ambient state of the index, alongside the AccountInfo borrow world. -/
structure Extra where
  /-- Byte vectors: instruction data, the 3.0.0 padding and seed literals. -/
  bytes : Owned.VectorState UInt8 := []
  /-- Instruction metadata vectors. -/
  metas : Owned.VectorState Solanalib.Runtime.CpiMeta := []
  /-- AccountInfo vectors. -/
  infos : Owned.VectorState AccountInfo.Value := []
  /-- Vectors of collected data Refs. -/
  guards : Owned.VectorState GuardElement := []
  /-- The discriminator vectors of the TLV validator. -/
  discriminators : Owned.VectorState Bytes := []
  /-- Slots of the empty-only unpacked-seed vectors. -/
  seeds : Owned.VectorState Unit := []
  /-- Slots of the empty-only seed-view vectors. -/
  seedRefs : Owned.VectorState Unit := []
  /-- The Rc strong count of each cell, indexed by `Borrow.Handle.cell`. -/
  rc : List Nat := []
  /-- The requests of the PDA syscall so far, in call order. -/
  pdaLog : List Address.Syscall.PdaRequest := []
  /-- Each CPI that reached the syscall, with the Rc counts at the call. -/
  cpiLog : List (CpiRequest.Request AccountInfo.Value × List Nat) := []

/-- The world of the index. -/
abbrev State := World Extra

/-- The initial world of a record: its borrow world and the Rc counts of its
cells before the call (`state.counts`); every ledger and log is empty. -/
def initialWorld (borrows : AccountInfo.State) (counts : List Nat) : State :=
  (borrows, { rc := counts })

/-- A recorded reply of `sol_try_find_program_address` as a PDA syscall reply:
the return value is the status, 32 data bytes are the address output (none
otherwise), and the bump is the bump output (255, its initial value, if
absent). -/
def pdaReplyOf (ret : Nat) (address : Solanalib.Runtime.Bytes) (bump : Option Nat) :
    Address.Syscall.PdaReply where
  status := UInt64.ofNat ret
  addressOutput := if h : address.length = 32 then some ⟨address, h⟩ else none
  bumpOutput := UInt8.ofNat (bump.getD 255)

/-! ## Foci -/

/-- The byte ledger. -/
def bytesFocus : Owned.Focus State (Owned.VectorState UInt8) where
  get := fun state => state.2.bytes
  set := fun state values => (state.1, { state.2 with bytes := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The metadata ledger. -/
def metasFocus : Owned.Focus State (Owned.VectorState Solanalib.Runtime.CpiMeta) where
  get := fun state => state.2.metas
  set := fun state values => (state.1, { state.2 with metas := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The AccountInfo ledger. -/
def infosFocus : Owned.Focus State (Owned.VectorState AccountInfo.Value) where
  get := fun state => state.2.infos
  set := fun state values => (state.1, { state.2 with infos := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The ledger of collected data Refs. -/
def guardsFocus : Owned.Focus State (Owned.VectorState GuardElement) where
  get := fun state => state.2.guards
  set := fun state values => (state.1, { state.2 with guards := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The discriminator ledger. -/
def discriminatorsFocus : Owned.Focus State (Owned.VectorState Bytes) where
  get := fun state => state.2.discriminators
  set := fun state values => (state.1, { state.2 with discriminators := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The slots of the unpacked-seed vectors. -/
def seedsFocus : Owned.Focus State (Owned.VectorState Unit) where
  get := fun state => state.2.seeds
  set := fun state values => (state.1, { state.2 with seeds := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The slots of the seed-view vectors. -/
def seedRefsFocus : Owned.Focus State (Owned.VectorState Unit) where
  get := fun state => state.2.seedRefs
  set := fun state values => (state.1, { state.2 with seedRefs := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-! ## Empty-only vectors -/

section EmptyOnly

variable {S E U T : Type}

/-- A vector with only empty contents over a ledger of unit slots, as
`Witness.emptyOnlyOps`: construction from the empty list and extension by the
empty list succeed, `push` and any nonempty contents have no outcome, and
`drop` retires the slot. -/
def emptyOnlyOps (part : Owned.Focus S (Owned.VectorState Unit)) :
    Owned.VectorOps S E Nat U T :=
  let units : Owned.VectorOps S Unit Nat U T := Owned.vectorReference.focus part
  { current := fun state resource => (units.current state resource).map fun _ => []
    empty := units.empty
    withCapacity := units.withCapacity
    fromList := fun state values outcome => values = [] ∧ units.withCapacity state 0 outcome
    push := fun _ _ _ => False
    extend := fun state (resource, values) outcome =>
      values = [] ∧ units.Live state resource ∧ outcome = .returned () state
    drop := units.drop }

/-- `emptyOnlyOps part` is bundled. Its `push` has no outcome (`pushF` is
`none`), and so have `fromList` and `extend` on a nonempty list. -/
def emptyOnlyPrims (part : Owned.Focus S (Owned.VectorState Unit)) :
    VecPrims (emptyOnlyOps (E := E) (U := U) (T := T) part) :=
  let units : VecPrims (Owned.vectorReference.focus part (Element := Unit) (Unwind := U)
      (Terminal := T)) := VecPrims.reference.focus part
  { withCapacityF := units.withCapacityF
    withCapacity_fn := units.withCapacity_fn
    fromListF := fun s values =>
      match values with
      | [] => units.withCapacityF s 0
      | _ :: _ => none
    fromList_fn := by
      intro s values o
      cases values with
      | nil => exact ⟨fun h => (units.withCapacity_fn s 0 o).1 h.2,
          fun h => ⟨rfl, (units.withCapacity_fn s 0 o).2 h⟩⟩
      | cons _ _ => exact ⟨fun h => (nomatch h.1), fun h => (nomatch h)⟩
    pushF := fun _ _ => none
    push_fn := fun _ _ _ => ⟨False.elim, fun h => nomatch h⟩
    extendF := fun s a =>
      match a.2 with
      | [] => ((part.get s).current a.1).map fun _ => .returned () s
      | _ :: _ => none
    extend_fn := by
      rintro s ⟨resource, values⟩ o
      cases values with
      | cons _ _ => exact ⟨fun h => (nomatch h.1), fun h => (nomatch h)⟩
      | nil =>
        show [] = [] ∧ (∃ values, (part.get s).current resource = some values) ∧
            o = .returned () s ↔ ((part.get s).current resource).map _ = some o
        cases (part.get s).current resource with
        | none => exact ⟨fun ⟨_, ⟨_, h⟩, _⟩ => (nomatch h), fun h => (nomatch h)⟩
        | some values =>
          exact ⟨fun ⟨_, _, h⟩ => by rw [h]; rfl,
            fun h => ⟨rfl, ⟨values, rfl⟩, (Option.some.inj h).symm⟩⟩
    dropF := units.dropF
    drop_fn := units.drop_fn }

end EmptyOnly

/-! ## Rc counts -/

/-- Clone one Rc of a cell: one more owner at `rc[cell]`. A cell with no owner
or out of range has no outcome. -/
def rcCloneF (s : State) (call : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome State Unit Empty Terminal) :=
  match s.2.rc[call.2.cell]? with
  | some (count + 1) =>
    some (.returned () (s.1, { s.2 with rc := s.2.rc.set call.2.cell (count + 2) }))
  | _ => none

/-- Drop one Rc of a cell: one owner fewer at `rc[cell]`. A cell with no owner
or out of range has no outcome. -/
def rcDropF (s : State) (call : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome State Unit Empty Terminal) :=
  match s.2.rc[call.2.cell]? with
  | some (count + 1) =>
    some (.returned () (s.1, { s.2 with rc := s.2.rc.set call.2.cell count }))
  | _ => none

/-- The Rc dependencies of the index: the graphs of `rcCloneF` and `rcDropF`. -/
def rcOps : AccountInfoRc.Ops State Terminal where
  cloneRc := fun s call o => rcCloneF s call = some o
  dropRc := fun s call o => rcDropF s call = some o

/-- The Rc dependencies are bundled. -/
def rcPrims : RcPrims rcOps where
  cloneRcF := rcCloneF
  cloneRc_fn := fun _ _ _ => Iff.rfl
  dropRcF := rcDropF
  dropRc_fn := fun _ _ _ => Iff.rfl

/-! ## Vectors -/

/-- Byte vectors on the byte ledger. -/
def bytesOps : Owned.VectorOps State UInt8 Nat Unwind Terminal :=
  Owned.vectorReference.focus bytesFocus

/-- Metadata vectors on the metadata ledger. -/
def metasOps : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Unwind Terminal :=
  Owned.vectorReference.focus metasFocus

/-- AccountInfo vectors: the info ledger, with Rc clones on `extend` and the
element drops on `drop` (`Witness.infosOps`). -/
def infosOps : Owned.VectorOps State AccountInfo.Value Nat Unwind Terminal :=
  rcInfosOps (Owned.vectorReference.focus infosFocus) rcOps

/-- Vectors of collected data Refs: `drop` releases the Ref of each element, in
order, before retiring the slot. -/
def guardsOps : Owned.VectorOps State GuardElement Nat Unwind Terminal :=
  dropEachOps (Owned.vectorReference.focus guardsFocus)
    (fun s element o => AllocatedControl.DataRef.drop element.2 s o)

/-- Discriminator vectors on their ledger. -/
def discriminatorsOps : Owned.VectorOps State Bytes Nat Unwind Terminal :=
  Owned.vectorReference.focus discriminatorsFocus

/-- The seed vectors: literals on the byte ledger, the unpacked seeds and the
seed views empty-only. -/
def seedOps : AllocatedSeeds.Ops State Nat Nat Nat Unwind Terminal where
  bytes := bytesOps
  seeds := emptyOnlyOps seedsFocus
  refs := emptyOnlyOps seedRefsFocus

/-- `bytesOps` is bundled. -/
def bytesPrims : VecPrims bytesOps := VecPrims.reference.focus bytesFocus

/-- `metasOps` is bundled. -/
def metasPrims : VecPrims metasOps := VecPrims.reference.focus metasFocus

/-- `infosOps` is bundled. -/
def infosPrims : VecPrims infosOps := rcInfosPrims (VecPrims.reference.focus infosFocus) rcPrims

/-- `guardsOps` is bundled. -/
def guardsPrims : VecPrims guardsOps :=
  dropEachPrims (VecPrims.reference.focus guardsFocus) (fun s e o => DataRef.drop_fn e.2 s o)

/-- `discriminatorsOps` is bundled. -/
def discriminatorsPrims : VecPrims discriminatorsOps := VecPrims.reference.focus discriminatorsFocus

/-! ## The literal array -/

/-- The literal construction work, computed: evaluate while the prefix is
shorter than the count, finish at equality, and no outcome beyond. -/
def literalWorkF (s : State) (input : Nat × List AccountInfo.Value) :
    Option (Outcome State Owned.Array.Command Unwind Terminal) :=
  if input.2.length < input.1 then some (.returned .evaluate s)
  else if input.2.length = input.1 then some (.returned .finish s)
  else none

/-- The literal-array provider: no internal chunk, completion by
`infos.fromList`, cleanup in index order and no storage to retire. Its `drop`
and `double` are replaced in `Types.literalProvider`. -/
def infoLiteral : Owned.Array.Provider State AccountInfo.Value Nat Unwind Terminal where
  work := fun before (count, values) outcome =>
    if values.length < count then outcome = .returned .evaluate before
    else values.length = count ∧ outcome = .returned .finish before
  finish := infosOps.fromList
  cleanupOrder := fun _ values => List.finRange values.length
  drop := AccountInfoRc.lift (AccountInfoRc.dropCall rcOps)
  retire := fun before _ outcome => outcome = .returned () before
  double := fun _ original later terminal => terminal = (original, later)

/-- The literal work admits exactly `literalWorkF`. -/
theorem literalWork_fn : Fn infoLiteral.work literalWorkF := by
  rintro s ⟨count, values⟩ o
  show (if values.length < count then o = .returned .evaluate s
      else values.length = count ∧ o = .returned .finish s) ↔ literalWorkF s (count, values) = some
        o
  unfold literalWorkF
  by_cases lt : values.length < count
  · simp only [lt, ↓reduceIte]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  · simp only [lt, ↓reduceIte]
    by_cases eq : values.length = count
    · subst eq
      simp only [↓reduceIte, true_and]
      exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    · simp only [eq, ↓reduceIte, false_and]
      exact ⟨False.elim, fun h => nomatch h⟩

/-- The literal retirement, computed: the state is unchanged. -/
def literalRetireF (s : State) (_ : List AccountInfo.Value) :
    Option (Outcome State Unit Unwind Terminal) :=
  some (.returned () s)

/-- The literal retirement admits exactly `literalRetireF`. -/
theorem literalRetire_fn : Fn infoLiteral.retire literalRetireF :=
  fun _ _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩

/-! ## Scripted primitives -/

/-- The PDA syscall, computed: the next scripted reply, after which the request
is logged. Past the script there is no outcome. -/
def pdaSyscallF (env : Env) (s : State) (request : Address.Syscall.PdaRequest) :
    Option (Outcome State Address.Syscall.PdaReply Unwind Terminal) :=
  env.pdaReplies[s.2.pdaLog.length]?.map fun reply =>
    .returned reply (s.1, { s.2 with pdaLog := s.2.pdaLog ++ [request] })

/-- The panic dependency, computed: unwind with the panic in the same state. -/
def raiseF (s : State) (reason : Onchain.Panic) : Option (Outcome State Empty Unwind Terminal) :=
  some (.unwound reason s)

/-- The panic dependency admits exactly `raiseF`. -/
theorem raise_fn : Fn (fun s reason o => o = .unwound reason s) raiseF :=
  fun _ _ _ => ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩

/-- The metadata write, computed: set entry `index` of the current metadata
vector to `item`. A missing vector has no outcome. -/
def writeMetaF (s : State) (resource index : Nat) (item : Solanalib.Runtime.CpiMeta) : Option State
  :=
  (s.2.metas.current resource).map fun values =>
    metasFocus.set s (s.2.metas.set resource (some (values.set index item)))

/-! ## The CPI provider

The pre-check and the reply reading are shared with the provider of the value checker
(`Onchain.providerF`). -/

/-- The borrow pre-check of solana-cpi 3.1.0 on the current borrow world: for each
instruction meta, the first AccountInfo with its key must admit a borrow of
both cells (exclusive if the meta is writable). -/
def precheck (s : AccountInfo.State) (r : CpiRequest.Request AccountInfo.Value) : Bool :=
  r.instruction.metas.all fun m =>
    match r.accounts.find? (·.key == m.key) with
    | none => true
    | some info =>
      let mode := if m.writableByte == 1 then Borrow.Mode.exclusive else .shared
      (match (Borrow.acquire s info.lamports mode .whole).1 with
        | .ok _ => true | .error _ => false) &&
        (match (Borrow.acquire s info.data mode .whole).1 with
          | .ok _ => true | .error _ => false)

/-- `ProgramError::from(u64)` (solana-program-error 3.0.1). -/
def programErrorOfU64 (v : Nat) : Token.Error :=
  let builtins : List Token.Error := [.Custom 0, .InvalidArgument, .InvalidInstructionData,
    .InvalidAccountData, .AccountDataTooSmall, .InsufficientFunds, .IncorrectProgramId,
    .MissingRequiredSignature, .AccountAlreadyInitialized, .UninitializedAccount,
    .NotEnoughAccountKeys, .AccountBorrowFailed, .MaxSeedLengthExceeded, .InvalidSeeds,
    .BorshIoError, .AccountNotRentExempt, .UnsupportedSysvar, .IllegalOwner,
    .MaxAccountsDataAllocationsExceeded, .InvalidRealloc, .MaxInstructionTraceLengthExceeded,
    .BuiltinProgramsMustConsumeComputeUnits, .InvalidAccountOwner, .ArithmeticOverflow,
    .Immutable, .IncorrectAuthority]
  if v % 2 ^ 32 = 0 ∧ 1 ≤ v / 2 ^ 32 ∧ v / 2 ^ 32 ≤ builtins.length then
    builtins.getD (v / 2 ^ 32 - 1) (.Custom 0)
  else .Custom (v % 2 ^ 32)

/-- The result of a CPI syscall return value. -/
def replyResult (ret : Nat) : Except Token.Error Unit :=
  if ret = 0 then .ok () else .error (programErrorOfU64 ret)

/-- The CPI, computed as the provider of the value checker: a failed pre-check
returns `AccountBorrowFailed` without reaching the syscall; otherwise the
scripted reply is returned and the request is logged with the Rc counts at the
call. Without a scripted reply there is no outcome. -/
def cpiF (env : Env) (s : State) (request : CpiRequest.Request AccountInfo.Value) :
    Option (Outcome State (Except Token.Error Unit) Unwind Terminal) :=
  if precheck s.1 request then
    env.cpiReply.map fun ret =>
      .returned (replyResult ret) (s.1, { s.2 with cpiLog := s.2.cpiLog ++ [(request, s.2.rc)] })
  else some (.returned (.error .AccountBorrowFailed) s)

/-! ## Collection -/

/-- The collection protocol: no internal chunk, completion by
`guards.fromList`, and the default (acquisition) cleanup order. Before
completion there is no storage to retire; a returned vector retires its slot,
as in `AllocatedCollect.referenceProtocol`. -/
def collectProtocol : AllocatedCollect.Protocol Extra Nat Unwind Terminal where
  internal := fun _ _ _ _ => False
  finish := guardsOps.fromList
  retire := fun resource _ before outcome =>
    match resource with
    | none => outcome = .returned () before
    | some identity => (Owned.vectorReference.focus guardsFocus).drop before identity outcome
  double := fun _ original later terminal => terminal = (original, later)

/-- The protocol has no internal chunk. -/
theorem collectProtocol_internal (index : Nat) (acquired : List AllocatedCollect.Element)
    (s : State) (o : Outcome State Unit Unwind Terminal) :
    ¬ collectProtocol.internal index acquired s o :=
  fun h => h

/-- The storage retirement of the protocol, computed: an in-progress collector
leaves the state unchanged, and a returned vector retires its slot. -/
def collectRetireF (resource : Option Nat) (_ : List AllocatedCollect.Element) :
    State → Option (Outcome State Unit Unwind Terminal) :=
  fun s =>
    match resource with
    | none => some (.returned () s)
    | some identity => (VecPrims.reference.focus guardsFocus).dropF s identity

/-- The storage retirement of the protocol admits exactly `collectRetireF`. -/
theorem collectRetire_fn (resource : Option Nat) (acquired : List AllocatedCollect.Element) :
    DFn (collectProtocol.retire resource acquired) (collectRetireF resource acquired) := by
  intro s o
  cases resource with
  | none => exact ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
  | some identity => exact (VecPrims.reference.focus guardsFocus).drop_fn s identity o

/-- The protocol keeps the default partial-cleanup order, the acquisition order. -/
theorem collectOrder_eq (s : State) (acquired : List AllocatedCollect.Element) :
    collectProtocol.partialOrder s acquired = acquired :=
  rfl

/-- The terminal reason of the index for a destructor that unwinds during an
unwind: the pair of reasons. -/
def dbl (_ : State) (original later : Unwind) : Terminal := (original, later)

/-- The double-unwind policy of the protocol is the graph of `dbl`. -/
theorem collectDouble_fn (s : State) (original later : Unwind) (t : Terminal) :
    collectProtocol.double s original later t ↔ t = dbl s original later :=
  Iff.rfl

/-! ## The closed index -/

/-- The types and primitive dependencies of the closed index. -/
def closedTypes (env : Env) : Types where
  Extra := Extra
  ByteResource := Nat
  MetaResource := Nat
  InfoResource := Nat
  GuardResource := Nat
  DiscResource := Nat
  SeedResource := Nat
  SeedRefResource := Nat
  Unwind := Unwind
  Terminal := Terminal
  wordBits := 64
  tokenEnumSize := 128
  bytes := bytesOps
  metas := metasOps
  infos := infosOps
  infoLiteral := infoLiteral
  guards := guardsOps
  discriminators := discriminatorsOps
  paddingBytes := bytesOps
  seedOps := seedOps
  rc := rcOps
  ownerAt := fun _ owner => (env.owners[owner.id]?).getD .zero
  pdaSyscall := fun s request o => pdaSyscallF env s request = some o
  raise := fun s reason o => o = .unwound reason s
  doubleUnwind := fun _ original later terminal => terminal = (original, later)
  writeMeta := fun before resource index item after =>
    writeMetaF before resource index item = some after

/-- The two explicit dependencies of the closed index: the protocol
collection and the scripted CPI. -/
def closedDependencies (env : Env) : Dependencies (closedTypes env) where
  collect := AllocatedCollect.protocolProvider collectProtocol
  invoke := fun s request o => cpiF env s request = some o

/-- The closed index of a record. -/
def Index (env : Env) : OnchainAllocated.Index := ⟨closedTypes env, closedDependencies env⟩

/-- The collection dependency of the closed index is the protocol provider. -/
theorem collect_eq (env : Env) :
    (Index env).dependencies.collect = AllocatedCollect.protocolProvider collectProtocol :=
  rfl

/-- The CPI of the closed index admits exactly `cpiF env`. -/
theorem cpi_fn (env : Env) : Fn (Index env).dependencies.invoke (cpiF env) :=
  fun _ _ _ => Iff.rfl

/-- The literal work never asks for another internal chunk. -/
theorem noAgain (env : Env) : NoAgain (Index env).types.infoLiteral := by
  rintro before ⟨count, values⟩ after h
  change (if values.length < count then _ else _) at h
  split at h
  · nomatch h
  · nomatch h.2

/-- The computed primitives of the closed index. -/
def prims (env : Env) : Prims (Index env).types where
  bytes := bytesPrims
  metas := metasPrims
  infos := infosPrims
  guards := guardsPrims
  discriminators := discriminatorsPrims
  paddingBytes := bytesPrims
  seedBytes := bytesPrims
  seeds := emptyOnlyPrims seedsFocus
  seedRefs := emptyOnlyPrims seedRefsFocus
  literalWorkF := literalWorkF
  literalWork_fn := literalWork_fn
  literalFinishF := infosPrims.fromListF
  literalFinish_fn := infosPrims.fromList_fn
  literalRetireF := literalRetireF
  literalRetire_fn := literalRetire_fn
  rc := rcPrims
  pdaSyscallF := pdaSyscallF env
  pdaSyscall_fn := fun _ _ _ => Iff.rfl
  raiseF := raiseF
  raise_fn := raise_fn
  dbl := dbl
  double_fn := fun _ _ _ _ => Iff.rfl
  writeMetaF := writeMetaF
  writeMeta_fn := fun _ _ _ _ _ => Iff.rfl

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainIndex
