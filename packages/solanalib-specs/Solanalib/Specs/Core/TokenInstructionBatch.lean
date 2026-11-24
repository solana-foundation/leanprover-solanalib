/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstruction
public import Solanalib.Specs.Core.AccountView
public import Solanalib.Specs.Core.CpiRequest

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Batch

/-- An account descriptor retains the live account identity for the address,
lamports, data and owner references. The other public fields are copied when
the source initializes this particular entry. Raw pointers and padding are
outside this value model. -/
structure CpiAccount where
  /-- Identity underlying the live address, lamports, data and owner references. -/
  account : AccountView.Handle
  /-- Data length copied when this entry is initialized. -/
  dataLen : Nat
  /-- The initializer supplies zero because AccountView has no rent epoch. -/
  rentEpoch : Nat
  /-- Signer flag copied at initialization. -/
  isSigner : Bool
  /-- Writable flag copied at initialization. -/
  isWritable : Bool
  /-- Executable flag copied at initialization. -/
  executable : Bool
  deriving DecidableEq, Repr

/-- The source initializer copies length and flags, retains field references,
and supplies zero for the missing rent epoch. -/
def cpiAccount (world : AccountView.State) (handle : AccountView.Handle) : CpiAccount :=
  let account := world.account handle
  ⟨handle, account.dataLen, 0, account.metadata.signer,
    account.metadata.writable, account.metadata.executable⟩

/-- Metadata retains an address reference rather than a cached public key. -/
abbrev Meta := Solanalib.Specs.Core.Instruction.RefMeta AccountView.AddressRef

/-- Metadata flag order is made explicit here: signer, then writable. -/
def accountMetaRef (handle : AccountView.Handle) (isSigner isWritable : Bool) : Meta :=
  ⟨⟨handle⟩, isSigner, isWritable⟩

/-- Caller-owned, separately borrowed buffers. `none` records uninitialized
storage; writes and failures retain all entries outside their actual ranges. -/
structure Buffers where
  /-- Caller-supplied mutable byte storage, including uninitialized suffixes. -/
  data : List (Option UInt8)
  /-- Caller-supplied mutable CpiAccount storage. -/
  accounts : List (Option CpiAccount)
  /-- Caller-supplied mutable instruction-metadata storage. -/
  instructionAccounts : List (Option Meta)

/-- The returned Batch descriptor refers to the three selected buffers.
These are committed lengths, independent of partially initialized suffixes. -/
structure Lengths where
  /-- Committed data prefix, including the discriminator. -/
  data : Nat
  /-- Committed CpiAccount prefix. -/
  accounts : Nat
  /-- Committed instruction-metadata prefix. -/
  instructionAccounts : Nat
  deriving DecidableEq, Repr

/-- Account and ambient callback state. Callbacks may change these values;
the exclusive batch-buffer borrows in the source keep buffers outside their frame. -/
structure Context (Ambient : Type) where
  /-- The common current account and identified-lease state. -/
  world : AccountView.State
  /-- Arbitrary additional effects visible to the supplied callback interpretation. -/
  ambient : Ambient

/-- One selected batch and its callback context. Other batches and allocations
belong to the ambient interpretation of the caller, not an implicitly copied pool. -/
structure State (Ambient : Type) where
  /-- The callback-accessible state. -/
  context : Context Ambient
  /-- The separately borrowed Batch storage, outside callback ownership. -/
  buffers : Buffers
  /-- Batch lengths change only after all three writers succeed. -/
  lengths : Lengths

/-- Mathematical values for the source amount and decimals arguments. -/
structure SingleTransfer where
  /-- Source token account reference. -/
  fromAccount : AccountView.Handle
  /-- Token mint reference. -/
  mint : AccountView.Handle
  /-- Destination token account reference. -/
  toAccount : AccountView.Handle
  /-- Owner/delegate or multisig authority reference. -/
  authority : AccountView.Handle
  /-- Mathematical amount; the Rust binding supplies the source u64 bound. -/
  amount : Nat
  /-- Mathematical decimals; the Rust binding supplies the source u8 bound. -/
  decimals : Nat
  deriving DecidableEq, Repr

/-- Generic signer values remain distinct from the accounts returned by their
callbacks. Repeated values and aliases are retained in their original order. -/
structure Transfer (Signer : Type) extends SingleTransfer where
  /-- Ordered signer values, each independently visited by both AsRef passes. -/
  multisigSigners : List Signer

/-- The specialized source constructor supplies an empty signer slice and
retains all four account references and both integer arguments. -/
def singleTransfer (args : SingleTransfer) : Transfer AccountView.Handle :=
  ⟨args, []⟩

/-- Exactly the bytes returned by the checked-transfer data writer. -/
def transferData {Signer : Type} (args : Transfer Signer) : Bytes :=
  Instruction.transferCheckedData args.amount args.decimals

/-- Write a supplied range in order. Call sites check capacity first; unlike
list splicing this primitive never enlarges the buffer of a caller. -/
def writeAt {Value : Type} (buffer : List (Option Value)) (offset : Nat)
    (values : List Value) : List (Option Value) :=
  match values with
  | [] => buffer
  | value :: rest => writeAt (buffer.set offset (some value)) (offset + 1) rest

/-- Every write retains the allocated buffer length, including failure suffixes. -/
theorem writeAt_length {Value : Type} (buffer : List (Option Value)) (offset : Nat)
    (values : List Value) : (writeAt buffer offset values).length = buffer.length := by
  induction values generalizing buffer offset with
  | nil => rfl
  | cons value rest ih =>
    simp only [writeAt, ih, List.length_set]

/-- A new Batch writes only its discriminator. Empty data buffers return
InvalidArgument without touching any of the three buffers. -/
def newBatch (before : Buffers) : Except Error Lengths × Buffers :=
  if before.data.isEmpty then (.error .InvalidArgument, before)
  else (.ok ⟨1, 0, 0⟩, { before with data := before.data.set 0 (some 255) })

/-- A committed prefix fits the supplied allocation and has no uninitialized slot. -/
def PrefixReady {Value : Type} (buffer : List (Option Value)) (length : Nat) : Prop :=
  length ≤ buffer.length ∧ (buffer.take length).all Option.isSome = true

/-- Mathematical invocation needs exactly three complete committed prefixes.
These gates are consumed by decoding; Rust storage, private-state and retained
reference validity are separate interpretation obligations. -/
def InvocationReady {Ambient : Type} (state : State Ambient) : Prop :=
  PrefixReady state.buffers.data state.lengths.data ∧
  PrefixReady state.buffers.accounts state.lengths.accounts ∧
  PrefixReady state.buffers.instructionAccounts state.lengths.instructionAccounts

/-- The fixed data writer checks its own remaining slice before any write. -/
def writeData {Ambient Signer : Type} (before : State Ambient) (args : Transfer Signer) :
    Except Error Nat × State Ambient :=
  if before.buffers.data.length - (before.lengths.data + 2) < 10 then
    (.error .InvalidArgument, before)
  else
    let data := writeAt before.buffers.data (before.lengths.data + 2) (transferData args)
    (.ok 10, { before with buffers := { before.buffers with data } })

/-- Initialize one account entry from the world at this exact point in the
callback sequence. Later callbacks do not refresh its copied length or flags. -/
def writeAccount {Ambient : Type} (before : State Ambient) (offset : Nat)
    (handle : AccountView.Handle) : State Ambient :=
  let accounts := before.buffers.accounts.set offset (some (cpiAccount before.context.world handle))
  { before with buffers := { before.buffers with accounts } }

/-- Metadata stores the address-reference identity and fixed flags of the account. -/
def writeMeta {Ambient : Type} (before : State Ambient) (offset : Nat)
    (handle : AccountView.Handle) (isSigner isWritable : Bool) : State Ambient :=
  { before with buffers := { before.buffers with
      instructionAccounts := before.buffers.instructionAccounts.set offset
        (some (accountMetaRef handle isSigner isWritable)) } }

/-- The four account descriptors precede all signer callbacks. -/
def writeBaseAccounts {Ambient Signer : Type} (before : State Ambient)
    (args : Transfer Signer) : State Ambient :=
  { before with buffers := { before.buffers with
    accounts := writeAt before.buffers.accounts before.lengths.accounts
      ([args.fromAccount, args.mint, args.toAccount, args.authority].map
        (cpiAccount before.context.world)) } }

/-- Metadata order is source, mint, destination, authority. The authority is a
signer exactly when the supplied multisig-signer slice is empty. -/
def writeBaseMetas {Ambient Signer : Type} (before : State Ambient)
    (args : Transfer Signer) : State Ambient :=
  let instructionAccounts :=
    writeAt before.buffers.instructionAccounts before.lengths.instructionAccounts
      [accountMetaRef args.fromAccount false true, accountMetaRef args.mint false false,
       accountMetaRef args.toAccount false true,
       accountMetaRef args.authority args.multisigSigners.isEmpty false]
  { before with buffers := { before.buffers with instructionAccounts } }

/-- Commit only after every writer succeeds. Header counts use the u8 cast of Rust;
the actual committed lengths retain their full mathematical values. -/
def commit {Ambient : Type} (before : State Ambient)
    (writtenData writtenAccounts writtenMetas : Nat) : State Ambient :=
  let data := writeAt before.buffers.data before.lengths.data
    [UInt8.ofNat writtenMetas, UInt8.ofNat writtenData]
  { before with
    buffers := { before.buffers with data }
    lengths := ⟨before.lengths.data + writtenData + 2,
      before.lengths.accounts + writtenAccounts,
      before.lengths.instructionAccounts + writtenMetas⟩ }

/-- Decode exactly the committed number of initialized slots. An absent or
uninitialized slot rejects the mathematical projection; it never compacts the
remaining values or invents a Rust error for reading uninitialized memory. -/
def initializedPrefix {Value : Type} : List (Option Value) → Nat → Option (List Value)
  | _, 0 => some []
  | some value :: rest, length + 1 => (initializedPrefix rest length).map (value :: ·)
  | _, _ + 1 => none

/-- Successful decoding preserves the position of every slot and the exact length. -/
theorem initializedPrefix_exact {Value : Type} {buffer : List (Option Value)}
    {length : Nat} {values : List Value}
    (decoded : initializedPrefix buffer length = some values) :
    values.length = length ∧ values.map some = buffer.take length := by
  induction length generalizing buffer values with
  | zero =>
    simp only [initializedPrefix, Option.some.injEq] at decoded
    subst values
    exact ⟨rfl, by simp⟩
  | succ length ih =>
    cases buffer with
    | nil => cases decoded
    | cons entry rest =>
      cases entry with
      | none => cases decoded
      | some value =>
        cases tail : initializedPrefix rest length with
        | none => simp [initializedPrefix, tail] at decoded
        | some suffix =>
          simp only [initializedPrefix, tail, Option.map_some, Option.some.injEq] at decoded
          subst values
          obtain ⟨count, same⟩ := ih tail
          exact ⟨by simp [count], by simp [same]⟩

/-- Initialization and bounds suffice to decode a complete prefix; this is the
source-admission premise consumed before making the opaque call. -/
theorem PrefixReady.decode {Value : Type} {buffer : List (Option Value)} {length : Nat}
    (ready : PrefixReady buffer length) : ∃ values, initializedPrefix buffer length = some values
      := by
  induction length generalizing buffer with
  | zero => exact ⟨[], by simp [initializedPrefix]⟩
  | succ length ih =>
    cases buffer with
    | nil => simp [PrefixReady] at ready
    | cons entry rest =>
      cases entry with
      | none => simp [PrefixReady] at ready
      | some value =>
        have tailReady : PrefixReady rest length := by
          simpa [PrefixReady] using ready
        obtain ⟨values, decoded⟩ := ih tailReady
        exact ⟨value :: values, by simp [initializedPrefix, decoded]⟩

/-- A successful decoder establishes the initialization condition as well. -/
theorem initializedPrefix_ready {Value : Type} {buffer : List (Option Value)}
    {length : Nat} {values : List Value}
    (decoded : initializedPrefix buffer length = some values) : PrefixReady buffer length := by
  obtain ⟨count, same⟩ := initializedPrefix_exact decoded
  constructor
  · have sizes := congrArg List.length same
    simp only [List.length_map, List.length_take] at sizes
    omega
  · rw [← same]
    simp

/-- The value/reference descriptor passed at the opaque provider boundary.
Metadata references remain live identities, while instruction bytes and the
already copied CPI fields are retained exactly. -/
structure Request where
  /-- The fixed legacy Token program identity supplied by Batch. -/
  programId : Solanalib.Runtime.Pubkey
  /-- Committed metadata entries retaining their live address-reference identities. -/
  instructionAccounts : List Meta
  /-- The exact committed instruction byte prefix. -/
  data : Bytes
  /-- Committed CPI descriptors with copied fields and live account identities. -/
  accounts : List CpiAccount
  /-- The exact nested signer/seed tree supplied to the wrapper. -/
  signers : List (List Bytes)

/-- Observe keys only when a consumer explicitly reads the retained address
references. The provider itself receives the uncollapsed descriptor. -/
def Request.observe (args : Request) (world : AccountView.State) : CpiRequest.Request CpiAccount :=
  CpiRequest.signed
    (Solanalib.Specs.Core.Instruction.make args.programId
      (args.instructionAccounts.map
        (Solanalib.Specs.Core.Instruction.RefMeta.observe
          (fun reference => reference.value world))) args.data)
    args.accounts args.signers

/-- Construct a request only from three complete initialized prefixes.
No request exists for an invalid prefix, and no uncommitted suffix is read. -/
def request {Ambient : Type} (before : State Ambient) (signers : List (List Bytes)) :
    Option Request := do
  let metas ← initializedPrefix before.buffers.instructionAccounts
    before.lengths.instructionAccounts
  let data ← initializedPrefix before.buffers.data before.lengths.data
  let accounts ← initializedPrefix before.buffers.accounts before.lengths.accounts
  return ⟨legacyProgramId, metas, data, accounts, signers⟩

/-- The request records each successful prefix decoder without dropping entries. -/
theorem request_parts {Ambient : Type} {before : State Ambient} {signers : List (List Bytes)}
    {sent : Request} (decoded : request before signers = some sent) :
    initializedPrefix before.buffers.instructionAccounts before.lengths.instructionAccounts =
      some sent.instructionAccounts ∧
    initializedPrefix before.buffers.data before.lengths.data = some sent.data ∧
    initializedPrefix before.buffers.accounts before.lengths.accounts = some sent.accounts ∧
    sent.signers = signers ∧ sent.programId = legacyProgramId := by
  unfold request at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨metas, metasDecoded, data, dataDecoded, accounts, accountsDecoded, same⟩ := decoded
  cases same
  exact ⟨metasDecoded, dataDecoded, accountsDecoded, rfl, rfl⟩

/-- Exactly the initialized-prefix admission gates supply a complete request. -/
theorem request_exists {Ambient : Type} {before : State Ambient}
    (ready : InvocationReady before) (signers : List (List Bytes)) :
    ∃ sent, request before signers = some sent := by
  obtain ⟨metas, metasDecoded⟩ := ready.2.2.decode
  obtain ⟨data, dataDecoded⟩ := ready.1.decode
  obtain ⟨accounts, accountsDecoded⟩ := ready.2.1.decode
  exact ⟨⟨legacyProgramId, metas, data, accounts, signers⟩,
    by simp [request, metasDecoded, dataDecoded, accountsDecoded]⟩

/-- The admission condition is exactly the domain of the decoder: it neither
permits a missing prefix nor adds an unrelated premise to request construction. -/
theorem request_domain {Ambient : Type} (before : State Ambient) (signers : List (List Bytes)) :
    (∃ sent, request before signers = some sent) ↔ InvocationReady before := by
  constructor
  · rintro ⟨sent, decoded⟩
    obtain ⟨metas, data, accounts, _⟩ := request_parts decoded
    exact ⟨initializedPrefix_ready data, initializedPrefix_ready accounts, initializedPrefix_ready
      metas⟩
  · exact fun ready => request_exists ready signers

/-- Source constructor equality retains the empty signer slice for every input. -/
theorem singleTransfer_signers (args : SingleTransfer) :
    (singleTransfer args).multisigSigners = [] := rfl

/-- No sorting or seed normalization occurs in a decoded invocation request. -/
theorem request_signers {Ambient : Type} {before : State Ambient} {signers : List (List Bytes)}
    {sent : Request} (decoded : request before signers = some sent) :
    sent.signers = signers := (request_parts decoded).2.2.2.1

/-- Batch always requests the fixed legacy Token program. -/
theorem request_program {Ambient : Type} {before : State Ambient} {signers : List (List Bytes)}
    {sent : Request} (decoded : request before signers = some sent) :
    sent.programId = legacyProgramId := (request_parts decoded).2.2.2.2

/-- Committing headers and lengths never changes callback state. -/
theorem commit_context {Ambient : Type} (before : State Ambient) (data accounts metas : Nat) :
    (commit before data accounts metas).context = before.context := rfl

end Solanalib.Specs.Core.Token.Batch
