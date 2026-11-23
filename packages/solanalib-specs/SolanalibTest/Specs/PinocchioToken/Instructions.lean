/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioToken.Instructions
public import Solanalib.Specs.Core.TokenInstructionBatchProperties

@[expose] public section

open Solanalib.Specs

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioToken.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Batch

/-- An empty data buffer rejects construction and preserves both other buffers. -/
theorem empty_data_constructor :
    newBatch ⟨[], [some (cpiAccount AccountView.witnessState AccountView.witnessHandle)],
      [some (accountMetaRef AccountView.witnessHandle true false)]⟩ =
    (.error .InvalidArgument,
      ⟨[], [some (cpiAccount AccountView.witnessState AccountView.witnessHandle)],
        [some (accountMetaRef AccountView.witnessHandle true false)]⟩) := rfl

/-- Nonempty construction overwrites only byte zero, initializes no accounts,
and sets the three committed lengths to one/zero/zero. -/
theorem constructor_first_byte_only :
    newBatch ⟨[some 17, some 31, none], [none], [none, none]⟩ =
      (.ok ⟨1, 0, 0⟩, ⟨[some 255, some 31, none], [none], [none, none]⟩) := rfl

/-- Single-owner construction retains all inputs and the empty signer slice. -/
theorem constructor_retains_references (args : SingleTransfer) :
    (singleTransfer args).toSingleTransfer = args ∧
      (singleTransfer args).multisigSigners = [] := ⟨rfl, rfl⟩

/-- The source u64 wire order is little endian, not decimal or network order. -/
theorem transfer_wire_bytes : transferData sampleTransfer = [12, 1, 2, 0, 0, 0, 0, 0, 0, 6] := rfl

/-- Full source-width decimals remain accepted, without an invented policy cap. -/
theorem full_integer_domains :
    transferData (singleTransfer
      { sampleSingle with amount := Solanalib.Runtime.U64_LIMIT - 1, decimals := 255 }) =
      [12, 255, 255, 255, 255, 255, 255, 255, 255, 255] := rfl

/-- The registered nonempty signer really executes both passes. -/
theorem nonempty_generic_execution :
    intoBatch sampleAsRef sampleState sampleTransfer (.returned (.ok ()) sampleCommitted) :=
  sampleInto_execute

/-- Only final success commits the header and thirteen-byte initialized prefix. -/
theorem committed_data : sampleCommitted.buffers.data =
    [some 255, some 5, some 10, some 12, some 1, some 2, some 0,
      some 0, some 0, some 0, some 0, some 0, some 6] := rfl

/-- Committed counts preserve five duplicate account entries and both callback effects. -/
theorem committed_counts_and_effects :
    sampleCommitted.lengths = ⟨13, 5, 5⟩ ∧ sampleCommitted.context.ambient = 2 := ⟨rfl, rfl⟩

/-- There is no address deduplication even when every source reference aliases. -/
theorem duplicate_accounts_preserved :
    (request sampleCommitted []).map (fun sent => sent.accounts.map CpiAccount.account) =
      some (List.replicate 5 AccountView.witnessHandle) := rfl

/-- Metadata preserves source/mint/destination/authority/signer flag order. -/
theorem ordered_metadata_flags :
    (request sampleCommitted []).map (fun sent => sent.instructionAccounts.map
        (fun entry => (entry.isSigner, entry.isWritable))) =
      some [(false, true), (false, false), (false, true), (false, false), (true, false)] := rfl

/-- The single-owner authority is a signer, unlike the nonempty multisig case. -/
theorem single_owner_authority_signs :
    ((writeBaseMetas sampleState (singleTransfer sampleSingle)).buffers.instructionAccounts[3]?).map
      (fun entry => entry.map (fun item => (item.isSigner, item.isWritable))) =
      some (some (true, false)) := rfl

/-- This sample callback is deterministic, without requiring determinism of the family. -/
theorem sample_deterministic : Deterministic sampleAsRef := by
  intro before signer first second left right
  exact left.2.trans right.2.symm

/-- An invented ordinary error cannot coexist with the actual success of the sample. -/
theorem no_fabricated_success_error (reason : Solanalib.Runtime.InstrError) (after : State Nat) :
    ¬ intoBatch sampleAsRef sampleState sampleTransfer (.returned (.error reason) after) := by
  intro error
  have same := intoBatch_deterministic sampleAsRef sample_deterministic
    sampleState sampleTransfer _ _ sampleInto_execute error
  cases same

/-- A callback that never returns can still be bypassed by an earlier source error. -/
def noCallback : AsRef sampleTypes := fun _ _ _ => False

/-- Header room is checked before the data writer or any generic callback. -/
def headerShort : State Nat :=
  { sampleState with buffers := { sampleBuffers with data := [some 255, none] } }

/-- Header failure makes no callback and performs no writes. -/
theorem header_error_before_callback :
    intoBatch noCallback headerShort sampleTransfer (.returned (.error .InvalidArgument)
      headerShort) :=
  intoBatch_header_error noCallback headerShort sampleTransfer (by decide)

/-- A header may fit while the fixed payload slice is one byte too short. -/
def dataShort : State Nat :=
  { sampleState with buffers := { sampleBuffers with data := some 255 :: List.replicate 11 none } }

/-- Data failure leaves all buffers and counters unchanged and calls nobody. -/
theorem data_error_before_callback :
    intoBatch noCallback dataShort sampleTransfer (.returned (.error .InvalidArgument) dataShort)
      := rfl

/-- Two simultaneous faults: no account capacity and source/destination already borrowed. -/
def accountShortBorrowed : State Nat :=
  ⟨⟨AccountView.witnessGuardState .shared, 0⟩,
    { sampleBuffers with accounts := [] }, ⟨1, 0, 0⟩⟩

/-- The account-capacity error wins over AccountBorrowFailed, after data was written. -/
theorem account_capacity_before_borrow :
    intoBatch noCallback accountShortBorrowed sampleTransfer
      (.returned (.error .InvalidArgument) (writeData accountShortBorrowed sampleTransfer).2) := by
  apply intoBatch_account_error noCallback accountShortBorrowed sampleTransfer
    (writeData accountShortBorrowed sampleTransfer).2
    (writeData accountShortBorrowed sampleTransfer).2 10 .InvalidArgument (by decide) rfl
  rfl

/-- Capacity failure retains the ten data writes, with the header still uncommitted. -/
theorem account_error_keeps_data :
    ((writeData accountShortBorrowed sampleTransfer).2.buffers.data.drop 3 =
      [some 12, some 1, some 2, some 0, some 0, some 0, some 0, some 0, some 0, some 6]) ∧
    (writeData accountShortBorrowed sampleTransfer).2.lengths = ⟨1, 0, 0⟩ := ⟨rfl, rfl⟩

/-- With capacity available, the actual source/destination lease is checked. -/
def sourceBorrowed : State Nat :=
  { sampleState with context := ⟨AccountView.witnessGuardState .shared, 0⟩ }

/-- The borrow conflict is derived from shared slots and retains preceding data writes. -/
theorem source_borrow_error :
    intoBatch noCallback sourceBorrowed sampleTransfer
      (.returned (.error .AccountBorrowFailed) (writeData sourceBorrowed sampleTransfer).2) := by
  apply intoBatch_account_error noCallback sourceBorrowed sampleTransfer
    (writeData sourceBorrowed sampleTransfer).2
    (writeData sourceBorrowed sampleTransfer).2 10 .AccountBorrowFailed (by decide) rfl
  rfl

/-- The metadata slice is independently too short after the first callback pass succeeds. -/
def metadataShort : State Nat :=
  { sampleState with buffers := { sampleBuffers with instructionAccounts := List.replicate 4 none }
    }

/-- The actual intermediate state contains all five CPI descriptors and one callback effect. -/
def metadataShortAfterAccounts : State Nat :=
  writeAccount
    { writeBaseAccounts (writeData metadataShort sampleTransfer).2 sampleTransfer with
      context := ⟨AccountView.witnessState, 1⟩ } 4 AccountView.witnessHandle

/-- First-pass success does not depend on later metadata capacity. -/
theorem metadata_short_accounts_execute :
    writeAccounts sampleAsRef (writeData metadataShort sampleTransfer).2 sampleTransfer
      (.returned (.ok 5) metadataShortAfterAccounts) := by
  apply writeAccounts_pass sampleAsRef (writeData metadataShort sampleTransfer).2 sampleTransfer
    (.returned () metadataShortAfterAccounts) (by decide) (by decide)
  apply signerPass_return sampleAsRef writeAccount
    (writeBaseAccounts (writeData metadataShort sampleTransfer).2 sampleTransfer)
    4 () [] AccountView.witnessHandle ⟨AccountView.witnessState, 1⟩
    (.returned () metadataShortAfterAccounts)
  · exact ⟨AccountView.witness_ready, rfl⟩
  · rfl

/-- Metadata capacity failure preserves the entire first callback pass, without committing counts.
-/
theorem metadata_error_keeps_first_pass :
    intoBatch sampleAsRef metadataShort sampleTransfer
      (.returned (.error .InvalidArgument) metadataShortAfterAccounts) :=
  intoBatch_meta_error sampleAsRef metadataShort sampleTransfer
    (writeData metadataShort sampleTransfer).2 metadataShortAfterAccounts metadataShortAfterAccounts
    10 5 .InvalidArgument (by decide) rfl metadata_short_accounts_execute rfl

/-- Both lengths and visible invocation prefixes stay uncommitted after that failure. -/
theorem failed_metadata_prefixes :
    metadataShortAfterAccounts.lengths = ⟨1, 0, 0⟩ ∧
    metadataShortAfterAccounts.context.ambient = 1 ∧
    request metadataShortAfterAccounts [] = some (sampleRequest []) :=
  ⟨rfl, rfl, rfl⟩

/-- Unchecked invocation can never manufacture an ordinary error from its unit result. -/
theorem unchecked_no_ordinary_error (after : State Nat) (reason : Solanalib.Runtime.InstrError) :
    ¬ invokeSigned sampleState sampleInvokeCall (.returned (.error reason) after) :=
  invokeSigned_no_error sampleState after sampleInvokeCall reason

/-- The original nested seed list is retained, including empty signers and seeds. -/
theorem signer_tree_preserved :
    (request sampleCommitted [[], [[], [7, 8]], [[9]]]).map Request.signers =
      some [[], [[], [7, 8]], [[9]]] := rfl

/-- Invocation sees the retained metadata identities and only the committed prefix. -/
theorem request_live_metadata_identities :
    (request sampleCommitted []).map
      (fun sent => sent.instructionAccounts.map (fun entry => entry.address.account)) =
      some (List.replicate 5 AccountView.witnessHandle) := rfl

/-- The same generic signer returns once and then unwinds on its second call. -/
def secondPassUnwind : AsRef sampleTypes := fun before signer outcome =>
  if before.ambient = 0 then sampleAsRef before signer outcome
  else outcome = .unwound 73 { before with ambient := before.ambient + 1 }

/-- One normal callback initializes the account entry before the later unwind. -/
theorem first_pass_before_unwind :
    writeAccounts secondPassUnwind sampleAfterData sampleTransfer
      (.returned (.ok 5) sampleAfterAccounts) := by
  apply writeAccounts_pass secondPassUnwind sampleAfterData sampleTransfer
    (.returned () sampleAfterAccounts) (by decide) (by decide)
  apply signerPass_return secondPassUnwind writeAccount
    (writeBaseAccounts sampleAfterData sampleTransfer) 4 () [] AccountView.witnessHandle
    ⟨AccountView.witnessState, 1⟩ (.returned () sampleAfterAccounts)
  · exact ⟨AccountView.witness_ready, rfl⟩
  · rfl

/-- All four base metadata entries precede the second callback, whose own
metadata entry is never written when it unwinds. -/
def beforeUnwind : State Nat :=
  { writeBaseMetas sampleAfterAccounts sampleTransfer with context := ⟨AccountView.witnessState, 2⟩
    }

/-- The second pass retains the first pass, base metadata writes and the actual unwind effect. -/
theorem second_pass_unwind_execute :
    writeMetas secondPassUnwind sampleAfterAccounts sampleTransfer (.unwound 73 beforeUnwind) := by
  apply writeMetas_pass secondPassUnwind sampleAfterAccounts sampleTransfer
    (.unwound 73 beforeUnwind) (by decide)
  exact signerPass_unwind secondPassUnwind
    (fun state offset handle => writeMeta state offset handle true false)
    (writeBaseMetas sampleAfterAccounts sampleTransfer) 4 () [] 73
    ⟨AccountView.witnessState, 2⟩ rfl

/-- The whole body propagates that unwind, without committing or synthesizing Ok. -/
theorem into_batch_second_pass_unwind :
    intoBatch secondPassUnwind sampleState sampleTransfer (.unwound 73 beforeUnwind) := by
  have header : ¬ sampleState.buffers.data.length < sampleState.lengths.data + 2 := by decide
  have data : writeData sampleState sampleTransfer = (.ok 10, sampleAfterData) := rfl
  simp only [intoBatch, header, ↓reduceIte, data]
  refine ⟨.returned (.ok 5) sampleAfterAccounts, first_pass_before_unwind, ?_⟩
  exact ⟨.unwound 73 beforeUnwind, second_pass_unwind_execute, rfl⟩

/-- Unwind preserves actual initialized entries, leaves its own slot empty,
and does not commit lengths despite the changed ambient state. -/
theorem unwind_partial_footprint :
    beforeUnwind.lengths = ⟨1, 0, 0⟩ ∧
    beforeUnwind.context.ambient = 2 ∧
    beforeUnwind.buffers.accounts[4]? =
      some (some (cpiAccount AccountView.witnessState AccountView.witnessHandle)) ∧
    beforeUnwind.buffers.instructionAccounts[3]? =
      some (some (accountMetaRef AccountView.witnessHandle false false)) ∧
    beforeUnwind.buffers.instructionAccounts[4]? = some none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A terminal callback relation contains only its reason, never a returned state. -/
def terminalCallback : AsRef sampleTypes := fun _ _ outcome => outcome = .terminated 91

/-- Terminal callback exits propagate through the account writer after base writes. -/
theorem account_pass_terminal :
    writeAccounts terminalCallback sampleAfterData sampleTransfer (.terminated 91) := by
  apply writeAccounts_pass terminalCallback sampleAfterData sampleTransfer
    (.terminated 91) (by decide) (by decide)
  exact signerPass_terminal terminalCallback writeAccount
    (writeBaseAccounts sampleAfterData sampleTransfer) 4 () [] 91 rfl

/-- The complete preparation does not fabricate an unwound or returned post-state for termination.
-/
theorem into_batch_terminal :
    intoBatch terminalCallback sampleState sampleTransfer (.terminated 91) := by
  have header : ¬ sampleState.buffers.data.length < sampleState.lengths.data + 2 := by decide
  have data : writeData sampleState sampleTransfer = (.ok 10, sampleAfterData) := rfl
  simp only [intoBatch, header, ↓reduceIte, data]
  exact ⟨.terminated 91, account_pass_terminal, rfl⟩

/-- An opaque unchecked provider may unwind with effects despite having a unit result type. -/
def unwindingProvider : InvokeCall sampleTypes :=
  ⟨[[]], fun before _ outcome => outcome = .unwound 37 { before with ambient := before.ambient + 9
    }⟩

/-- The wrapper retains the actual unwind reason and state of the provider. -/
theorem unchecked_unwind_effect :
    invokeSigned sampleState unwindingProvider
      (.unwound 37 { sampleState with context := ⟨AccountView.witnessState, 9⟩ }) :=
  ⟨sampleRequest unwindingProvider.signers, sampleRequest_decodes _,
    .unwound 37 ⟨AccountView.witnessState, 9⟩, rfl, rfl⟩

/-- A terminal provider produces no synthetic return value or post-state. -/
theorem unchecked_terminal_effect :
    invokeSigned sampleState
      (⟨[], fun _ _ outcome => outcome = .terminated 53⟩ : InvokeCall sampleTypes)
      (.terminated 53) := ⟨sampleRequest [], sampleRequest_decodes [], .terminated 53, rfl, rfl⟩

/-- A second account has a distinct key, copied length and signer flag. -/
def secondAccount : AccountView.Account :=
  { AccountView.Account.empty with
    metadata := ⟨.ofNat 13, true, false, false⟩
    dataLen := 1
    entryLen := 1
    backing := [99] }

/-- The optional lease belongs only to cell one, used for mint and authority. -/
def twoWorld (leased : Bool) : AccountView.State :=
  ⟨[⟨AccountView.Account.empty, Borrow.Policy.accountView⟩,
    ⟨secondAccount, Borrow.Policy.accountView⟩],
    if leased then [some ⟨⟨1⟩, .shared, 0, ⟨0, 1⟩⟩] else []⟩

/-- Both finite worlds satisfy the real shared cell/lease invariant. -/
theorem twoWorld_wellFormed (leased : Bool) : AccountView.State.WellFormed (twoWorld leased) := by
  constructor
  · constructor
    · intro id slot present
      cases leased with
      | false => simp [Borrow.State.lookupSlot, twoWorld] at present
      | true =>
        cases id with
        | zero =>
          simp [Borrow.State.lookupSlot, twoWorld] at present
          subst slot
          exact ⟨_, rfl⟩
        | succ id => simp [Borrow.State.lookupSlot, twoWorld] at present
    · intro handle cell present
      rcases handle with ⟨index⟩
      cases index with
      | zero =>
        simp [Borrow.State.lookupCell, twoWorld] at present
        subst cell
        cases leased <;> decide
      | succ index =>
        cases index with
        | zero =>
          simp [Borrow.State.lookupCell, twoWorld] at present
          subst cell
          cases leased <;> decide
        | succ index => simp [Borrow.State.lookupCell, twoWorld] at present
  · intro cell member
    simp only [twoWorld, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨rfl, AccountView.Account.empty_valid_core⟩
    · exact ⟨rfl, by unfold AccountView.Account.Valid; decide⟩

/-- The first handle is valid in either lease configuration. -/
theorem twoWorld_zero_ready (leased : Bool) : AccountView.Ready (twoWorld leased) ⟨0⟩ :=
  ⟨twoWorld_wellFormed leased, ⟨_, rfl⟩⟩

/-- The distinct second handle is also valid, even while borrowed. -/
theorem twoWorld_one_ready (leased : Bool) : AccountView.Ready (twoWorld leased) ⟨1⟩ :=
  ⟨twoWorld_wellFormed leased, ⟨_, rfl⟩⟩

/-- Source/destination are free; mint/authority alias the separately borrowed account. -/
def mintBorrowedTransfer : Transfer Unit :=
  ⟨⟨⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩, 513, 6⟩, []⟩

/-- The prepared Batch uses one well-formed two-account world. -/
def mintBorrowedState : State Nat :=
  { sampleState with context := ⟨twoWorld true, 0⟩ }

/-- Only the two source-selected borrow flags are tested. -/
theorem distinct_borrow_flags :
    AccountView.isBorrowed (twoWorld true) ⟨0⟩ = false ∧
    AccountView.isBorrowed (twoWorld true) ⟨1⟩ = true := ⟨rfl, rfl⟩

/-- Borrowed mint/authority references do not cause an invented AccountBorrowFailed. -/
theorem borrowed_mint_authority_accepted :
    writeAccounts noCallback mintBorrowedState mintBorrowedTransfer
      (.returned (.ok 4) (writeBaseAccounts mintBorrowedState mintBorrowedTransfer)) := by
  apply writeAccounts_pass noCallback mintBorrowedState mintBorrowedTransfer
    (.returned () (writeBaseAccounts mintBorrowedState mintBorrowedTransfer)) (by decide) (by
      decide)
  rfl

/-- This callback returns a different account on its second invocation, while
preserving every current source reference and recording both effects. -/
def alternatingAsRef : AsRef sampleTypes := fun before _ outcome =>
  AccountView.Ready before.world ⟨0⟩ ∧ AccountView.Ready before.world ⟨1⟩ ∧
    outcome = .returned (if before.ambient = 0 then ⟨1⟩ else ⟨0⟩)
      { before with ambient := before.ambient + 1 }

/-- Nonempty-signer preparation starts before either alternating callback. -/
def alternatingState : State Nat := { sampleState with context := ⟨twoWorld false, 0⟩ }

/-- The descriptor of the first callback points to cell one and copies its fields. -/
def alternatingAfterAccounts : State Nat :=
  writeAccount
    { writeBaseAccounts (writeData alternatingState sampleTransfer).2 sampleTransfer with
      context := ⟨twoWorld false, 1⟩ } 4 ⟨1⟩

/-- The metadata of the second callback points independently to cell zero. -/
def alternatingAfterMetas : State Nat :=
  writeMeta
    { writeBaseMetas alternatingAfterAccounts sampleTransfer with
      context := ⟨twoWorld false, 2⟩ } 4 ⟨0⟩ true false

/-- The actual first pass calls the signer once and stores its returned cell. -/
theorem alternating_accounts_execute :
    writeAccounts alternatingAsRef (writeData alternatingState sampleTransfer).2 sampleTransfer
      (.returned (.ok 5) alternatingAfterAccounts) := by
  apply writeAccounts_pass alternatingAsRef (writeData alternatingState sampleTransfer).2
    sampleTransfer
    (.returned () alternatingAfterAccounts) (by decide) (by decide)
  apply signerPass_return alternatingAsRef writeAccount
    (writeBaseAccounts (writeData alternatingState sampleTransfer).2 sampleTransfer)
    4 () [] ⟨1⟩ ⟨twoWorld false, 1⟩ (.returned () alternatingAfterAccounts)
  · exact ⟨twoWorld_zero_ready false, twoWorld_one_ready false, rfl⟩
  · rfl

/-- The actual second pass calls it again, rather than reusing the first handle. -/
theorem alternating_metas_execute :
    writeMetas alternatingAsRef alternatingAfterAccounts sampleTransfer
      (.returned (.ok 5) alternatingAfterMetas) := by
  apply writeMetas_pass alternatingAsRef alternatingAfterAccounts sampleTransfer
    (.returned () alternatingAfterMetas) (by decide)
  apply signerPass_return alternatingAsRef
    (fun state offset handle => writeMeta state offset handle true false)
    (writeBaseMetas alternatingAfterAccounts sampleTransfer)
    4 () [] ⟨0⟩ ⟨twoWorld false, 2⟩ (.returned () alternatingAfterMetas)
  · exact ⟨twoWorld_zero_ready false, twoWorld_one_ready false, rfl⟩
  · rfl

/-- Complete source preparation allows the two callback passes to produce different references. -/
theorem alternating_full_execution :
    intoBatch alternatingAsRef alternatingState sampleTransfer
      (.returned (.ok ()) (commit alternatingAfterMetas 10 5 5)) :=
  intoBatch_success alternatingAsRef alternatingState sampleTransfer
    (writeData alternatingState sampleTransfer).2 alternatingAfterAccounts alternatingAfterMetas
    10 5 5 (by decide) rfl alternating_accounts_execute alternating_metas_execute

/-- A five-entry account request and a five-entry metadata request retain their
distinct final signer identities, with no matching or deduplication added. -/
theorem two_pass_distinct_references :
    (request (commit alternatingAfterMetas 10 5 5) []).map
      (fun sent => sent.accounts.map CpiAccount.account) = some [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩] ∧
    (request (commit alternatingAfterMetas 10 5 5) []).map
      (fun sent => sent.instructionAccounts.map (fun entry => entry.address.account)) =
      some [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] := ⟨rfl, rfl⟩

/-- The copied descriptor fields come from the returned account of the first callback. -/
theorem copied_cpi_fields :
    (request (commit alternatingAfterMetas 10 5 5) []).bind (fun sent => sent.accounts[4]?) =
      some ⟨⟨1⟩, 1, 0, true, false, false⟩ := rfl

/-- A current-world observation may change while the reference
identities of the request and copied CPI fields remain unchanged. This is a model projection
control, not a claim that safe SDK code can mutate an address field. -/
theorem live_key_observation :
    (request sampleCommitted []).map (fun sent => (sent.observe
      ((Borrow.replaceCell AccountView.witnessState AccountView.witnessHandle
        { secondAccount with metadata := ⟨.ofNat 29, true, false, false⟩
          }).2)).instruction.metas.map
      Solanalib.Runtime.CpiMeta.key) = some (List.replicate 5 (.ofNat 29)) ∧
    (request sampleCommitted []).bind (fun sent => sent.accounts[0]?) =
      some ⟨⟨0⟩, 0, 0, false, false, false⟩ := ⟨rfl, rfl⟩

/-- A valid constant callback still executes once per signer in each pass. -/
def constantAsRef : AsRef sampleTypes := fun before _ outcome =>
  AccountView.Ready before.world AccountView.witnessHandle ∧
    outcome = .returned AccountView.witnessHandle before

/-- Repeat the immediate entry write for the closed constant-callback interpretation. -/
def repeatWrites (write : State Nat → Nat → AccountView.Handle → State Nat)
    (before : State Nat) (offset count : Nat) : State Nat :=
  match count with
  | 0 => before
  | count + 1 => repeatWrites write (write before offset AccountView.witnessHandle) (offset + 1)
    count

/-- Repeated immediate writes preserve every observation each individual write preserves. -/
theorem repeatWrites_preserves {Observed : Type}
    (write : State Nat → Nat → AccountView.Handle → State Nat) (observe : State Nat → Observed)
    (preserves : ∀ before offset handle, observe (write before offset handle) = observe before)
    (before : State Nat) (offset count : Nat) :
    observe (repeatWrites write before offset count) = observe before := by
  induction count generalizing before offset with
  | zero => rfl
  | succ count ih => exact (ih _ _).trans (preserves _ _ _)

/-- This is an actual ordered callback execution for every finite signer count,
not a replacement of the generic model by a constant callback assumption. -/
theorem constant_pass_execution (write : State Nat → Nat → AccountView.Handle → State Nat)
    (preserves : ∀ before offset handle, (write before offset handle).context = before.context)
    (before : State Nat) (offset count : Nat)
    (ready : AccountView.Ready before.context.world AccountView.witnessHandle) :
    signerPass constantAsRef write before offset (List.replicate count ())
      (.returned () (repeatWrites write before offset count)) := by
  induction count generalizing before offset with
  | zero => rfl
  | succ count ih =>
    apply signerPass_return constantAsRef write before offset () (List.replicate count ())
      AccountView.witnessHandle before.context _
    · exact ⟨ready, rfl⟩
    · apply ih
      rw [preserves]
      exact ready

/-- Buffers can be larger than the public suggested capacities; construction
does not add a maximum-multisig check. -/
def manyState (count : Nat) : State Nat :=
  { sampleState with buffers :=
    ⟨sampleBuffers.data, List.replicate (4 + count) none, List.replicate (4 + count) none⟩ }

/-- Duplicate signer values are retained at arbitrary finite multiplicity. -/
def manyTransfer (count : Nat) : Transfer Unit := ⟨sampleSingle, List.replicate count ()⟩

/-- First-pass state for the explicit constant-callback interpretation. -/
def manyAccounts (count : Nat) : State Nat :=
  repeatWrites writeAccount
    (writeBaseAccounts (writeData (manyState count) (manyTransfer count)).2 (manyTransfer count)) 4
      count

/-- Second-pass state for the same interpretation, after every first-pass write. -/
def manyMetas (count : Nat) : State Nat :=
  repeatWrites (fun state offset handle => writeMeta state offset handle true false)
    (writeBaseMetas (manyAccounts count) (manyTransfer count)) 4 count

/-- The first pass retains its context and committed lengths and does not touch metadata. -/
theorem manyAccounts_frame (count : Nat) :
    (manyAccounts count).context = sampleState.context ∧
    (manyAccounts count).lengths = ⟨1, 0, 0⟩ ∧
    (manyAccounts count).buffers.instructionAccounts = List.replicate (4 + count) none := by
  refine ⟨?_, ?_, ?_⟩
  · exact repeatWrites_preserves writeAccount State.context (fun _ _ _ => rfl) _ _ _
  · exact repeatWrites_preserves writeAccount State.lengths (fun _ _ _ => rfl) _ _ _
  · exact repeatWrites_preserves writeAccount (fun state => state.buffers.instructionAccounts)
      (fun _ _ _ => rfl) _ _ _

/-- Every first callback pass succeeds with sufficient capacity, without a signer-count cap. -/
theorem many_accounts_execute (count : Nat) :
    writeAccounts constantAsRef (writeData (manyState count) (manyTransfer count)).2 (manyTransfer
      count)
      (.returned (.ok (4 + count)) (manyAccounts count)) := by
  suffices writeAccounts constantAsRef
      (writeData (manyState count) (manyTransfer count)).2 (manyTransfer count)
      (.returned (.ok (4 + (manyTransfer count).multisigSigners.length)) (manyAccounts count)) by
    simpa only [manyTransfer, List.length_replicate] using this
  apply writeAccounts_pass constantAsRef
    (writeData (manyState count) (manyTransfer count)).2 (manyTransfer count)
    (.returned () (manyAccounts count))
  · change ¬ (List.replicate (4 + count) (none : Option CpiAccount)).length - 0 <
        4 + (List.replicate count ()).length
    simp
  · rfl
  · exact constant_pass_execution writeAccount (fun _ _ _ => rfl) _ 4 count
      AccountView.witness_ready

/-- The complete second pass repeats those callbacks at the same multiplicity. -/
theorem many_metas_execute (count : Nat) :
    writeMetas constantAsRef (manyAccounts count) (manyTransfer count)
      (.returned (.ok (4 + count)) (manyMetas count)) := by
  suffices writeMetas constantAsRef (manyAccounts count) (manyTransfer count)
      (.returned (.ok (4 + (manyTransfer count).multisigSigners.length)) (manyMetas count)) by
    simpa only [manyTransfer, List.length_replicate] using this
  apply writeMetas_pass constantAsRef (manyAccounts count) (manyTransfer count)
    (.returned () (manyMetas count))
  · rw [(manyAccounts_frame count).2.2, (manyAccounts_frame count).2.1]
    simp [manyTransfer]
  · have ready : AccountView.Ready
        (writeBaseMetas (manyAccounts count) (manyTransfer count)).context.world
        AccountView.witnessHandle := by
      change AccountView.Ready (manyAccounts count).context.world AccountView.witnessHandle
      rw [(manyAccounts_frame count).1]
      exact AccountView.witness_ready
    have pass := constant_pass_execution
      (fun state offset handle => writeMeta state offset handle true false)
      (fun _ _ _ => rfl) (writeBaseMetas (manyAccounts count) (manyTransfer count)) 4 count ready
    simpa only [manyTransfer, manyMetas, (manyAccounts_frame count).2.1, Nat.zero_add] using pass

/-- The full model has this actual finite execution for every supplied signer count. -/
theorem many_full_execution (count : Nat) :
    intoBatch constantAsRef (manyState count) (manyTransfer count)
      (.returned (.ok ()) (commit (manyMetas count) 10 (4 + count) (4 + count))) :=
  intoBatch_success constantAsRef (manyState count) (manyTransfer count)
    (writeData (manyState count) (manyTransfer count)).2 (manyAccounts count) (manyMetas count)
    10 (4 + count) (4 + count) (by change ¬ 13 < 1 + 2; decide) rfl
    (many_accounts_execute count) (many_metas_execute count)

/-- Twelve multisig values are accepted by local Batch preparation; the separate maximum of a direct
invocation helper is not imported into this source function. -/
theorem no_imported_multisig_limit :
    intoBatch constantAsRef (manyState 12) (manyTransfer 12)
      (.returned (.ok ()) (commit (manyMetas 12) 10 16 16)) := many_full_execution 12

/-- Second-pass writes retain the precommit lengths for every finite count. -/
theorem manyMetas_lengths (count : Nat) : (manyMetas count).lengths = ⟨1, 0, 0⟩ := by
  have same := repeatWrites_preserves
    (fun state offset handle => writeMeta state offset handle true false)
    State.lengths (fun _ _ _ => rfl)
    (writeBaseMetas (manyAccounts count) (manyTransfer count)) 4 count
  exact same.trans (manyAccounts_frame count).2.1

/-- Neither callback pass changes the already written payload or header slots. -/
theorem manyMetas_data (count : Nat) :
    (manyMetas count).buffers.data = sampleAfterData.buffers.data := by
  have second := repeatWrites_preserves
    (fun state offset handle => writeMeta state offset handle true false)
    (fun state => state.buffers.data) (fun _ _ _ => rfl)
    (writeBaseMetas (manyAccounts count) (manyTransfer count)) 4 count
  have first := repeatWrites_preserves writeAccount (fun state => state.buffers.data)
    (fun _ _ _ => rfl)
    (writeBaseAccounts (writeData (manyState count) (manyTransfer count)).2 (manyTransfer count)) 4
      count
  exact second.trans first

/-- An actual 256-signer execution retains the full counts 260 while the u8
header records four. This is local construction, not runtime admission. -/
theorem wrapped_header_full_counters :
    intoBatch constantAsRef (manyState 256) (manyTransfer 256)
      (.returned (.ok ()) (commit (manyMetas 256) 10 260 260)) ∧
    (commit (manyMetas 256) 10 260 260).lengths = ⟨13, 260, 260⟩ ∧
    (commit (manyMetas 256) 10 260 260).buffers.data[1]? = some (some 4) := by
  refine ⟨many_full_execution 256, ?_, ?_⟩
  · simp only [commit, manyMetas_lengths]
  · simp only [commit, manyMetas_lengths, manyMetas_data]
    rfl

/-- The wrapping-header execution is admitted by the generic family. Its exact
buffer writes and full counters are established by wrapped_header_full_counters. -/
theorem wrapped_header_permitted :
    (intoFamily.contract sampleTypes).requires (manyState 256)
      ⟨manyTransfer 256, constantAsRef⟩ := True.intro

/-- The alternating-reference control is also a permitted generic-family input. -/
theorem alternating_permitted :
    (intoFamily.contract sampleTypes).requires alternatingState
      ⟨sampleTransfer, alternatingAsRef⟩ := True.intro

/-- A permitted nondeterministic interpretation can either return the account
with an effect or terminate. The generic contract does not choose for it. -/
def choiceAsRef : AsRef sampleTypes := fun before signer outcome =>
  sampleAsRef before signer outcome ∨ terminalCallback before signer outcome

/-- Both different finite outcomes of the supplied nondeterministic callback
are retained by the same complete preparation relation. -/
theorem nondeterministic_exits_preserved :
    intoBatch choiceAsRef sampleState sampleTransfer (.returned (.ok ()) sampleCommitted) ∧
    intoBatch choiceAsRef sampleState sampleTransfer (.terminated 91) := by
  have accounts : writeAccounts choiceAsRef sampleAfterData sampleTransfer
      (.returned (.ok 5) sampleAfterAccounts) := by
    apply writeAccounts_pass choiceAsRef sampleAfterData sampleTransfer
      (.returned () sampleAfterAccounts) (by decide) (by decide)
    exact signerPass_return choiceAsRef writeAccount
      (writeBaseAccounts sampleAfterData sampleTransfer) 4 () [] AccountView.witnessHandle
      ⟨AccountView.witnessState, 1⟩ (.returned () sampleAfterAccounts)
      (Or.inl ⟨AccountView.witness_ready, rfl⟩) rfl
  have metas : writeMetas choiceAsRef sampleAfterAccounts sampleTransfer
      (.returned (.ok 5) sampleAfterMetas) := by
    apply writeMetas_pass choiceAsRef sampleAfterAccounts sampleTransfer
      (.returned () sampleAfterMetas) (by decide)
    exact signerPass_return choiceAsRef
      (fun state offset handle => writeMeta state offset handle true false)
      (writeBaseMetas sampleAfterAccounts sampleTransfer) 4 () [] AccountView.witnessHandle
      ⟨AccountView.witnessState, 2⟩ (.returned () sampleAfterMetas)
      (Or.inl ⟨AccountView.witness_ready, rfl⟩) rfl
  have terminal : writeAccounts choiceAsRef sampleAfterData sampleTransfer (.terminated 91) := by
    apply writeAccounts_pass choiceAsRef sampleAfterData sampleTransfer
      (.terminated 91) (by decide) (by decide)
    exact signerPass_terminal choiceAsRef writeAccount
      (writeBaseAccounts sampleAfterData sampleTransfer) 4 () [] 91 (Or.inr rfl)
  refine ⟨intoBatch_success choiceAsRef sampleState sampleTransfer sampleAfterData
    sampleAfterAccounts
    sampleAfterMetas 10 5 5 (by decide) rfl accounts metas, ?_⟩
  have header : ¬ sampleState.buffers.data.length < sampleState.lengths.data + 2 := by decide
  have data : writeData sampleState sampleTransfer = (.ok 10, sampleAfterData) := rfl
  simp only [intoBatch, header, ↓reduceIte, data]
  exact ⟨.terminated 91, terminal, rfl⟩

/-- The versioned constructor contract admits the complete specialized value,
including its unchanged state and retained account references. -/
theorem versioned_single_constructor :
    PinocchioToken.instructions.transfer_checked.TransferChecked.new_contract.ensures
      () sampleSingle (singleTransfer sampleSingle) () :=
  PinocchioToken.instructions.transfer_checked.TransferChecked.new_reference_realizes
    () sampleSingle True.intro

/-- The real nonempty two-pass execution satisfies the versioned contract. -/
theorem versioned_into_batch_client :
    (PinocchioToken.instructions.transfer_checked.TransferChecked.into_batch_contract.contract
      sampleTypes).post sampleState sampleIntoCall (.returned (.ok ()) sampleCommitted) :=
  PinocchioToken.instructions.transfer_checked.TransferChecked.into_batch_reference_holds
    sampleTypes sampleState sampleIntoCall (.returned (.ok ()) sampleCommitted)
    sampleInto_requires sampleInto_execute

/-- The versioned Batch constructor is witnessed at actual nonempty buffers. -/
theorem versioned_batch_constructor :
    PinocchioToken.instructions.batch.Batch.new_contract.ensures sampleBuffers ()
      (.ok ⟨1, 0, 0⟩) sampleBuffers :=
  PinocchioToken.instructions.batch.Batch.new_reference_realizes
    sampleBuffers () True.intro

/-- The versioned invocation contract retains the actual unchecked-provider effect. -/
theorem versioned_invocation_client :
    (PinocchioToken.instructions.batch.Batch.invoke_signed_contract.contract
      sampleTypes).post
      sampleState sampleInvokeCall
      (.returned (.ok ()) { sampleState with context := ⟨AccountView.witnessState, 1⟩ }) :=
  PinocchioToken.instructions.batch.Batch.invoke_signed_reference_holds
    sampleTypes sampleState sampleInvokeCall _ sampleInvocationReady
    (invokeSigned_return (types := sampleTypes) sampleState sampleInvokeCall
      (sampleRequest sampleInvokeCall.signers) (sampleRequest_decodes _)
      ⟨AccountView.witnessState, 1⟩ rfl)

/-- These mathematical integers are outside the u64/u8 argument domains of Rust. -/
def wideSingle : SingleTransfer :=
  { sampleSingle with amount := Solanalib.Runtime.U64_LIMIT, decimals := 256 }

/-- The constructor stores even wider mathematical values unchanged. Source
integer representability is not an unused condition on that value equality. -/
theorem wide_constructor_retains_values :
    ¬ (wideSingle.amount < Solanalib.Runtime.U64_LIMIT ∧ wideSingle.decimals < 256) ∧
    PinocchioToken.instructions.transfer_checked.TransferChecked.new_contract.requires
      () wideSingle ∧
    PinocchioToken.instructions.transfer_checked.TransferChecked.new_contract.ensures
      () wideSingle (singleTransfer wideSingle) () :=
  ⟨by decide, True.intro,
    PinocchioToken.instructions.transfer_checked.TransferChecked.new_reference_realizes
      () wideSingle True.intro⟩

/-- A mathematical counter outside the source width, with the original buffers. -/
def wideCounterState : State Nat :=
  { sampleState with lengths := ⟨Solanalib.Runtime.U64_LIMIT, 0, 0⟩ }

/-- Header rejection remains a real finite outcome at this newly admitted
input. The impossible callback is never reached and all buffers stay unchanged. -/
theorem wide_counter_header_error :
    ¬ wideCounterState.lengths.data + 2 < Solanalib.Runtime.U64_LIMIT ∧
    (intoFamily.contract sampleTypes).requires wideCounterState
      ⟨⟨wideSingle, [()]⟩, noCallback⟩ ∧
    intoRun sampleTypes wideCounterState ⟨⟨wideSingle, [()]⟩, noCallback⟩
      (.returned (.error .InvalidArgument) wideCounterState) :=
  ⟨by decide, True.intro,
    intoBatch_header_error noCallback wideCounterState ⟨wideSingle, [()]⟩ (by decide)⟩

/-- This malformed mathematical state has a hole in each committed prefix.
The source cannot read any of those prefixes as a complete initialized slice. -/
def partialPrefixState : State Nat := {
  sampleState with
  buffers := ⟨[some 255, none, some 7],
    [none, some (cpiAccount AccountView.witnessState AccountView.witnessHandle)],
    [none, some (accountMetaRef AccountView.witnessHandle true false)]⟩
  lengths := ⟨3, 2, 2⟩ }

/-- A hole rejects the entire prefix, including a later available value.
This applies independently to bytes, CPI descriptors and instruction metadata. -/
theorem partial_prefix_rejected :
    initializedPrefix partialPrefixState.buffers.data 3 = none ∧
    initializedPrefix partialPrefixState.buffers.accounts 2 = none ∧
    initializedPrefix partialPrefixState.buffers.instructionAccounts 2 = none := ⟨rfl, rfl, rfl⟩

/-- An out-of-bounds length is rejected even when every allocated slot is initialized. -/
theorem short_prefix_rejected : initializedPrefix ([some 255, some 7] : List (Option UInt8)) 3 =
  none := rfl

/-- Invalid prefixes are outside the source domain of the versioned contract. -/
theorem partial_prefix_not_admitted :
    ¬ (invokeFamily.contract sampleTypes).requires partialPrefixState sampleInvokeCall := by
  intro ready
  have initialized := ready.1
  simp [PrefixReady, partialPrefixState] at initialized

/-- No request and no provider outcome, including an unwind or terminal exit,
can be fabricated from the malformed partial-prefix state. -/
theorem partial_prefix_no_provider (args : InvokeCall sampleTypes)
    (outcome : Outcome (State Nat) (Except Error Unit) Nat Nat) :
    request partialPrefixState args.signers = none ∧
      ¬ invokeSigned partialPrefixState args outcome :=
  ⟨rfl, invokeSigned_no_request partialPrefixState args rfl outcome⟩

/-- The successful two-pass constructor is admitted; every committed byte is
present in order and both callback effects remain before invocation. -/
theorem complete_prefix_admitted :
    (invokeFamily.contract sampleTypes).requires sampleCommitted sampleInvokeCall ∧
    (request sampleCommitted sampleInvokeCall.signers).map Request.data =
      some [255, 5, 10, 12, 1, 2, 0, 0, 0, 0, 0, 0, 6] ∧
    sampleCommitted.context.ambient = 2 := ⟨sampleCommittedInvocationReady, rfl, rfl⟩

/-- A provider that counts bytes observes all thirteen committed bytes and
preserves the two preceding signer-callback effects in its resulting state. -/
theorem complete_prefix_provider_effect :
    invokeRun sampleTypes sampleCommitted sampleInvokeCall
      (.returned (.ok ())
        { sampleCommitted with context := ⟨AccountView.witnessState, 15⟩ }) := by
  obtain ⟨sent, decoded, progress⟩ := sampleCommittedInvocationReady.progress sampleInvokeCall
  apply progress (.returned () ⟨AccountView.witnessState, 15⟩)
  have count := (request_exact decoded).1.1
  change sent.data.length = 13 at count
  change (Outcome.returned () ⟨AccountView.witnessState, 15⟩ : Outcome (Context Nat) Unit Nat Nat) =
    .returned () { sampleCommitted.context with ambient := sampleCommitted.context.ambient +
      sent.data.length }
  rw [count]
  rfl

end SolanalibTest.Specs.PinocchioToken.Instructions
