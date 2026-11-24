/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Common
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainAllocatedRun
import SolanalibTest.Conformance.Library.Runtime
import Solanalib.Specs.SplToken2022.Instructions

/-!
# spl-token-2022 11.0.0 `onchain::invoke_transfer_checked`

One checker decides the two registered models of the call on every record:
the operational family `invoke_transfer_checked_reference`
(`Token.OnchainAllocated.family`) and the supporting value observation
`invoke_transfer_checked_value_reference` (`Onchain.run`). A record is
admitted when both admit it.

**Record.** The state before the call holds the distinct accounts, the borrows
the caller holds across the call, the syscall script (`sol_try_find_program_address`
replies, then the `sol_invoke_signed_rust` reply) and `counts`; the outcome
holds the exit, the accounts read back, the borrows still held, the syscall
log (each CPI request with its own `counts`) and `counts`.

**The `counts` field.** A flat list of `Rc::strong_count`, in cell order:
entry `2i` is account the lamports of `i` `Rc`, entry `2i + 1` its data `Rc`. The
driver reads it through one `Weak` per cell, which leaves the strong counts
unchanged, at three points:
- `state.counts`, before the call, with the arguments built: one owner for the info of the
  caller, one per appearance in `additional` and one per role the
  account fills (the four infos the call takes by value);
- `call.counts` of each CPI request in the log after the call, read when the
  shim decodes the request: the infos of the caller and `additional`, plus one per
  appearance in the account infos of the request (the role infos are dropped by
  then);
- `outcome.state.counts`, after the call returned or unwound, while the caller
  still holds its infos and `additional`.

The value observation ignores `counts`; the operational family starts its Rc
ledger from `state.counts` and is compared on the other two.

**State.** Account `i` of the record owns cells `2i` (lamports) and `2i + 1`
(data) and owner reference `i`; aliases are the same value. Borrows the caller
holds across the call are live guards of the initial state.

**Value observation: index and provider (test choices).**
`Types := ⟨List Logged, Empty, Empty⟩`: the ambient state is the log of
invocations. The provider interprets the `invoke_signed` of solana-cpi 3.1.0
(`OnchainIndex.precheck`, `OnchainIndex.replyResult`): for each instruction
meta it borrows the first account info with that key (mutably if the meta is
writable) and drops the borrow, returning `AccountBorrowFailed` on a conflict;
otherwise it logs the request and returns the scripted
`sol_invoke_signed_rust` reply of the shim, read through `ProgramError::from(u64)`.
Profile: 64-bit RefCell counters, unwinding panics. The PDA interpretation
`crypto` is the table of the address searches of the record: SHA-256 of each
recorded request (seeds, bump, program id, marker) is the address the shim
answered, and every other input hashes to an on-curve value. The search of the model therefore finds
the recorded address only if it asks for the recorded
seeds and program id.

**Value observation: outcome.** `run` admits exactly the outcome `computed`
(`run_iff`). It is compared with the record through `observe?`: the exit and
result (a panic by its reason), the cell contents, the live guards and the
invocation log (instruction, account values, signer seeds); the ordered
syscalls and the unconsumed replies against `modelSearches`. The checker
decides its precondition `PreparationReady`.

**Operational family.** Decided at the closed index `OnchainIndex.Index env`
with `env := envOf raw script` (the account owners, the PDA replies through
`OnchainIndex.pdaReplyOf`, the CPI reply), from the initial world
`OnchainIndex.initialWorld (initialState raw borrows) state.counts`. There the
family admits exactly `OnchainAllocatedRun.invokeF env s a`
(`OnchainAllocatedRun.invoke_fn`), which the checker evaluates as compiled
code (kernel `decide` cannot reduce its well-founded recursions). It is
compared through `observeAllocated?`: the exit and result, the cell contents
and live guards, each CPI request with the Rc counts of the model at the call
(against `call.counts`), the ordered syscalls (the PDA log, then the CPI log)
and the unconsumed replies, and the final Rc counts (against
`outcome.state.counts`). Its precondition
`∃ protocol, Admitted ∧ ResourceReady ∧ BorrowReady` is not decidable and is
listed in `requires-open.toml`. Not observed: heap allocation counts, the `tokenEnumSize` and
capacities of the index, and terminal (double-unwind) outcomes,
which `observeAllocated?` maps to `none`. An extra account resolved from seeds
has no outcome at this index (its seed vectors are empty-only), so such a
record would be rejected; no record has one.

The released-guard tombstones and cell policies of both models are not observable natively.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.Onchain

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Onchain

/-- One logged invocation: instruction, account values and signer seeds. -/
abbrev Logged := Solanalib.Runtime.CpiInstruction × List Onchain.Account × List (List
  Solanalib.Runtime.Bytes)

def types : Types := ⟨List Logged, Empty, Empty⟩

abbrev World := Onchain.State × List Logged
abbrev Out := Outcome World (Except Token.Error Unit) (Panic ⊕ Empty) (Panic ⊕ Empty)

def logged (r : CpiRequest.Request Onchain.Account) : Logged := (r.instruction, r.accounts,
  r.signers)

/-- The computed outcome of the provider; `none` when the syscall is reached
without a scripted reply (no execution). -/
def providerF (reply : Option Nat) (s : World) (r : CpiRequest.Request Onchain.Account) :
    Option (Outcome World (Except Token.Error Unit) Empty Empty) :=
  if OnchainIndex.precheck s.1 r then
    reply.map fun ret => .returned (OnchainIndex.replyResult ret) (s.1, s.2 ++ [logged r])
  else some (.returned (.error .AccountBorrowFailed) s)

def provider (reply : Option Nat) :
    CpiRequest.Invocation World Onchain.Account Token.Error Empty Empty :=
  fun s r o => providerF reply s r = some o

def computed (before : World) (call : Call types) (reply : Option Nat) : Option Out :=
  match prepare before.1 call.args with
  | (.success prepared, after) =>
    (providerF reply (after, before.2) (prepared.request call.args.signers)).map providerOutcome
  | (.error error, after) => some (.returned (.error error) (after, before.2))
  | (.panic reason, after) =>
    some (if call.args.profile.aborts then .terminated (.inl reason) else .unwound (.inl reason)
      (after, before.2))
  | (.malformed, _) => none

/-- With the scripted provider, the registered value reference admits exactly
`computed`. -/
theorem run_iff (before : World) (args : Onchain.Args) (reply : Option Nat) (o : Out) :
    Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference types before
        ⟨args, provider reply⟩ o ↔
      computed before ⟨args, provider reply⟩ reply = some o := by
  show run types before ⟨args, provider reply⟩ o ↔ _
  unfold run computed
  cases prepare before.1 args with
  | mk step after =>
    cases step with
    | success prepared =>
      dsimp only
      constructor
      · rintro ⟨result, hr, rfl⟩
        rw [show providerF reply (after, before.2) (prepared.request args.signers) = some result
          from hr]
        rfl
      · intro h
        cases hp : providerF reply (after, before.2) (prepared.request args.signers) with
        | none => rw [hp] at h; cases h
        | some result =>
          rw [hp] at h
          exact ⟨result, hp, Option.some.inj h⟩
    | error e =>
      dsimp only
      exact ⟨fun h => by subst h; rfl, fun h => (Option.some.inj h).symm⟩
    | panic reason =>
      dsimp only
      cases args.profile.aborts <;>
        exact ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
    | malformed => exact ⟨False.elim, fun h => by cases h⟩

/-! ## Observation -/

/-- A returned result, or an unwind with its panic message. The `Panic` reasons of the model are
mapped to the messages the source emits for them on the
pinned toolchain (`panicMessage`). -/
inductive Exit where
  | returned (result : Except Token.Error Unit)
  | unwound (message : String)
  deriving DecidableEq

abbrev Observation := Exit × List AccountInfo.Content × List (Borrow.Handle × Borrow.Mode) × List
  Logged


instance instDecidableEqLogged : DecidableEq Logged := inferInstance
instance instDecidableEqContents : DecidableEq (List AccountInfo.Content) := inferInstance
instance instDecidableEqGuards : DecidableEq (List (Borrow.Handle × Borrow.Mode)) := inferInstance
/-- Spelled out: instance search does not find the product instance here. -/
instance instDecidableEqObservation : DecidableEq Observation := fun a b =>
  @instDecidableEqProd _ _ instDecidableEqExit
    (@instDecidableEqProd _ _ instDecidableEqContents
      (@instDecidableEqProd _ _ instDecidableEqGuards (instDecidableEqList))) a b

def live (s : Onchain.State) : List (Borrow.Handle × Borrow.Mode) :=
  s.slots.filterMap fun slot => slot.map fun x => (x.cell, x.mode)

def observe? (message : Panic → String) : Out → Option Observation
  | .returned r (s, log) => some (.returned r, s.cells.map (·.value), live s, log)
  | .unwound (.inl p) (s, log) => some (.unwound (message p), s.cells.map (·.value), live s, log)
  | .unwound (.inr e) _ => e.elim
  | .terminated _ => none

theorem admits_iff (message : Panic → String) (before : World) (args : Onchain.Args) (reply :
  Option Nat)
    (rec : Observation) :
    (∃ o, Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference types before
        ⟨args, provider reply⟩ o ∧ observe? message o = some rec) ↔
      (computed before ⟨args, provider reply⟩ reply).bind (observe? message) = some rec := by
  constructor
  · rintro ⟨o, ho, hobs⟩
    rw [(run_iff before args reply o).1 ho]
    exact hobs
  · intro h
    cases hc : computed before ⟨args, provider reply⟩ reply with
    | none => rw [hc] at h; cases h
    | some o =>
      rw [hc] at h
      exact ⟨o, (run_iff before args reply o).2 hc, h⟩

/-! ## Reading records -/

structure RawAccount where
  key : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  lamports : Nat
  data : Solanalib.Runtime.Bytes
  isSigner : Bool
  isWritable : Bool
  executable : Bool

def rawAccount (j : Json) : Result RawAccount := do
  pure ⟨← keyField j "key", ← keyField j "owner", ← uintField 64 j "lamports", ← asBytes (← field j
    "data"),
    ← boolField j "is_signer", ← boolField j "is_writable", ← boolField j "executable"⟩

def accountValue (i : Nat) (a : RawAccount) : Onchain.Account :=
  ⟨a.key, ⟨2 * i⟩, ⟨2 * i + 1⟩, a.owner, 0, a.isSigner, a.isWritable, a.executable, ⟨i⟩⟩

def policy : Borrow.Policy := (⟨64, false⟩ : AccountInfo.Profile).policy

def cellsOf (accounts : List RawAccount) : List AccountInfo.Content :=
  accounts.flatMap fun a => [.lamports (UInt64.ofNat a.lamports), .data a.data]

def held (j : Json) : Result (Borrow.Handle × Borrow.Mode) := do
  let i ← natField j "account"
  let cell ← match ← (← field j "cell").getStr? with
    | "lamports" => pure (2 * i)
    | "data" => pure (2 * i + 1)
    | other => throw s!"unknown cell {other}"
  let mode ← match ← (← field j "mode").getStr? with
    | "shared" => pure Borrow.Mode.shared
    | "exclusive" => pure Borrow.Mode.exclusive
    | other => throw s!"unknown mode {other}"
  pure (⟨cell⟩, mode)

def initialState (accounts : List RawAccount) (borrows : List (Borrow.Handle × Borrow.Mode)) :
  Onchain.State :=
  ⟨(cellsOf accounts).map fun c => ⟨c, policy⟩, borrows.map fun (h, m) => some ⟨h, m, 0, .whole⟩⟩

def seeds (j : Json) : Result (List (List Solanalib.Runtime.Bytes)) := do
  (← j.getArr?).toList.mapM fun s => do (← s.getArr?).toList.mapM asBytes

def index {α : Type} (l : List α) (i : Nat) : Result α :=
  match l[i]? with
  | some a => pure a
  | none => throw s!"account index {i} out of range"

/-- The decoded CPI: account infos are identified by their cell pair. -/
def loggedCall (j : Json) : Result Logged := do
  let call ← field j "call"
  let instr ← instruction (← field call "instruction")
  let infos ← listField call "account_infos" fun a => do
    let i ← natField a "cells"
    pure (accountValue i ⟨← keyField a "key", ← keyField a "owner", 0, [], ← boolField a
      "is_signer",
      ← boolField a "is_writable", ← boolField a "executable"⟩)
  pure (instr, infos, ← seeds (← field call "signers_seeds"))

/-- The scripted CPI reply: the first `sol_invoke_signed_rust` reply. -/
def cpiReply (script : Runtime.SyscallState) : Option Nat :=
  (script.replies.find? (·.syscall == "sol_invoke_signed_rust")).map (·.ret)

/-- One recorded address search: its hash input at the answered bump, and the
answered address. -/
def pdaEntry (request : Runtime.Request) (reply : Runtime.Reply) : Result (Solanalib.Runtime.Bytes
  × Solanalib.Runtime.Bytes) := do
  let seeds ← request.slices "seeds"
  let programId ← request.bytes "program_id"
  let bump ← match reply.bump with
    | some b => pure b
    | none => throw "address search reply without bump"
  pure ((seeds ++ [[UInt8.ofNat bump]]).flatten ++ programId ++ Solanalib.Runtime.PDA_MARKER,
    reply.data)

def cryptoOf (table : List (Solanalib.Runtime.Bytes × Solanalib.Runtime.Bytes)) : Address.Crypto
  where
  primitives := {
    sha256 := fun input => ((table.find? (·.1 == input)).map (·.2)).getD []
    onCurve := fun h => !(table.any (·.2 == h)) }

def pdaTable (script after : Runtime.SyscallState) : Result (List (Solanalib.Runtime.Bytes ×
  Solanalib.Runtime.Bytes)) := do
  let requests := after.log.filter (·.syscall == "sol_try_find_program_address")
  let replies := script.replies.filter (·.syscall == "sol_try_find_program_address")
  -- Unpaired requests or replies are not dropped silently: the search and
  -- leftover-reply comparison below rejects them.
  (requests.zip replies).mapM fun (q, r) => pdaEntry q r

/-- The exact message the source emits for a model panic, from the inputs of the record. Every
`borrowFailed` of this preparation is a failing unchecked *shared* borrow (`data_len` and the
multisig `data.borrow()`), which core reports as "RefCell already mutably borrowed"; the
multisig range panic is the slice-index panic of `signers[..n]` with `n` at byte 1 of the data
of the authority and the eleven stored keys; a failed address search panics with the
`Syscall.panicMessage` of the Address model. -/
def panicMessage (state : Onchain.State) (args : Onchain.Args) : Panic → String
  | .borrowFailed => "RefCell already mutably borrowed"
  | .multisigSignerRange =>
    let n := match state.lookupCell args.authority.data with
      | some ⟨.data bytes, _⟩ => (bytes[1]?.map UInt8.toNat).getD 0
      | _ => 0
    s!"range end index {n} out of range for slice of length 11"
  | .noViableProgramAddress => Address.Syscall.panicMessage

def observationJson (o : Observation) : Json :=
  let (exit, cells, guards, log) := o
  Json.mkObj [
    ("exit", match exit with
      | .returned r => resultJson (fun _ => Json.null) r
      | .unwound m => Json.mkObj [("unwound", Json.str m)]),
    ("cells", Json.arr (cells.map fun
      | .lamports l => Lean.toJson l.toNat
      | .data d => bytesJson d).toArray),
    ("live_guards", Json.arr (guards.map fun (h, m) =>
      Json.mkObj [("cell", Lean.toJson h.cell), ("exclusive", Json.bool (m ==
        .exclusive))]).toArray),
    ("cpi", Json.arr (log.map fun (i, accounts, _) => Json.mkObj [("instruction", instructionJson
      i),
      ("accounts", Json.arr (accounts.map fun a => Lean.toJson a.data.cell).toArray)]).toArray)]

/-! ## The precondition `PreparationReady`

The `requires` of the value family is `PreparationReady before.1 call.args`: the
reached borrows expose current data and the reached releases succeed, along
the actual branches of the preparation. Every predicate it is built from is decidable;
these instances follow the definitions branch by branch, so the checker
decides the registered precondition itself and a record outside it fails. -/

instance decDataBorrowReady (mode : Borrow.Mode) (state : Onchain.State) (handle : Borrow.Handle) :
    Decidable (AccountInfo.DataBorrow.Ready mode state handle) := by
  unfold AccountInfo.DataBorrow.Ready
  split
  · exact instDecidableTrue
  · split
    · exact instDecidableTrue
    · exact instDecidableFalse
    · exact instDecidableFalse

instance decAfterSuccess {Value : Type} (step : Step Value × Onchain.State)
    (ready : Onchain.State → Value → Prop) [h : ∀ s v, Decidable (ready s v)] :
    Decidable (AfterSuccess step ready) := by
  unfold AfterSuccess
  split
  · exact h _ _
  all_goals exact instDecidableTrue

instance decReleaseReady (state : Onchain.State) (guard : Borrow.Guard) :
    Decidable (ReleaseReady state guard) := by
  unfold ReleaseReady
  infer_instance

def decReleasesReady : (state : Onchain.State) → (guards : List Borrow.Guard) →
    Decidable (ReleasesReady state guards)
  | _, [] => instDecidableTrue
  | state, guard :: rest => by
    unfold ReleasesReady
    split
    · exact decReleasesReady _ rest
    · exact instDecidableFalse

instance (state : Onchain.State) (guards : List Borrow.Guard) : Decidable (ReleasesReady state
  guards) :=
  decReleasesReady state guards

instance decScopeReady {Value : Type} (checked : Bool) (state : Onchain.State) (info :
  Onchain.Account)
    (next : Onchain.State → Solanalib.Runtime.Bytes → Step Value × Onchain.State)
    (bodyReady : Onchain.State → Solanalib.Runtime.Bytes → Prop) [∀ s b, Decidable (bodyReady s b)]
      :
    Decidable (ScopeReady checked state info next bodyReady) := by
  unfold ScopeReady
  infer_instance

instance decDataLenReady (state : Onchain.State) (info : Onchain.Account) :
    Decidable (DataLenReady state info) := by
  unfold DataLenReady
  split <;> infer_instance

instance decMultisigReady (state : Onchain.State) (info : Onchain.Account) :
    Decidable (MultisigReady state info) := by
  unfold MultisigReady
  infer_instance

instance decAddMultisigReady (state : Onchain.State) (args : Onchain.Args) :
    Decidable (AddMultisigReady state args) := by
  unfold AddMultisigReady
  infer_instance

def decCollectReady : (state : Onchain.State) → (infos : List Onchain.Account) →
    (guards : List Borrow.Guard) → Decidable (CollectReady state infos guards)
  | _, [], _ => instDecidableTrue
  | state, info :: rest, guards => by
    unfold CollectReady
    have : Decidable (match borrowData true state info with
        | (.success borrowed, after) => CollectReady after rest (guards ++ [borrowed.guard])
        | (.error _, after) | (.panic _, after) => ReleasesReady after guards
        | (.malformed, _) => True) := by
      split
      · exact decCollectReady _ rest _
      · infer_instance
      · infer_instance
      · exact instDecidableTrue
    infer_instance

instance (state : Onchain.State) (infos : List Onchain.Account) (guards : List Borrow.Guard) :
    Decidable (CollectReady state infos guards) := decCollectReady state infos guards

def decExtraReady (crypto : Address.Crypto) (additional : List Onchain.Account) :
    (extras : List Hook.ExtraMeta) → (state : Onchain.State) → (prepared : Prepared) →
      Decidable (ExtraReady crypto additional extras state prepared)
  | [], _, _ => instDecidableTrue
  | extra :: rest, state, prepared => by
    unfold ExtraReady
    have : ∀ s p, Decidable (ExtraReady crypto additional rest s p) :=
      fun s p => decExtraReady crypto additional rest s p
    have : ∀ (after : Onchain.State) (item : Solanalib.Runtime.CpiMeta), Decidable
        (match additional.find? (fun info => info.key == (Hook.deescalate
          prepared.instruction.metas item).key) with
          | none => True
          | some info =>
            ExtraReady crypto additional rest after {
              instruction := { prepared.instruction with
                metas := prepared.instruction.metas ++ [Hook.deescalate prepared.instruction.metas
                  item] }
              accounts := prepared.accounts ++ [info] }) := by
      intro after item
      split
      · exact instDecidableTrue
      · infer_instance
    infer_instance

instance (crypto : Address.Crypto) (additional : List Onchain.Account) (extras : List
  Hook.ExtraMeta)
    (state : Onchain.State) (prepared : Prepared) :
    Decidable (ExtraReady crypto additional extras state prepared) :=
  decExtraReady crypto additional extras state prepared

instance decHookReady (state : Onchain.State) (args : Onchain.Args) (programId :
  Solanalib.Runtime.Pubkey)
    (prepared : Prepared) : Decidable (HookReady state args programId prepared) := by
  unfold HookReady
  split
  · exact instDecidableTrue
  · split
    · exact instDecidableTrue
    · split
      · exact instDecidableTrue
      · refine @decScopeReady _ _ _ _ _ _ ?_
        intro during bytes
        split
        · exact instDecidableTrue
        · infer_instance

instance decMintReady (state : Onchain.State) (args : Onchain.Args) (prepared : Prepared) :
    Decidable (MintReady state args prepared) := by
  unfold MintReady
  refine @decScopeReady _ _ _ _ _ _ ?_
  intro during bytes
  split
  · exact instDecidableTrue
  · split
    · exact instDecidableTrue
    · infer_instance

instance decPreparationReady (state : Onchain.State) (args : Onchain.Args) :
    Decidable (PreparationReady state args) := by
  unfold PreparationReady
  split
  · exact instDecidableTrue
  · infer_instance

/-- A world outside the precondition: the data handle of account 0 holds a lamports
cell, so the checked mint read finds no data. -/
def illTypedWorld : Onchain.State :=
  ⟨[⟨.lamports 1, policy⟩, ⟨.lamports 2, policy⟩], []⟩

def illTypedArgs : Onchain.Args where
  profile := ⟨64, false⟩
  crypto := Address.witnessCrypto
  tokenProgramId := token2022ProgramId
  source := ⟨.zero, ⟨0⟩, ⟨1⟩, .zero, 0, false, true, false, ⟨0⟩⟩
  mint := ⟨.zero, ⟨0⟩, ⟨1⟩, .zero, 0, false, true, false, ⟨0⟩⟩
  destination := ⟨.zero, ⟨0⟩, ⟨1⟩, .zero, 0, false, true, false, ⟨0⟩⟩
  authority := ⟨.zero, ⟨0⟩, ⟨1⟩, .zero, 0, false, true, false, ⟨0⟩⟩
  additional := []
  amount := 1
  decimals := 0
  signers := []

/-- The decider is live: it rejects the ill-typed world (kernel-checked). The
record parser builds a lamports and a data cell for every account and only the guards of the
preparation are released, so recorded worlds are inside the
precondition; this theorem is the negative control a record cannot express. -/
theorem illTyped_not_ready : ¬ PreparationReady illTypedWorld illTypedArgs := by
  decide

/-- The precondition of the registered family at this index is `PreparationReady`. -/
theorem requires_eq (before : World) (call : Call types) :
    (Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_contract.contract
      types).requires
      before call = PreparationReady before.1 call.args := rfl

/-! ## The address searches and leftover replies

The PDA search of the value model is pure, so the syscall count is not part of its
outcome. The crypto table above must therefore be exactly the searches the path of the
model performs: `modelSearches` follows `prepare` through the definitions of the
model (program check, multisig preparation, the checked mint
borrow, packed-Mint unpacking and `hookProgram`) to the validation-address
search of `addHook`. The recorded searches must equal it, in order, and the
replies left unconsumed must be the script minus those searches and minus the
CPI reply exactly when the model invokes the provider. Extra-meta PDA seeds
(which would search again) occur in no record; such a record would differ in
its search count and be rejected. -/

def modelSearches (state : Onchain.State) (args : Onchain.Args) :
    List (List Solanalib.Runtime.Bytes × Solanalib.Runtime.Pubkey) :=
  match Instruction.transferChecked .either {
      programId := args.tokenProgramId
      source := args.source.key
      mint := args.mint.key
      destination := args.destination.key
      authority := args.authority.key
      signers := []
      amount := args.amount
      decimals := args.decimals } with
  | .error _ => []
  | .ok instruction =>
    let base : Prepared := {
      instruction := instruction
      accounts := [args.source, args.mint, args.destination, args.authority] }
    match addMultisig state args base with
    | (.success _, after) =>
      match borrowData true after args.mint with
      | (.success borrowed, _) =>
        match unpackMintWithExtensions borrowed.bytes with
        | .ok mint =>
          match hookProgram mint.tlv with
          | some programId => [([Hook.extraAccountMetasSeed, args.mint.key.bytes], programId)]
          | none => []
        | .error _ => []
      | _ => []
    | _ => []

/-- One syscall of the ordered log: an address search with its seeds, program
id and initial bump slot, the CPI, or anything else (which no model call
produces). -/
inductive Syscall where
  | search (seeds : List Solanalib.Runtime.Bytes) (programId : Solanalib.Runtime.Pubkey) (bump :
    Option Nat)
  | cpi
  | other (name : String)
  deriving DecidableEq

def recordedSyscall (r : Runtime.Request) : Result Syscall :=
  match r.syscall with
  | "sol_try_find_program_address" => do
    let bump ← match r.fields.getObjVal? "bump" with
      | .ok .null => pure none
      | .ok b => do pure (some (← b.getNat?))
      | .error _ => pure none
    pure (.search (← r.slices "seeds") (← keyField r.fields "program_id") bump)
  | "sol_invoke_signed_rust" => pure .cpi
  | other => pure (.other other)

/-- The ordered syscalls of the path of the model: each address search as the
Address model builds its request (`Syscall.pdaRequest`: the seeds, the program
id and the bump slot initialised to 255), then the CPI exactly when the model
reaches the provider. -/
def modelSyscalls (searches : List (List Solanalib.Runtime.Bytes × Solanalib.Runtime.Pubkey)) (cpi
  : Bool) : List Syscall :=
  searches.map (fun (seeds, programId) =>
      let request := Address.Syscall.pdaRequest ⟨seeds, programId⟩
      Syscall.search request.seeds request.programId (some request.bumpOutput.toNat)) ++
    (if cpi then [.cpi] else [])

/-- Remove the first `n` replies answering `name`. -/
def consume (name : String) : Nat → List Runtime.Reply → List Runtime.Reply
  | 0, replies => replies
  | _, [] => []
  | n + 1, r :: rest => if r.syscall == name then consume name n rest else r :: consume name (n +
    1) rest

def expectedLeftover (script : List Runtime.Reply) (searches : Nat) (invoked : Bool) : List
  Runtime.Reply :=
  consume "sol_invoke_signed_rust" (if invoked then 1 else 0)
    (consume "sol_try_find_program_address" searches script)

/-- Whether the computed outcome of the model passed the pre-check of the provider and
logged an invocation. -/
def invoked : Option Out → Bool
  | some (.returned _ (_, log)) => !log.isEmpty
  | some (.unwound _ (_, log)) => !log.isEmpty
  | _ => false

/-! ## The operational family `invoke_transfer_checked_reference`

The registered family `Token.OnchainAllocated.family` is decided at the closed
index `OnchainIndex.Index env` of each record, from the initial world
`OnchainIndex.initialWorld` (the borrow world of the record and `state.counts`),
through `OnchainAllocatedRun.invoke_fn`: at that index the family admits
exactly the outcome `OnchainAllocatedRun.invokeF env s a`, evaluated as
compiled code. -/

/-- An outcome of the operational family at the closed index. -/
abbrev AllocatedOut :=
  Outcome OnchainIndex.State (Except Token.Error Unit) OnchainIndex.Unwind OnchainIndex.Terminal

/-- One CPI that reached the syscall, with the Rc strong counts at the call. -/
abbrev CountedCall := Logged × List Nat

/-- The observation of the operational family: the exit, the cell contents and
live guards, each CPI with the Rc counts at the call, the ordered syscalls,
the unconsumed replies and the Rc counts after the call. -/
abbrev AllocatedObservation :=
  Exit × List AccountInfo.Content × List (Borrow.Handle × Borrow.Mode) × List CountedCall ×
    List Syscall × List Runtime.Reply × List Nat

instance instDecidableEqCountedCalls : DecidableEq (List CountedCall) := inferInstance
instance instDecidableEqSyscalls : DecidableEq (List Syscall) := inferInstance
instance instDecidableEqReplies : DecidableEq (List Runtime.Reply) := inferInstance
/-- Spelled out, as `instDecidableEqObservation`. -/
instance instDecidableEqAllocatedObservation : DecidableEq AllocatedObservation := fun a b =>
  @instDecidableEqProd _ _ instDecidableEqExit
    (@instDecidableEqProd _ _ instDecidableEqContents
      (@instDecidableEqProd _ _ instDecidableEqGuards
        (@instDecidableEqProd _ _ instDecidableEqCountedCalls
          (@instDecidableEqProd _ _ instDecidableEqSyscalls
            (@instDecidableEqProd _ _ instDecidableEqReplies instDecidableEqList))))) a b

/-- What the record scripts for the closed index: the owner of each account,
the `sol_try_find_program_address` replies in order (`pdaReplyOf`) and the CPI
reply. -/
def envOf (raw : List RawAccount) (script : Runtime.SyscallState) : OnchainIndex.Env where
  owners := raw.map (·.owner)
  pdaReplies := (script.replies.filter (·.syscall == "sol_try_find_program_address")).map
    fun r => OnchainIndex.pdaReplyOf r.ret r.data r.bump
  cpiReply := cpiReply script

/-- The observed part of a final world. The model keeps the PDA and CPI
requests in two logs; `invoke` makes every PDA call during preparation and the
one CPI after it, so the ordered syscalls are the PDA requests (as
`modelSyscalls` builds them) followed by the CPIs. The unconsumed replies are
the script minus one reply per PDA request and minus the CPI reply if a CPI was
logged (`expectedLeftover`). -/
def allocatedView (script : List Runtime.Reply) (s : OnchainIndex.State) :
    List AccountInfo.Content × List (Borrow.Handle × Borrow.Mode) × List CountedCall ×
      List Syscall × List Runtime.Reply × List Nat :=
  (s.1.cells.map (·.value), live s.1, s.2.cpiLog.map (fun (r, rc) => (logged r, rc)),
    s.2.pdaLog.map (fun r => Syscall.search r.seeds r.programId (some r.bumpOutput.toNat)) ++
      s.2.cpiLog.map (fun _ => Syscall.cpi),
    expectedLeftover script s.2.pdaLog.length (!s.2.cpiLog.isEmpty), s.2.rc)

/-- The observation of an outcome; a terminal outcome (a destructor unwinding
during an unwind) is not observable natively. -/
def observeAllocated? (message : Panic → String) (script : List Runtime.Reply) :
    AllocatedOut → Option AllocatedObservation
  | .returned r s => some (.returned r, allocatedView script s)
  | .unwound p s => some (.unwound (message p), allocatedView script s)
  | .terminated _ => none

/-- The registered family reference admits an outcome with the recorded
observation exactly when the outcome of `invokeF` has it. -/
theorem allocated_admits_iff (env : OnchainIndex.Env) (message : Panic → String)
    (script : List Runtime.Reply) (before : OnchainIndex.State) (args : Onchain.Args)
    (rec : AllocatedObservation) :
    (∃ o, Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_reference
      (OnchainIndex.Index env)
        before args o ∧ observeAllocated? message script o = some rec) ↔
      (OnchainAllocatedRun.invokeF env before args).bind (observeAllocated? message script) = some
        rec := by
  constructor
  · rintro ⟨o, ho, hobs⟩
    rw [(OnchainAllocatedRun.invoke_fn env before args o).1 ho]
    exact hobs
  · intro h
    cases hc : OnchainAllocatedRun.invokeF env before args with
    | none => rw [hc] at h; cases h
    | some o =>
      rw [hc] at h
      exact ⟨o, (OnchainAllocatedRun.invoke_fn env before args o).2 hc, h⟩

def countsJson (counts : List Nat) : Json := Json.arr (counts.map Lean.toJson).toArray

def allocatedJson (o : AllocatedObservation) : Json :=
  let (exit, cells, guards, calls, syscalls, leftover, rc) := o
  Json.mergeObj (observationJson (exit, cells, guards, calls.map (·.1))) (Json.mkObj [
    ("cpi_counts", Json.arr (calls.map (countsJson ·.2)).toArray),
    ("syscalls", Json.arr (syscalls.map fun
      | .search seeds programId bump => Json.mkObj [("search", Json.arr (seeds.map
        bytesJson).toArray),
          ("program_id", pubkeyJson programId), ("bump", Lean.toJson bump)]
      | .cpi => Json.str "cpi"
      | .other name => Json.str name).toArray),
    ("leftover_replies", Lean.toJson leftover.length),
    ("counts", countsJson rc)])

/-! ## The checker -/

/-- Both verdicts on one record, the verdict of the operational family first (`pairChecker`
order), and the report. Both models read the same arguments, borrow world and
recorded exit; the value model also decides its precondition. -/
def checkRecord (c : Case) : Result (Bool × Bool × Json) := do
  let raw ← listField c.state "accounts" rawAccount
  let borrows ← listField c.state "borrows" held
  let script ← Runtime.syscallsOf c.state
  let reply := cpiReply script
  let state ← field c.outcome "state"
  let syscallsAfter ← Runtime.syscallsOf state
  let accounts := raw.zipIdx.map fun (a, i) => accountValue i a
  let args : Onchain.Args := {
    profile := ⟨64, false⟩
    crypto := cryptoOf (← pdaTable script syscallsAfter)
    tokenProgramId := ← keyField c.args "program_id"
    source := ← index accounts (← natField c.args "source")
    mint := ← index accounts (← natField c.args "mint")
    destination := ← index accounts (← natField c.args "destination")
    authority := ← index accounts (← natField c.args "authority")
    additional := ← listField c.args "additional" fun j => do index accounts (← j.getNat?)
    amount := ← uintField 64 c.args "amount"
    decimals := ← uintField 8 c.args "decimals"
    signers := ← seeds (← field c.args "seeds") }
  let before : World := (initialState raw borrows, [])
  let message := panicMessage before.1 args
  let model := (computed before ⟨args, provider reply⟩ reply).bind (observe? message)
  let expected := model.elim Json.null observationJson
  let after ← listField state "accounts" rawAccount
  let liveAfter ← listField state "borrows" held
  let log ← (syscallsAfter.log.filter (·.syscall == "sol_invoke_signed_rust")).mapM
    fun r => loggedCall r.fields
  let exit ← match ← (← field c.outcome "exit").getStr? with
    | "returned" => do pure (Exit.returned (← resultOf unitState (← field c.outcome "result")))
    | "unwound" => do pure (Exit.unwound (← (← field c.outcome "reason").getStr?))
    | other => throw s!"unexpected exit {other}"
  let recorded : Observation := (exit, cellsOf after, liveAfter, log)
  let searches := modelSearches before.1 args
  let cpi := invoked (computed before ⟨args, provider reply⟩ reply)
  let recordedSyscalls ← syscallsAfter.log.mapM recordedSyscall
  let leftover := expectedLeftover script.replies searches.length cpi
  let syscallsOk := recordedSyscalls == modelSyscalls searches cpi && syscallsAfter.replies ==
    leftover
  -- Keys, owners and flags are AccountInfo values: no step of either family
  -- changes them and the scripted providers write nothing.
  let metaOf := fun (a : RawAccount) => (a.key, a.owner, a.isSigner, a.isWritable, a.executable)
  let metasOk := after.map metaOf == raw.map metaOf
  have : Decidable (∃ o,
    Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference types before
      ⟨args, provider reply⟩ o ∧ observe? message o = some recorded) :=
    decidable_of_iff _ (admits_iff message before args reply recorded).symm
  let expected := Json.mergeObj expected (Json.mkObj [
    ("address_searches", Lean.toJson searches.length), ("leftover_replies", Lean.toJson
      leftover.length)])
  -- The precondition of the contract, decided at the registered name (`requires_eq`).
  have : Decidable
    ((Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_contract.contract
    types).requires
      before ⟨args, provider reply⟩) := by
    rw [requires_eq]; exact decPreparationReady _ _
  let ready := decide
    ((Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_contract.contract
    types).requires before ⟨args, provider reply⟩)
  let expected := Json.mergeObj expected (Json.mkObj [("preparation_ready", Json.bool ready)])
  let valueOk := ready && syscallsOk && metasOk && decide (∃ o,
    Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference
      types before ⟨args, provider reply⟩ o ∧ observe? message o = some recorded)
  -- The operational family at the closed index of the record, from its Rc counts.
  let env := envOf raw script
  let world := OnchainIndex.initialWorld before.1 (← listField c.state "counts" Json.getNat?)
  let calls ← (syscallsAfter.log.filter (·.syscall == "sol_invoke_signed_rust")).mapM fun r => do
    pure ((← loggedCall r.fields, ← listField (← field r.fields "call") "counts" Json.getNat?) :
      CountedCall)
  let recordedAllocated : AllocatedObservation := (exit, cellsOf after, liveAfter, calls,
    recordedSyscalls,
    syscallsAfter.replies, ← listField state "counts" Json.getNat?)
  have : Decidable (∃ o, Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_reference
      (OnchainIndex.Index env) world args o ∧ observeAllocated? message script.replies o = some
        recordedAllocated) :=
    decidable_of_iff _ (allocated_admits_iff env message script.replies world args
      recordedAllocated).symm
  let familyOk := metasOk && decide (∃ o,
    Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_reference
    (OnchainIndex.Index env) world args o ∧ observeAllocated? message script.replies o = some
      recordedAllocated)
  let familyModel := ((OnchainAllocatedRun.invokeF env world args).bind
    (observeAllocated? message script.replies)).elim Json.null allocatedJson
  return (familyOk, valueOk, Json.mkObj [("family", familyModel), ("value", expected)])

/-- One checker, two registered models of the same Rust function: the
operational family (`invoke_transfer_checked_reference`, its precondition open
in `requires-open.toml`) and the value observation, whose precondition it
decides. -/
def checker : Checker :=
  pairChecker "spl_token_2022::onchain::invoke_transfer_checked" []
    "Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_reference"
    "Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference" checkRecord
    (requiresDecided :=
      ["Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference"])

def checkers : List Checker := [checker]

end SolanalibTest.Conformance.Library.Families.TokenInterface.Onchain
