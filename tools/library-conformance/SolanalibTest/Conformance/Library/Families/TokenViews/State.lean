/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenViews.Common
import Solanalib.Specs.PinocchioToken.State
import Solanalib.Specs.PinocchioToken2022.State

/-!
# Token account and mint byte views (`pinocchio_token.State`, `pinocchio_token_2022.State`)

`Account::from_account_view` and `Mint::from_account_view` are registered as
total references over the AccountView pool; the checker decides their graph
up to the pool observation and the view the returned `Ref` denotes. The
getters take the live `Ref<Account>`/`Ref<Mint>` of the driver (see `Common`):
`amount` and `decimals` return values, `mint` and `owner` return field
references, observed as the account, data offset and current 32 bytes they
denote. `Account::state` is a panic-policy family; the checker instantiates it
with the policy of this target (`panic = "unwind"`: the panic message of the source,
state unchanged) and decides it through `state_graph`.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.TokenViews.State

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenViews

abbrev Pool := AccountView.State

/-! ## Parsers -/

/-- The value observation of a parser result: the view its guard denotes. -/
def parsedObs (result : Except Solanalib.Runtime.InstrError Ref) (after : Pool) :
    Except Solanalib.Runtime.InstrError (Option ViewObs) :=
  match result with
  | .ok ref => .ok (guardView after ref.guard)
  | .error e => .error e

def parserChecker (function reference : String)
    (run : Pool → Borrow.Handle → Except Solanalib.Runtime.InstrError Ref × Pool) : Checker where
  function
  generics := []
  reference
  decides := [reference]
  check := fun c => do
    let (before, frame) ← poolState c.state
    let h ← handleField c.args "account"
    resolves before.cells.length h
    let recorded ← parseOutcome (asExcept programError fun j => do pure (some (← viewObs j)))
      poolObs noReason noReason c.outcome
    pure (decideObserved (returnsOf (Unwind := Empty) (Terminal := Empty) run before h)
      (some (.returned (run before h).1 (run before h).2)) (returnsOf_graph run before h)
      (Outcome.observe parsedObs (fun s => ⟨booleanPoolObs s, frame⟩) id id) recorded
      (outcomeJson (exceptObsJson programErrorJson (optionJson viewObsJson)) poolObsJson emptyJson
        emptyJson))

/-! ## Getters over a live typed view -/

/-- The before-state and typed reference of a getter record: `args.ref` names
the account and the view of the live `Ref` of the driver. -/
def typedRef (c : Case) (kind : ViewKind) : Result (Pool × Ref × Frame) := do
  let (pool, frame) ← poolState c.state
  let r ← field c.args "ref"
  let view ← viewObs r
  unless view.offset = 0 ∧ view.length = kind.length do
    throw s!"typed reference must cover bytes [0, {kind.length}), got \
      {view.offset}+{view.length}"
  let (pool, guard) ← withMappedGuard pool view.account view.offset view.length
  pure (pool, ⟨guard, kind⟩, frame)

/-- `AccountReadable` (the `requires` of the amount and state contracts) is decided
by the current raw account view. -/
instance accountReadableDec (s : Pool) (r : Ref) : Decidable (AccountReadable s r) :=
  match h : currentAccount s r with
  | .ok raw => isTrue ⟨raw, h⟩
  | .error _ => isFalse fun ⟨_, h'⟩ => by rw [h] at h'; cases h'

/-- `MintReadable` (the `requires` of the decimals contracts) likewise. -/
instance mintReadableDec (s : Pool) (r : Ref) : Decidable (MintReadable s r) :=
  match h : currentMint s r with
  | .ok raw => isTrue ⟨raw, h⟩
  | .error _ => isFalse fun ⟨_, h'⟩ => by rw [h] at h'; cases h'

/-- The precondition of a model on a record, decided through a decidable predicate
`P` it is equivalent to. -/
structure Requires where
  /-- The name of the predicate, in the message of the checker for a record outside it. -/
  name : String
  holds : Pool → Ref → Prop
  dec : (s : Pool) → (r : Ref) → Decidable (holds s r)

def Requires.of (name : String) (pre : Pool → Ref → Prop) (P : Pool → Ref → Prop)
    [∀ s r, Decidable (P s r)] (equiv : ∀ s r, pre s r ↔ P s r) : Requires :=
  ⟨name, pre, fun s r => decidable_of_iff _ (equiv s r).symm⟩

/-- The verdict of the checker for a record outside the precondition of the model. -/
def outsidePrecondition (pre : Requires) : Verdict :=
  ⟨false, Json.str s!"outside the precondition {pre.name}"⟩

/-- Decide the getter reference `run` on a record, and the `requires` of the model: a record outside
it is rejected (the fallback value of the reference
there tests nothing the contract promises). -/
def getterCheck {V VO : Type} [DecidableEq VO] (kind : ViewKind) (pre : Requires)
    (run : Pool → Ref → V × Pool) (observe : V → Pool → VO) (parse : Json → Result VO)
    (render : VO → Json) (c : Case) : Result Verdict := do
  let (before, ref, frame) ← typedRef c kind
  let recorded ← parseOutcome parse poolObs noReason noReason c.outcome
  let verdict := decideObserved (returnsOf (Unwind := Empty) (Terminal := Empty) run before ref)
    (some (.returned (run before ref).1 (run before ref).2)) (returnsOf_graph run before ref)
    (Outcome.observe observe (fun s => ⟨booleanPoolObs s, frame⟩) id id) recorded
    (outcomeJson render poolObsJson emptyJson emptyJson)
  if @Decidable.decide (pre.holds before ref) (pre.dec before ref) then pure verdict
  else pure (outsidePrecondition pre)

/-- A getter checker decides two registered models on each record: the reference of the
version (`reference`, `run`, the `requires` of its contract as `pre`) and
the shared `Solanalib.Specs.Core.Token` model it is defined as (`shared`,
`sharedRun`, `sharedPre`; `Instructions/SharedToken.lean` proves the
references equal by `rfl`). Each is decided from its own names. -/
def getterChecker {V VO : Type} [DecidableEq VO] (function reference : String) (kind : ViewKind)
    (pre : Requires) (run : Pool → Ref → V × Pool) (shared : String) (sharedPre : Requires)
    (sharedRun : Pool → Ref → V × Pool) (observe : V → Pool → VO) (parse : Json → Result VO)
    (render : VO → Json) (decidesPre : Bool) : Checker where
  function
  generics := []
  reference
  decides := [reference, shared]
  decidesRequires := if decidesPre then [reference, shared] else []
  check := getterCheck kind pre run observe parse render
  checkModels := some (perModel [(reference, getterCheck kind pre run observe parse render),
    (shared, getterCheck kind sharedPre sharedRun observe parse render)])

/-- `contract` is the registered amount contract of the version; its `requires` is
`AccountReadable`, as is the precondition of the shared contract. -/
def amountChecker (function reference : String) (contract : Solanalib.Contracts.Model Pool Ref Nat)
    (equiv : ∀ s r, contract.requires s r ↔ AccountReadable s r) (run : Pool → Ref → Nat × Pool) :
    Checker :=
  getterChecker function reference .account (.of "AccountReadable" contract.requires
    AccountReadable equiv) run
    "Solanalib.Specs.Core.Token.amountReference"
    (.of "AccountReadable" amountContract.requires AccountReadable fun _ _ => Iff.rfl)
      amountReference
    (fun v _ => v) (asUInt 64) toJson true

def decimalsChecker (function reference : String) (contract : Solanalib.Contracts.Model Pool Ref
  UInt8)
    (equiv : ∀ s r, contract.requires s r ↔ MintReadable s r) (run : Pool → Ref → UInt8 × Pool) :
    Checker :=
  getterChecker function reference .mint (.of "MintReadable" contract.requires MintReadable equiv)
    run
    "Solanalib.Specs.Core.Token.decimalsReference"
    (.of "MintReadable" decimalsContract.requires MintReadable fun _ _ => Iff.rfl) decimalsReference
    (fun v _ => v.toNat) (asUInt 8) toJson true

/-- A returned `&Address` field reference: the account and data offset it
points into and the 32 bytes read through it. -/
structure KeyObs where
  account : Nat
  offset : Nat
  value : Solanalib.Runtime.Pubkey
  deriving DecidableEq

def keyObs (j : Json) : Result (Option KeyObs) := do
  pure (some ⟨← natField j "account" 64, ← natField j "offset" 64, ← pubkey (← field j
    "value")⟩)

def keyObsJson (k : KeyObs) : Json := Json.mkObj [("account", toJson k.account),
  ("offset", toJson k.offset), ("value", pubkeyJson k.value)]

/-- The observation of a field descriptor in the after-state: the account and
offset of the view of its still-live guard plus its offset, and the current key. -/
def keyRefObs (k : KeyRef) (after : Pool) : Option KeyObs :=
  match guardView after k.guard, currentKey after k with
  | some v, .ok key => some ⟨v.account, v.offset + k.offset, key⟩
  | _, _ => none

/-- The field-reference contracts require `True`. -/
def trivialRequires : Requires := ⟨"True", fun _ _ => True, fun _ _ => isTrue trivial⟩

def keyChecker (function reference : String) (run : Pool → Ref → KeyRef × Pool) (shared : String)
    (sharedRun : Pool → Ref → KeyRef × Pool) : Checker :=
  getterChecker function reference .account trivialRequires run shared trivialRequires sharedRun
    keyRefObs
    keyObs (optionJson keyObsJson) false

/-! ## `Account::state` -/

/-- The panic policy of this target: `panic = "unwind"` unwinds with the message of the source
(`invalid account state value: {value}`) and changes no state. -/
def unwindPolicy : StatePolicy where
  Unwind := String
  Terminal := Empty
  panic := Callback.ofFunction fun s byte => .unwound s!"invalid account state value: \
    {byte.toNat}"
    s

/-- The outcome of the state projection under `unwindPolicy`; `none` when the
reference is not readable (the family admits no exit there). -/
def stateComputed (before : Pool) (ref : Ref) : Option (Outcome Pool AccountState String Empty) :=
  match currentAccount before ref with
  | .error _ => none
  | .ok raw =>
    match decodeAccountState raw.stateByte with
    | some state => some (.returned state before)
    | none => some (.unwound s!"invalid account state value: {raw.stateByte.toNat}" before)

/-- The relation of the state family at `unwindPolicy` is the graph of `stateComputed`. -/
theorem stateRun_graph (before : Pool) (ref : Ref) (o : Outcome Pool AccountState String Empty) :
    stateRun unwindPolicy.panic before ref o ↔ stateComputed before ref = some o := by
  unfold stateRun stateComputed
  cases currentAccount before ref with
  | error e => dsimp only; exact ⟨False.elim, fun h => by cases h⟩
  | ok raw =>
    dsimp only
    cases decodeAccountState raw.stateByte with
    | some state =>
      dsimp only
      exact ⟨fun h => congrArg some h.symm, fun h => (Option.some.inj h).symm⟩
    | none =>
      dsimp only
      refine (Callback.map_ofFunction (fun impossible : Empty => nomatch impossible) _ before
        raw.stateByte o).trans ?_
      exact ⟨fun h => congrArg some h, fun h => Option.some.inj h⟩

def accountStates : List (String × AccountState) :=
  [("Uninitialized", .uninitialized), ("Initialized", .initialized), ("Frozen", .frozen)]

def accountState (j : Json) : Result AccountState := do
  let s ← j.getStr?
  match accountStates.find? (·.1 == s) with
  | some (_, v) => pure v
  | none => throw s!"unknown AccountState {s}"

def accountStateJson (v : AccountState) : Json :=
  Json.str ((accountStates.find? (·.2 == v)).map (·.1) |>.getD "?")

/-- Decide a state relation with its graph lemma on a record, and the `requires` of the family at
`unwindPolicy` (`AccountReadable`): a record outside it
is rejected. -/
def stateCheck (pre : Requires) (relation : Pool → Ref → Outcome Pool AccountState String Empty →
  Prop)
    (graph : ∀ before ref o, relation before ref o ↔ stateComputed before ref = some o) (c : Case) :
    Result Verdict := do
  let (before, ref, frame) ← typedRef c .account
  let recorded ← parseOutcome accountState poolObs (fun r => some r) noReason c.outcome
  let verdict := decideObserved (relation before ref) (stateComputed before ref) (graph before ref)
    (Outcome.observe (fun v _ => v) (fun s => ⟨booleanPoolObs s, frame⟩) id id) recorded
    (outcomeJson accountStateJson poolObsJson Json.str emptyJson)
  if @Decidable.decide (pre.holds before ref) (pre.dec before ref) then pure verdict
  else pure (outsidePrecondition pre)

/-- The relation of the shared state family at `unwindPolicy`. -/
theorem shared_state_graph (before : Pool) (ref : Ref) (o : Outcome Pool AccountState String Empty)
  :
    stateFamilyRun unwindPolicy before ref o ↔ stateComputed before ref = some o :=
  stateRun_graph before ref o

/-- The `requires` of the shared state family at `unwindPolicy`. -/
def sharedStatePre : Requires :=
  .of "AccountReadable" (stateFamily.contract unwindPolicy).requires AccountReadable fun _ _ =>
    Iff.rfl

/-- `relation` is the registered state reference of the version at `unwindPolicy`
and `pre` the `requires` of its family contract there; the shared
`Solanalib.Specs.Core.Token.stateFamilyRun` is decided as well, with the `requires` of the shared
family. -/
def stateChecker (function reference : String) (pre : Requires)
    (relation : Pool → Ref → Outcome Pool AccountState String Empty → Prop)
    (graph : ∀ before ref o, relation before ref o ↔ stateComputed before ref = some o) : Checker
      where
  function
  generics := []
  reference
  decides := [reference, "Solanalib.Specs.Core.Token.stateFamilyRun"]
  decidesRequires := [reference, "Solanalib.Specs.Core.Token.stateFamilyRun"]
  check := stateCheck pre relation graph
  checkModels := some (perModel [(reference, stateCheck pre relation graph),
    ("Solanalib.Specs.Core.Token.stateFamilyRun",
      stateCheck sharedStatePre (stateFamilyRun unwindPolicy) shared_state_graph)])

/-! ## Registered references -/

namespace V060
open Solanalib.Specs.PinocchioToken.state

theorem state_graph (before : Pool) (ref : Ref) (o : Outcome Pool AccountState String Empty) :
    account.Account.state_reference unwindPolicy before ref o ↔ stateComputed before ref = some o :=
  stateRun_graph before ref o

def checkers : List Checker := [
  parserChecker "pinocchio_token::state::account::Account::from_account_view"
    "Solanalib.Specs.PinocchioToken.state.account.Account.from_account_view_reference"
    account.Account.from_account_view_reference,
  parserChecker "pinocchio_token::state::mint::Mint::from_account_view"
    "Solanalib.Specs.PinocchioToken.state.mint.Mint.from_account_view_reference"
    mint.Mint.from_account_view_reference,
  amountChecker "pinocchio_token::state::account::Account::amount"
    "Solanalib.Specs.PinocchioToken.state.account.Account.amount_reference"
      account.Account.amount_contract
    (fun _ _ => Iff.rfl) account.Account.amount_reference,
  keyChecker "pinocchio_token::state::account::Account::mint"
    "Solanalib.Specs.PinocchioToken.state.account.Account.mint_reference"
      account.Account.mint_reference
    "Solanalib.Specs.Core.Token.mintReference" mintReference,
  keyChecker "pinocchio_token::state::account::Account::owner"
    "Solanalib.Specs.PinocchioToken.state.account.Account.owner_reference"
      account.Account.owner_reference
    "Solanalib.Specs.Core.Token.ownerReference" ownerReference,
  stateChecker "pinocchio_token::state::account::Account::state"
    "Solanalib.Specs.PinocchioToken.state.account.Account.state_reference"
    (.of "AccountReadable" (account.Account.state_contract.contract unwindPolicy).requires
      AccountReadable
      fun _ _ => Iff.rfl)
    (account.Account.state_reference unwindPolicy) state_graph,
  decimalsChecker "pinocchio_token::state::mint::Mint::decimals"
    "Solanalib.Specs.PinocchioToken.state.mint.Mint.decimals_reference" mint.Mint.decimals_contract
    (fun _ _ => Iff.rfl) mint.Mint.decimals_reference]

end V060

namespace V031
open Solanalib.Specs.PinocchioToken2022.state

theorem state_graph (before : Pool) (ref : Ref) (o : Outcome Pool AccountState String Empty) :
    account.Account.state_reference unwindPolicy before ref o ↔ stateComputed before ref = some o :=
  stateRun_graph before ref o

def checkers : List Checker := [
  parserChecker "pinocchio_token_2022::state::account::Account::from_account_view"
    "Solanalib.Specs.PinocchioToken2022.state.account.Account.from_account_view_reference"
    account.Account.from_account_view_reference,
  parserChecker "pinocchio_token_2022::state::mint::Mint::from_account_view"
    "Solanalib.Specs.PinocchioToken2022.state.mint.Mint.from_account_view_reference"
    mint.Mint.from_account_view_reference,
  amountChecker "pinocchio_token_2022::state::account::Account::amount"
    "Solanalib.Specs.PinocchioToken2022.state.account.Account.amount_reference"
      account.Account.amount_contract
    (fun _ _ => Iff.rfl) account.Account.amount_reference,
  keyChecker "pinocchio_token_2022::state::account::Account::mint"
    "Solanalib.Specs.PinocchioToken2022.state.account.Account.mint_reference"
      account.Account.mint_reference
    "Solanalib.Specs.Core.Token.mintReference" mintReference,
  keyChecker "pinocchio_token_2022::state::account::Account::owner"
    "Solanalib.Specs.PinocchioToken2022.state.account.Account.owner_reference"
      account.Account.owner_reference
    "Solanalib.Specs.Core.Token.ownerReference" ownerReference,
  stateChecker "pinocchio_token_2022::state::account::Account::state"
    "Solanalib.Specs.PinocchioToken2022.state.account.Account.state_reference"
    (.of "AccountReadable" (account.Account.state_contract.contract unwindPolicy).requires
      AccountReadable
      fun _ _ => Iff.rfl)
    (account.Account.state_reference unwindPolicy) state_graph,
  decimalsChecker "pinocchio_token_2022::state::mint::Mint::decimals"
    "Solanalib.Specs.PinocchioToken2022.state.mint.Mint.decimals_reference"
      mint.Mint.decimals_contract
    (fun _ _ => Iff.rfl) mint.Mint.decimals_reference]

end V031

end SolanalibTest.Conformance.Library.Families.TokenViews.State
