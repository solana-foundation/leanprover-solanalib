/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresAccounts
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresErrors
import SolanalibTest.Conformance.Library.Families.Anchor.Spl
import SolanalibTest.Conformance.Library.Families.Anchor.Misc
import SolanalibTest.Conformance.Library.Families.Anchor.TransferOwned

/-!
# The Anchor checkers with their decided preconditions

Each checker below decides, on every record, the registered `requires` of the
models it decides, through the deciders of `RequiresAccounts` and
`RequiresErrors` and their equivalence theorems (`decideBy`): a record outside
the precondition of a model is rejected by that model. The observation models of
the errors and the remaining Anchor models have trivial preconditions.

A record mutation breaks the decided preconditions of the constructors and
error models (the controls in `controls/Anchor.py`). The parser types every
lamports and data cell, and the checkers fix the vector ledger and builder
states, so no record leaves the other preconditions; for those the theorems
of the last section show, in the kernel, that the deciders reject an input
outside them.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Families.Anchor.RequiresAccounts
  SolanalibTest.Conformance.Library.Families.Anchor.RequiresErrors
open AnchorErrorOwned.Reference (StringId BoxId)
open SolanalibTest.Conformance.Library.Families.Anchor.Decide (onReturnedB onReturned_iff)
open SolanalibTest.Conformance.Library.Runtime
open SolanalibTest.Conformance.Library.Families.Anchor.Spl (asTransferArgs)

/-- Decide `p` through an executable decider and its equivalence. -/
def decideBy {p : Prop} (b : Bool) (h : b = true ↔ p) : Bool := @decide p (decidable_of_iff _ h)

/-! ## Constructors -/

open Construct in
def accountOwned (c : Case) : Result Bool := do
  let i ← inputs c
  pure (decideBy (p :=
    (accounts.account.Account.try_from_contract.contract
      (ownedTypes i.script)).requires (i.world, (heap0, i.aux)) i.args)
    _ (ownedReadyB_iff .account i.script (i.world, (heap0, i.aux)) i.args))

open Construct in
def accountObs (c : Case) : Result Bool := do
  let i ← inputs c
  pure (decideBy (p :=
    (accounts.account.Account.try_from_observation_contract.contract
      (obsIndex i.script)).requires (i.world, i.aux) i.args)
    _ (obsReadyB_iff .account i.script (i.world, i.aux) i.args))

open Construct in
def interfaceOwned (c : Case) : Result Bool := do
  let i ← inputs c
  pure (decideBy (p :=
    (accounts.interface_account.InterfaceAccount.try_from_contract.contract
      (ownedTypes i.script)).requires (i.world, (heap0, i.aux)) i.args)
    _ (ownedReadyB_iff .interfaceAccount i.script (i.world, (heap0, i.aux)) i.args))

open Construct in
def interfaceObs (c : Case) : Result Bool := do
  let i ← inputs c
  pure (decideBy (p :=
    (accounts.interface_account.InterfaceAccount.try_from_observation_contract.contract
      (obsIndex i.script)).requires (i.world, i.aux) i.args)
    _ (obsReadyB_iff .interfaceAccount i.script (i.world, i.aux) i.args))

open Construct in
def loaderOwned (c : Case) : Result Bool := do
  let i ← inputs c
  pure (decideBy (p :=
    (accounts.account_loader.AccountLoader.try_from_contract.contract
      (ownedTypes i.script)).requires (i.world, (heap0, i.aux)) i.args)
    _ (ownedReadyB_iff .loader i.script (i.world, (heap0, i.aux)) i.args))

open Construct in
def loaderObs (c : Case) : Result Bool := do
  let i ← inputs c
  pure (decideBy (p :=
    (accounts.account_loader.AccountLoader.try_from_observation_contract.contract
      (obsIndex i.script)).requires (i.world, i.aux) i.args)
    _ (obsReadyB_iff .loader i.script (i.world, i.aux) i.args))

def L : String := "Solanalib.Specs.AnchorLang.accounts."

def constructCheckers : List Checker := [
  withRequires [(L ++ "account.Account.try_from_run", accountOwned),
      (L ++ "account.Account.try_from_observation_run", accountObs)]
    (withFrame [("no syscalls", noSyscalls)] Construct.accountChecker),
  withRequires [(L ++ "interface_account.InterfaceAccount.try_from_run", interfaceOwned),
      (L ++ "interface_account.InterfaceAccount.try_from_observation_run", interfaceObs)]
    (withFrame [("no syscalls", noSyscalls)] Construct.interfaceChecker),
  withRequires [(L ++ "account_loader.AccountLoader.try_from_run", loaderOwned),
      (L ++ "account_loader.AccountLoader.try_from_observation_run", loaderObs)]
    (withFrame [("no syscalls", noSyscalls)] Construct.loaderChecker)]

/-! ## Loading -/

def obsLoadReadyB (mode : Borrow.Mode) {l : LoadIndex} (state : AccountInfo.State) (args : LoadArgs
  l) : Bool :=
  decide (mode = .exclusive ∧ args.loader.info.isWritable = false) || dataReadyB mode state
    args.loader.info.data

theorem obsLoadReadyB_iff (mode : Borrow.Mode) {l : LoadIndex} (state : AccountInfo.State) (args :
  LoadArgs l) :
    obsLoadReadyB mode state args = true ↔ LoadReady mode state args := by
  unfold obsLoadReadyB LoadReady
  by_cases blocked : mode = .exclusive ∧ args.loader.info.isWritable = false
  · simp [blocked]
  · simp only [blocked, decide_false, Bool.false_or, ↓reduceIte, dataReadyB_iff]

def loadInputs (size alignment : Nat) (c : Case) :
    Result (AccountInfo.State × LoadArgs (Loading.layout size alignment)) := do
  let (input, world) ← asWorld c.state
  let info ← infoAt input (← natField c.args "account")
  pure (world, ⟨profile, ⟨info⟩, ← natField c.args "data_address"⟩)

def loadOwned (mutable : Bool) (size alignment : Nat) (c : Case) : Result Bool := do
  let (world, args) ← loadInputs size alignment c
  let l := Loading.layout size alignment
  if mutable then
    pure (decideBy (p :=
      (accounts.account_loader.AccountLoader.load_mut_contract.contract
        (Loading.types l)).requires (world, Loading.heap0) args) _ (admissionB_iff .exclusive l
          (world, Loading.heap0) args))
  else
    pure (decideBy (p :=
      (accounts.account_loader.AccountLoader.load_contract.contract
        (Loading.types l)).requires (world, Loading.heap0) args) _ (admissionB_iff .shared l
          (world, Loading.heap0) args))

def loadObs (mutable : Bool) (size alignment : Nat) (c : Case) : Result Bool := do
  let (world, args) ← loadInputs size alignment c
  let l := Loading.layout size alignment
  if mutable then
    pure (decideBy (p :=
      (accounts.account_loader.AccountLoader.load_mut_observation_contract.contract
        l).requires world args) _ (obsLoadReadyB_iff .exclusive world args))
  else
    pure (decideBy (p :=
      (accounts.account_loader.AccountLoader.load_observation_contract.contract
        l).requires world args) _ (obsLoadReadyB_iff .shared world args))

def loadCheckers : List Checker :=
  ([(false, "conformance_anchor::script::Zc", 16, 8), (false, "conformance_anchor::script::\
    Zc16",
    32, 16),
    (true, "conformance_anchor::script::Zc", 16, 8), (true, "conformance_anchor::script::Zc\
      16", 32,
      16)]).map
    fun (mutable, ty, size, alignment) =>
      let name := if mutable then "load_mut" else "load"
      withRequires [(L ++ s!"account_loader.AccountLoader.{name}_run", loadOwned mutable size
        alignment),
          (L ++ s!"account_loader.AccountLoader.{name}_observation_run", loadObs mutable size
            alignment)]
        (withFrame [("no syscalls", noSyscalls)] (Loading.loadChecker mutable ty size alignment))

/-! ## Errors -/

open Errors in
def fromAnchorOwned (c : Case) : Result Bool := do
  let heap ← Owned.asHeap c.state
  let payload ← match ← Owned.asPayload (← field c.args "error") with
    | .anchor p => pure p
    | .program _ => throw "From<AnchorError> takes an AnchorError"
  pure (decideBy _ (fromAnchor_requires_iff heap payload).symm)

open Errors in
def withPubkeysOwned (c : Case) : Result Bool := do
  let heap ← Owned.asHeap c.state
  let error ← boxArg (← field c.args "error")
  pure (decideBy _ (withPubkeys_requires_iff heap (error, ← keyField c.args "left", ← keyField
    c.args "right")).symm)

open Errors in
def withValuesOwned (c : Case) : Result Bool := do
  let heap ← Owned.asHeap c.state
  let log ← asList asOpEvent (← field c.state "log")
  let error ← boxArg (← field c.args "error")
  let args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand :=
    ⟨error, ← asOperand (← field c.args "left"), ← asOperand (← field c.args "right")⟩
  pure (decideBy _ (withValues_requires_iff (heap, log) args).symm)

def E : String := "Solanalib.Specs.AnchorLang.error.Error."

def errorCheckers : List Checker := [
  withRequires [(E ++ "from_anchor_error_run", fromAnchorOwned)]
    (withFrame [("no syscalls", noSyscalls)] Errors.fromAnchorChecker),
  withRequires [(E ++ "with_pubkeys_run", withPubkeysOwned)]
    (withFrame [("no syscalls", noSyscalls)] Errors.withPubkeysChecker),
  withRequires [(E ++ "with_values_run", withValuesOwned)]
    (withFrame [("no syscalls", noSyscalls)] Errors.withValuesChecker)]

/-! ## `anchor_spl::token::accessor::amount` -/

def amountInputs (c : Case) : Result (AccountInfo.State × AccountInfo.Args) := do
  let (input, world) ← asWorld c.state
  let info ← infoAt input (← natField c.args "account")
  pure (world, ⟨profile, info⟩)

def amountOwned (c : Case) : Result Bool := do
  let (world, args) ← amountInputs c
  pure (decideBy (p := (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract
    Spl.amountTypes).requires
    (world, Spl.heap0) args) _ (dataReadyB_iff .shared world args.info.data))

def amountObs (c : Case) : Result Bool := do
  let (world, args) ← amountInputs c
  pure (decideBy (p :=
    Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_contract.requires world args) _
    (dataReadyB_iff .shared world args.info.data))

def amountChecker : Checker :=
  withRequires [("Solanalib.Specs.AnchorSpl.token.accessor.amount_run", amountOwned),
      ("Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_run", amountObs)]
    (withFrame [("no syscalls", noSyscalls)] Spl.amountChecker)

/-! ## `CpiContext::new_with_signer` (`EmptyReady`) -/

def emptyReadyB (types : AnchorContextOwned.Types) (before : types.State) : Bool :=
  decide (types.remaining.current (types.remaining.empty before).2 (types.remaining.empty before).1
    = some []) &&
  decide (types.remaining.current before (types.remaining.empty before).1 = none)

theorem emptyReadyB_iff (types : AnchorContextOwned.Types) (before : types.State) :
    emptyReadyB types before = true ↔ AnchorContextOwned.EmptyReady types before := by
  unfold emptyReadyB
  rw [iff_of_eq (Bool.and_eq_true _ _), decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

def contextOwned (c : Case) : Result Bool := do
  let input ← loaderInput (← field c.state "input")
  let a ← field c.args "accounts"
  let accounts : Misc.Accounts := ⟨← infoAt input (← natField a "from"), ← infoAt input (← natField
    a "to"),
    ← infoAt input (← natField a "authority")⟩
  let args : AnchorContext.NewWithSignerArgs Misc.Accounts :=
    ⟨← keyField c.args "program_id", accounts, ← Misc.asSeeds (← field c.args "signer_seeds")⟩
  pure (decideBy (p :=
    (context.CpiContext.new_with_signer_contract.contract
    Misc.ownedTypes).requires
    [] args) _ (emptyReadyB_iff Misc.ownedTypes []))

def contextChecker : Checker :=
  withRequires [("Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_run", contextOwned)]
    (withFrame [("no syscalls", noSyscalls), ("accounts unchanged", accountsUnchanged)]
      Misc.contextChecker)

/-- `Misc.checkers` with the context checker deciding its precondition. -/
def miscCheckers : List Checker := [
  withFrame [("no syscalls", noSyscalls), ("accounts unchanged", accountsUnchanged)]
    Misc.toInfoChecker,
  contextChecker,
  withFrame [("replies unchanged", Misc.repliesUnchanged)] Misc.logChecker]

/-! ## `anchor_spl::token::transfer` (`BuildReady`) -/

open AnchorSplTransfer in
/-- Every successful build leaves its instruction `live` (the builder has a
graph, `TransferOwned.build_graph`, at every builder state). -/
def buildReadyWithB (live : TransferOwned.S → TransferOwned.IV → Bool) (before : TransferOwned.S)
    (args : Args Sample.resources) : Bool :=
  onReturnedB (TransferOwned.buildFn before (plan args)) fun v after =>
    match v with
    | .ok instruction => live after instruction
    | .error _ => true

/-- Both vectors of a constructed instruction are current in the sample builder. -/
def sampleLive (s : TransferOwned.S) (i : TransferOwned.IV) : Bool :=
  (TransferOwned.B.metas.current s i.metas).isSome && (TransferOwned.B.bytes.current s
    i.data).isSome

open AnchorSplTransfer in
theorem buildReadyB_iff (before : TransferOwned.S) (args : Args Sample.resources) :
    buildReadyWithB sampleLive before args = true ↔ BuildReady Sample.resources before args := by
  unfold buildReadyWithB
  refine (onReturned_iff (TransferOwned.build_graph before (plan args))
    (fun v after => match v with
      | .ok instruction => ConstructedReadable Sample.resources after instruction
      | .error _ => True) _ ?_).trans ?_
  · intro v after
    cases v with
    | error e => exact ⟨fun _ => trivial, fun _ => rfl⟩
    | ok instruction =>
      show sampleLive after instruction = true ↔ ConstructedReadable Sample.resources after
        instruction
      unfold sampleLive ConstructedReadable Owned.VectorOps.Live
      rw [iff_of_eq (Bool.and_eq_true _ _), Option.isSome_iff_exists, Option.isSome_iff_exists]
  · exact ⟨fun h instruction after run => h (.ok instruction) after run,
      fun h v after run => by
        cases v with
        | error e => trivial
        | ok instruction => exact h instruction after run⟩

open AnchorSplTransfer in
/-- At the builder state of the checker (both vector ledgers empty) the precondition
holds for every argument (`Sample.build_ready`); it is decided by
`buildReadyWithB sampleLive`, which `transfer_decider_rejects` shows can reject. -/
def transferOwned (c : Case) : Result Bool := do
  let a ← asTransferArgs c
  let script ← syscallsOf c.state
  let ret ← match script.replies with
    | [r] => pure r.ret
    | _ => throw "one scripted invocation reply expected"
  let (_, world) ← asWorld c.state
  let inv : Spl.Invocation := ⟨ret, world⟩
  let args : Args Sample.resources :=
    ⟨⟨a.context.accounts, (show Sample.resources.RemainingResource from (0 : Nat)),
      a.context.programId,
      a.context.signerSeeds⟩, a.amount⟩
  let before : TransferOwned.S := (([], []), ⟨TransferOwned.heap0, [], [some []], []⟩)
  pure (decideBy (p := (Solanalib.Specs.AnchorSpl.token.transfer_contract.contract
    (TransferOwned.types inv)).requires
    before args) _ (buildReadyB_iff before args))

def transferChecker : Checker :=
  withRequires [("Solanalib.Specs.AnchorSpl.token.transfer_run", transferOwned)]
    TransferOwned.checker

/-! ## Kernel-checked rejections outside the preconditions no record can leave -/

/-- A world whose data handle `⟨0⟩` holds lamports. The parser never builds
one: it gives each account a lamports cell and a data cell. -/
def illTyped : AccountInfo.State := ⟨[⟨.lamports 0, policy⟩, ⟨.lamports 0, policy⟩], []⟩

/-- A writable account whose data handle is `⟨0⟩` and lamports handle `⟨1⟩`. -/
def illInfo : AccountInfo.Value := ⟨.zero, ⟨1⟩, ⟨0⟩, .zero, 0, false, true, false, ⟨0⟩⟩

theorem dataReady_illTyped (mode : Borrow.Mode) : dataReadyB mode illTyped ⟨0⟩ = false := by
  cases mode <;> rfl

theorem load_rejects_illTyped (l : LoadIndex) (address : Nat) :
    ¬ (accounts.account_loader.AccountLoader.load_contract.contract
      (Loading.types l)).requires
      (illTyped, Loading.heap0) ⟨profile, ⟨illInfo⟩, address⟩ := fun h => by
  have e : admissionB .shared l (illTyped, Loading.heap0) ⟨profile, ⟨illInfo⟩, address⟩ = false :=
    rfl
  exact absurd (e.symm.trans ((admissionB_iff _ _ _ _).mpr h)) Bool.false_ne_true

theorem load_mut_rejects_illTyped (l : LoadIndex) (address : Nat) :
    ¬ (accounts.account_loader.AccountLoader.load_mut_contract.contract
      (Loading.types l)).requires
      (illTyped, Loading.heap0) ⟨profile, ⟨illInfo⟩, address⟩ := fun h => by
  have e : admissionB .exclusive l (illTyped, Loading.heap0) ⟨profile, ⟨illInfo⟩, address⟩ = false
    := rfl
  exact absurd (e.symm.trans ((admissionB_iff _ _ _ _).mpr h)) Bool.false_ne_true

theorem load_observation_rejects_illTyped (l : LoadIndex) (address : Nat) :
    ¬ (accounts.account_loader.AccountLoader.load_observation_contract.contract l).requires
      illTyped ⟨profile, ⟨illInfo⟩, address⟩ := fun h => by
  have e : obsLoadReadyB .shared illTyped (⟨profile, ⟨illInfo⟩, address⟩ : LoadArgs l) = false :=
    rfl
  exact absurd (e.symm.trans ((obsLoadReadyB_iff _ _ _).mpr h)) Bool.false_ne_true

theorem load_mut_observation_rejects_illTyped (l : LoadIndex) (address : Nat) :
    ¬ (accounts.account_loader.AccountLoader.load_mut_observation_contract.contract l).requires
      illTyped ⟨profile, ⟨illInfo⟩, address⟩ := fun h => by
  have e : obsLoadReadyB .exclusive illTyped (⟨profile, ⟨illInfo⟩, address⟩ : LoadArgs l) = false
    := rfl
  exact absurd (e.symm.trans ((obsLoadReadyB_iff _ _ _).mpr h)) Bool.false_ne_true

theorem amount_rejects_illTyped :
    ¬ (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract Spl.amountTypes).requires
      (illTyped, Spl.heap0) ⟨profile, illInfo⟩ := fun h => by
  have e := dataReady_illTyped .shared
  exact absurd (e.symm.trans ((dataReadyB_iff _ _ _).mpr h)) Bool.false_ne_true

theorem amount_observation_rejects_illTyped :
    ¬ Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_contract.requires illTyped
      ⟨profile, illInfo⟩ := fun h => by
  have e := dataReady_illTyped .shared
  exact absurd (e.symm.trans ((dataReadyB_iff _ _ _).mpr h)) Bool.false_ne_true

/-- One owner call returning the owner of the account, which passes the owner check. -/
def ownerScript : Construct.Script := ⟨[⟨.zero, none, false⟩], [], [], 0, 1⟩

theorem loader_observation_rejects_illTyped :
    ¬ (accounts.account_loader.AccountLoader.try_from_observation_contract.contract
      (Construct.obsIndex ownerScript)).requires (illTyped, ⟨[.zero], []⟩) ⟨profile, illInfo⟩ :=
        fun h => by
  have e : obsReadyB .loader ownerScript (illTyped, ⟨[.zero], []⟩) ⟨profile, illInfo⟩ = false := by
    decide
  exact absurd (e.symm.trans ((obsReadyB_iff _ _ _ _).mpr h)) Bool.false_ne_true

/-- A vector ledger whose empty construction reuses identity 0. -/
def reusingTypes : AnchorContextOwned.Types where
  State := Owned.VectorState AccountInfo.Value
  Accounts := Misc.Accounts
  Resource := Nat
  Unwind := Empty
  Terminal := Empty
  remaining := { Owned.vectorReference with empty := fun state => (0, state) }

theorem new_with_signer_decider_rejects : emptyReadyB reusingTypes ([some []] : Owned.VectorState
  AccountInfo.Value) = false := by
  decide

open AnchorSplTransfer in
/-- The transfer decider rejects a build whose instruction is not readable: at
the arguments of the sample the build returns an instruction (`Sample.builder_returns`),
and with a liveness test that holds of nothing the decider answers `false`. With
the sample builder no state makes a built instruction unreadable, so no record
can leave this precondition. -/
theorem transfer_decider_rejects :
    buildReadyWithB (fun _ _ => false) Sample.initial Sample.args = false := by
  unfold buildReadyWithB
  have g := (TransferOwned.build_graph Sample.initial (plan Sample.args) _).mp
    Sample.builder_returns
  rw [g]
  rfl

end SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck
