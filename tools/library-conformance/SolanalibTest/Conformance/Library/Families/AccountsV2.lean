/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV2.Requires

/-!
# Family `AccountsV2`: solana-account-view 2.0.0

Driver `rust/accounts-v2`, corpus `solana_account_view`. The state
projection is described in `AccountsV2/Projection.lean`, the scripted `try_map`
callbacks in `AccountsV2/Map.lean`.

* The nine `AccountView.Pool` models are total functions registered as
  `RealizedBy` references; each checker evaluates the registered function and
  decides its graph (`returnsOf`).
* The six `Observation` models (the single-account API) have no Rust
  item of their own. Each is decided on every record of the `AccountView`
  method whose result it observes, through the projection of the specification
  `AccountView.observe` of the pool state at the account of the call: the record is
  admitted only if both the pool model and the observation reference admit it.
  The observation result of an acquisition is the bytes the returned guard
  denotes, read through its private `value` pointer at the call.
* The seven `Ref`/`RefMut` families are decided at the byte-range index
  `sliceProfile` (`T = [u8]` and, for mapped targets, `T = u8`); dereference and
  release are graphs (`*_evaluated`, by `rfl`), `try_map` is decided through
  `tryMap_function_iff` at `mapProfile`.

A native reference returned by `Deref::deref`/`DerefMut::deref_mut` denotes the
model `DataRef` of the argument guard exactly when it addresses the current target of that guard
(account, offset, length) in the state after the call; its
mutability is its type. A returned `&Address` denotes the account whose address
field it addresses.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.SolanaAccountView

namespace SolanalibTest.Conformance.Library.Families.AccountsV2

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! ## Generic deciders -/

/-- Decide a pool reference, registered as a total function, on a record:
first the precondition of its contract, then its graph. -/
def poolCheck {A V : Type} [DecidableEq V] (pre : Pre PoolState A) (model : PoolState → A → V ×
  PoolState)
    (args : Native → Json → Result A) (value : Json → Result (Option V)) (renderValue : V → Json)
    (c : Case) : Result Verdict := do
  let before ← parseBefore c.state
  let a ← args before c.args
  pre.check before.state a
  let recorded ← parseReturned value (parseAfter before) c.outcome
  return decideReturnsOpt (returnsOf model) model rfl before.state a recorded renderValue stateJson

/-- Decide an observation reference on the record of the pool call at `handle`,
with both states projected by `AccountView.observe`: first the precondition of its contract at the
observed state, then its graph. -/
def observationCheck {A V : Type} [DecidableEq V] (pre : Pre ObsState A) (op : ObsState → A → V ×
  ObsState)
    (args : Json → Result A) (value : Json → Result (Option V))
    (renderValue : V → Json) (c : Case) : Result Verdict := do
  let before ← parseBefore c.state
  let h ← handleArg before c.args
  let a ← args c.args
  let observed := AccountView.observe before.state h
  pre.check observed a
  let observeAfter (j : Json) : Result (Option ObsState) := do
    return (← parseAfter before j).map (AccountView.observe · h)
  let recorded ← parseReturned value observeAfter c.outcome
  return decideReturnsOpt (returnsOf op) op rfl observed a recorded renderValue obsStateJson

def unitValue (j : Json) : Result (Option Unit) := do asUnit j; return some ()
def natValue (j : Json) : Result (Option Nat) := some' (asUInt 64) j
def boolValue (j : Json) : Result (Option Bool) := some' Json.getBool? j
def unitArgs (_ : Json) : Result Unit := pure ()

/-! ## AccountView: pool models and their observations -/

def accountView (name : String) : String := s!"solana_account_view::AccountView::{name}"
def pool (name : String) : String := s!"Solanalib.Specs.SolanaAccountView.AccountView.Pool.\
  {name}_model"
def observation (name : String) : String :=
  s!"Solanalib.Specs.SolanaAccountView.AccountView.Observation.reference.{name}"
def reference : String := "Solanalib.Specs.SolanaAccountView.AccountView.Observation.refere\
  nce"

/-- `HasAccount`, the presence of the cell of the handle, decided (the reader already
makes every handle the position of a parsed account). -/
def hasAccountPre {A : Type} (contract : Solanalib.Contracts.Model PoolState A Nat) (handle : A →
  Handle)
    (same : ∀ s a, contract.requires s a = s.HasAccount (handle a)) : Pre PoolState A :=
  ⟨contract.requires, fun s a => (same s a) ▸ inferInstance, (fun _ _ =>
    "the account referenced by the handle is missing (HasAccount)")⟩

/-- A precondition that is `True` by definition, decided as such. -/
def truePre {S A V : Type} (contract : Solanalib.Contracts.Model S A V) (same : ∀ s a,
  contract.requires s a = True) :
    Pre S A :=
  ⟨contract.requires, fun s a => (same s a) ▸ instDecidableTrue, (fun _ _ => "True")⟩

/-- The cell whose `address` field the returned `&Address` addresses, if any. -/
def addressValue (j : Json) : Result (Option AccountView.AddressRef) := do
  match ← field j "cell" with
  | .null => return none
  | c => return some ⟨⟨← c.getNat?⟩⟩

def addressChecker : Checker where
  function := accountView "address"
  generics := []
  reference := pool "address"
  decides := [pool "address"]
  decidesRequires := [pool "address"]
  check := poolCheck (truePre AccountView.Pool.address_contract
    fun _ _ => rfl)
    AccountView.Pool.address_model handleArg addressValue
    fun r => Json.mkObj [("cell", toJson r.account.cell)]

def closePre : Pre PoolState Handle :=
  ⟨AccountView.Pool.close_header_contract.requires,
    fun s h => inferInstanceAs (Decidable (AccountView.isBorrowed s h = false → s.HasAccount h)),
    (fun _ _ => "an unborrowed account is missing (HasAccount)")⟩

def closeChecker : Checker where
  function := accountView "close"
  generics := []
  reference := pool "close_header"
  decides := [pool "close_header"]
  decidesRequires := [pool "close_header"]
  check := poolCheck closePre AccountView.Pool.close_header_model
    handleArg
    (optExcept programError unitValue) (exceptJson errorJson fun _ => Json.null)

def ownedByPre : Pre PoolState (Handle × Solanalib.Runtime.Pubkey) :=
  ⟨AccountView.Pool.owned_by_contract.requires,
    fun s a => inferInstanceAs (Decidable (s.HasAccount a.1)), (fun _ _ =>
      "the account referenced by the handle is missing (HasAccount)")⟩

def ownedByChecker : Checker where
  function := accountView "owned_by"
  generics := []
  reference := pool "owned_by"
  decides := [pool "owned_by"]
  decidesRequires := [pool "owned_by"]
  check := poolCheck ownedByPre AccountView.Pool.owned_by_model
    (fun n j => return (← handleArg n j, ← pubkey (← field j "program"))) boolValue toJson

/-- A pool member decided together with the observation model of the same method. -/
def combined (name obsName : String) (poolC obsC : Case → Result Verdict) : Checker where
  function := accountView name
  generics := []
  reference := pool name ++ "&" ++ observation obsName
  check := fun c => do
    let p ← poolC c
    let o ← obsC c
    return both p o
  decides := [pool name, reference]
  decidesRequires := [pool name, reference]
  checkModels := some (perModel [(pool name, poolC), (reference, obsC)])

def scalarPre (contract : Solanalib.Contracts.Model PoolState Handle Nat) (same : ∀ s h,
  contract.requires s h = s.HasAccount h) :
    Pre PoolState Handle :=
  hasAccountPre contract id same

def dataLenPre : Pre PoolState Handle :=
  scalarPre AccountView.Pool.data_len_contract fun _ _ => rfl

def lamportsPre : Pre PoolState Handle :=
  scalarPre AccountView.Pool.lamports_contract fun _ _ => rfl

def dataLenChecker : Checker :=
  combined "data_len" "dataLen"
    (poolCheck dataLenPre
      AccountView.Pool.data_len_model handleArg natValue toJson)
    (observationCheck (truePre
      AccountView.Observation.data_len_contract fun _ _ => rfl)
      AccountView.Observation.reference.dataLen unitArgs natValue
        toJson)

def lamportsChecker : Checker :=
  combined "lamports" "lamports"
    (poolCheck lamportsPre
      AccountView.Pool.lamports_model handleArg natValue toJson)
    (observationCheck (truePre
      AccountView.Observation.lamports_contract fun _ _ => rfl)
      AccountView.Observation.reference.lamports unitArgs
        natValue toJson)

def isSignerPre : Pre PoolState Handle :=
  ⟨AccountView.Pool.is_signer_contract.requires,
    fun s h => inferInstanceAs (Decidable (s.HasAccount h)), (fun _ _ =>
      "the account referenced by the handle is missing (HasAccount)")⟩

def isSignerChecker : Checker :=
  combined "is_signer" "isSigner"
    (poolCheck isSignerPre AccountView.Pool.is_signer_model
      handleArg boolValue toJson)
    (observationCheck (truePre
      AccountView.Observation.is_signer_contract fun _ _ => rfl)
      AccountView.Observation.reference.isSigner unitArgs
        boolValue toJson)

def lamportsArg (j : Json) : Result Nat := do asUInt 64 (← field j "lamports")

def setLamportsPre : Pre PoolState (Handle × Nat) :=
  ⟨AccountView.Pool.set_lamports_contract.requires,
    fun s a => inferInstanceAs (Decidable (s.HasAccount a.1)), (fun _ _ =>
      "the account referenced by the handle is missing (HasAccount)")⟩

def obsSetLamportsPre : Pre ObsState Nat :=
  ⟨AccountView.Observation.set_lamports_contract.requires,
    fun _ v => inferInstanceAs (Decidable (v < Solanalib.Runtime.U64_LIMIT)), (fun _ _ =>
      "the value is not below 2^64")⟩

def setLamportsChecker : Checker :=
  combined "set_lamports" "setLamports"
    (poolCheck setLamportsPre AccountView.Pool.set_lamports_model
      (fun n j => return (← handleArg n j, ← lamportsArg j)) unitValue (fun _ => Json.null))
    (observationCheck obsSetLamportsPre
      AccountView.Observation.reference.setLamports
      lamportsArg unitValue (fun _ => Json.null))

/-- The pool result of an acquisition: the ghost identity of the returned guard. -/
def acquiredGuard (j : Json) : Result (Option Guard) := do some' parseGuard (← field j
  "guard")

/-- The observation result of an acquisition: the bytes the returned guard denotes. -/
def acquiredBytes (j : Json) : Result (Option Solanalib.Runtime.Bytes) := do some' asBytes (← field
  j "bytes")

def borrowError (j : Json) : Result (Option AccountViewObservation.BorrowError) := do
  match ← programError j with
  | some .accountBorrowFailed => return some .accountBorrowFailed
  | _ => return none

def borrowResultJson : AccountViewObservation.BorrowResult → Json :=
  exceptJson (fun _ => "AccountBorrowFailed") bytesJson

/-- The acquisition observations require `State.Valid` of the observed account,
decided through `obsValid_iff`. -/
def obsValidPre (contract : Solanalib.Contracts.Model ObsState Unit
  AccountViewObservation.BorrowResult)
    (same : ∀ s, contract.requires s () = s.Valid) : Pre ObsState Unit :=
  ⟨contract.requires, fun s a => by
      cases a
      rw [same]
      exact decidable_of_iff _ (obsValid_iff s).symm,
    (fun _ _ => "the observed account is not Valid (u64 bounds, lease count, byte \
      availability)")⟩

def tryBorrowChecker : Checker :=
  combined "try_borrow" "tryBorrow"
    (poolCheck (truePre AccountView.Pool.try_borrow_contract fun
      _ _ => rfl)
      AccountView.Pool.try_borrow_model handleArg
      (optExcept programError acquiredGuard) (exceptJson errorJson guardJson))
    (observationCheck (obsValidPre
      AccountView.Observation.try_borrow_contract fun _ => rfl)
      AccountView.Observation.reference.tryBorrow unitArgs
      (optExcept borrowError acquiredBytes) borrowResultJson)

def tryBorrowMutChecker : Checker :=
  combined "try_borrow_mut" "tryBorrowMut"
    (poolCheck (truePre AccountView.Pool.try_borrow_mut_contract
      fun _ _ => rfl)
      AccountView.Pool.try_borrow_mut_model handleArg
      (optExcept programError acquiredGuard) (exceptJson errorJson guardJson))
    (observationCheck (obsValidPre
      AccountView.Observation.try_borrow_mut_contract fun _ =>
      rfl)
      AccountView.Observation.reference.tryBorrowMut unitArgs
      (optExcept borrowError acquiredBytes) borrowResultJson)

/-! ## Ref and RefMut at the byte-range index -/

/-- Shared dereference at `sliceProfile` is the graph of descriptor construction. -/
theorem ref_deref_evaluated :
    Ref.deref_model AccountView.sliceProfile =
      returnsOf (fun (before : World) (guard : Guard) => ((⟨guard, false⟩ : AccountView.DataRef),
        before)) :=
  rfl

/-- `RefMut` read-only dereference at `sliceProfile`. -/
theorem ref_mut_deref_evaluated :
    RefMut.deref_model AccountView.sliceProfile =
      returnsOf (fun (before : World) (guard : Guard) => ((⟨guard, false⟩ : AccountView.DataRef),
        before)) :=
  rfl

/-- `RefMut` mutable dereference at `sliceProfile`. -/
theorem ref_mut_deref_mut_evaluated :
    RefMut.deref_mut_model AccountView.sliceProfile =
      returnsOf (fun (before : World) (guard : Guard) => ((⟨guard, true⟩ : AccountView.DataRef),
        before)) :=
  rfl

/-- Guard destruction at `sliceProfile` is the graph of the registry release. -/
theorem ref_release_evaluated :
    Ref.release_model AccountView.sliceProfile =
      returnsOf (fun (before : World) (guard : Guard) => ((), ((Borrow.release before.1 guard).2,
        before.2))) :=
  rfl

theorem ref_mut_release_evaluated :
    RefMut.release_model AccountView.sliceProfile =
      returnsOf (fun (before : World) (guard : Guard) => ((), ((Borrow.release before.1 guard).2,
        before.2))) :=
  rfl

/-- The native reference returned by a dereference, as the model `DataRef` of
the argument guard if it addresses the current target of that guard. -/
def dataRefIn (guard : Guard) (after : World) (j : Json) : Result (Option AccountView.DataRef) := do
  let writable ← (← field j "mutable").getBool?
  let offset ← natField j "offset"
  let length ← natField j "length"
  match ← field j "cell" with
  | .null => return none
  | cj =>
    let cell ← cj.getNat?
    match after.1.resolve guard with
    | some slot =>
      return if slot.cell = ⟨cell⟩ ∧ slot.view = ⟨offset, length⟩ then some ⟨guard, writable⟩ else
        none
    | none => return none

def dataRefJson (r : AccountView.DataRef) : Json :=
  Json.mkObj [("guard", guardJson r.guard), ("mutable", toJson r.writable)]

/-- Decide a dereference family at `sliceProfile`. -/
def derefCheck (relation : World → Guard → Outcome World AccountView.DataRef Empty Empty → Prop)
    (writable : Bool)
    (evaluated : relation = returnsOf (fun (before : World) (guard : Guard) =>
      ((⟨guard, writable⟩ : AccountView.DataRef), before)))
    (c : Case) : Result Verdict := do
  let native ← parseBefore c.state
  let before : World := (native.state, ())
  let guard ← guardArg c.args
  let recorded ← match ← (← field c.outcome "exit").getStr? with
    | "returned" => do
      match ← parseWorld native (← field c.outcome "state") with
      | some after => pure ((← dataRefIn guard after (← field c.outcome "result")).map (.returned ·
        after))
      | none => pure none
    | _ => pure none
  return decideReturnsOpt relation _ evaluated before guard recorded dataRefJson worldJson

/-- `Ref::release` requires a live guard, decided through `release_requires_iff`. -/
def refReleasePre : Pre World Guard :=
  ⟨fun w g => (Ref.release_contract.contract
    AccountView.sliceProfile).requires w g,
    fun w g => decidable_of_iff _ (release_requires_iff .shared w g).symm, (fun _ _ =>
      "the guard is not live")⟩

def refMutReleasePre : Pre World Guard :=
  ⟨fun w g => (RefMut.release_contract.contract
    AccountView.sliceProfile).requires w g,
    fun w g => decidable_of_iff _ (release_requires_iff .exclusive w g).symm, (fun _ _ =>
      "the guard is not live")⟩

def releaseCheck (pre : Pre World Guard) (relation : World → Guard → Outcome World Unit Empty Empty
  → Prop)
    (evaluated : relation = returnsOf (fun (before : World) (guard : Guard) =>
      ((), ((Borrow.release before.1 guard).2, before.2))))
    (c : Case) : Result Verdict := do
  let native ← parseBefore c.state
  let before : World := (native.state, ())
  let guard ← guardArg c.args
  pre.check before guard
  let recorded ← parseReturned unitValue (parseWorld native) c.outcome
  return decideReturnsOpt relation _ evaluated before guard recorded (fun _ => Json.null) worldJson

def refType (kind : String) : String := s!"solana_account_view::{kind}<'_, T>"

def derefCheckers : List Checker := ["[u8]", "u8"].flatMap fun t => [
  { function := s!"<{refType "Ref"} as core::ops::deref::Deref>::deref"
    generics := [("T", t)]
    reference := "Solanalib.Specs.SolanaAccountView.Ref.deref_model"
    decides := ["Solanalib.Specs.SolanaAccountView.Ref.deref_model"]
    check := derefCheck (Ref.deref_model
      AccountView.sliceProfile) false
      ref_deref_evaluated },
  { function := s!"<{refType "RefMut"} as core::ops::deref::Deref>::deref"
    generics := [("T", t)]
    reference := "Solanalib.Specs.SolanaAccountView.RefMut.deref_model"
    decides := ["Solanalib.Specs.SolanaAccountView.RefMut.deref_model"]
    check := derefCheck (RefMut.deref_model
      AccountView.sliceProfile) false
      ref_mut_deref_evaluated },
  { function := s!"<{refType "RefMut"} as core::ops::deref::DerefMut>::deref_mut"
    generics := [("T", t)]
    reference := "Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_model"
    decides := ["Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_model"]
    check := derefCheck (RefMut.deref_mut_model
      AccountView.sliceProfile) true
      ref_mut_deref_mut_evaluated },
  { function := s!"<{refType "Ref"} as core::ops::drop::Drop>::drop"
    generics := [("T", t)]
    reference := "Solanalib.Specs.SolanaAccountView.Ref.release_model"
    decidesRequires := ["Solanalib.Specs.SolanaAccountView.Ref.release_model"]
    decides := ["Solanalib.Specs.SolanaAccountView.Ref.release_model"]
    check := releaseCheck refReleasePre (Ref.release_model
      AccountView.sliceProfile)
      ref_release_evaluated },
  { function := s!"<{refType "RefMut"} as core::ops::drop::Drop>::drop"
    generics := [("T", t)]
    reference := "Solanalib.Specs.SolanaAccountView.RefMut.release_model"
    decidesRequires := ["Solanalib.Specs.SolanaAccountView.RefMut.release_model"]
    decides := ["Solanalib.Specs.SolanaAccountView.RefMut.release_model"]
    check := releaseCheck refMutReleasePre (RefMut.release_model
      AccountView.sliceProfile)
      ref_mut_release_evaluated }]

/-- The `try_map` precondition at a scripted callback, decided through
`tryMap_requires_iff`; the report names the failing part. -/
def tryMapPre (mode : Mode) (req : Script → World → Guard → Prop)
    (equiv : ∀ script before guard, req script before guard ↔ tryMapReadyB mode script before guard)
    (script : Script) : Pre World Guard where
  requires := req script
  dec := fun before guard => decidable_of_iff _ (equiv script before guard).symm
  says := fun before guard =>
    match before.1.resolve guard with
    | none => "the guard is not live"
    | some slot => match before.1.lookupCell slot.cell with
      | none => "the account referenced by the guard is missing"
      | some _ => if slot.mode = mode then "the scripted callback is not CallbackSafe"
          else "the guard mode does not match the family mode"

def tryMapCheckers : List Checker := ["[u8]", "u8"].flatMap fun u => [
  { function := "solana_account_view::Ref::<'a, T>::try_map"
    generics := [("T", "[u8]"), ("U", u), ("E", "u8")]
    reference := "Solanalib.Specs.SolanaAccountView.Ref.try_map_model"
    decidesRequires := ["Solanalib.Specs.SolanaAccountView.Ref.try_map_model"]
    decides := ["Solanalib.Specs.SolanaAccountView.Ref.try_map_model"]
    check := decideTryMap false (u == "u8") (tryMapPre .shared
        (fun script before guard =>
          (Ref.try_map_contract.contract mapProfile).requires
            before
            ⟨guard, scriptCallback script⟩)
        (fun script before guard => tryMap_requires_iff .shared script before guard))
      (fun script before guard o =>
        Ref.try_map_model mapProfile before ⟨guard,
          scriptCallback script⟩ o)
      ref_try_map_evaluated },
  { function := "solana_account_view::RefMut::<'a, T>::try_map"
    generics := [("T", "[u8]"), ("U", u), ("E", "u8")]
    reference := "Solanalib.Specs.SolanaAccountView.RefMut.try_map_model"
    decidesRequires := ["Solanalib.Specs.SolanaAccountView.RefMut.try_map_model"]
    decides := ["Solanalib.Specs.SolanaAccountView.RefMut.try_map_model"]
    check := decideTryMap true (u == "u8") (tryMapPre .exclusive
        (fun script before guard =>
          (RefMut.try_map_contract.contract mapProfile).requires
            before
            ⟨guard, scriptCallback script⟩)
        (fun script before guard => tryMap_requires_iff .exclusive script before guard))
      (fun script before guard o =>
        RefMut.try_map_model mapProfile before ⟨guard,
          scriptCallback script⟩ o)
      ref_mut_try_map_evaluated }]

def checkers : List Checker :=
  [addressChecker, closeChecker, dataLenChecker, isSignerChecker, lamportsChecker, ownedByChecker,
    setLamportsChecker, tryBorrowChecker, tryBorrowMutChecker] ++ derefCheckers ++ tryMapCheckers

/-! ## Negative theorems for the preconditions no parseable record can break

The reader makes every handle the position of a parsed account and rejects
`set_lamports` values of 2^64 and more, so no record can leave `HasAccount` or
the bound of the observation setter. These kernel-checked evaluations show that the deciders of the
checkers reject such inputs. -/

/-- A pool without cells: handle ⟨0⟩ names no account. -/
def emptyPool : PoolState := ⟨[], []⟩

theorem close_pre_rejects_missing : @decide _ (closePre.dec emptyPool ⟨0⟩) = false := rfl
theorem data_len_pre_rejects_missing : @decide _ (dataLenPre.dec emptyPool ⟨0⟩) = false := rfl
theorem is_signer_pre_rejects_missing : @decide _ (isSignerPre.dec emptyPool ⟨0⟩) = false := rfl
theorem lamports_pre_rejects_missing : @decide _ (lamportsPre.dec emptyPool ⟨0⟩) = false := rfl
theorem owned_by_pre_rejects_missing :
    @decide _ (ownedByPre.dec emptyPool (⟨0⟩, Solanalib.Runtime.Pubkey.zero)) = false := rfl
theorem set_lamports_pre_rejects_missing : @decide _ (setLamportsPre.dec emptyPool (⟨0⟩, 0)) =
  false := rfl
theorem obs_set_lamports_pre_rejects_2_64 :
    @decide _ (obsSetLamportsPre.dec (AccountView.observe emptyPool ⟨0⟩)
      Solanalib.Runtime.U64_LIMIT) = false := rfl

def corpora : List (String × List Checker) := [("solana_account_view_2_0_0", checkers)]

end SolanalibTest.Conformance.Library.Families.AccountsV2
