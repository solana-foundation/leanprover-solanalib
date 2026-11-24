/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV1.Common
import SolanalibTest.Conformance.Library.Families.AccountsV1.Requires
import Solanalib.Specs.SolanaAccountView

/-!
# solana-account-view 1.0.0 checkers

Corpus `solana_account_view` (and `_forged`), written by
`rust/accounts-v1/src/view.rs` over input regions that the `entrypoint::deserialize` of pinocchio
0.10.2 turns into AccountViews.

**Projection.** The model state `Borrow.State Account Slice` is read from the
record as follows.

* Cell `k` is the `k`-th non-duplicate account of the region; a duplicate
  AccountView (pinocchio clones the original) denotes the same handle. The `Account` of the
  cell is its RuntimeAccount header (`is_signer`, `is_writable`,
  `executable` as nonzero bytes, `resize_delta`, `address`, `owner`,
  `lamports`, `data_len`) and `backing`, the allocated data area (entry
  length plus the 10 KiB realloc reserve). Its policy is `Policy.accountView`.
* Slot `i` is the guard object `i` of the driver (creation order; a map keeps the
  identity), live while the driver holds it, with the cell of its `state`
  pointer, the mode of its type and the range of its `value` pointer.
* Ghost components come from the state before (`ghost`): entry lengths,
  owner epochs, the slot count and the generations. The state after is
  compared without them.
* The borrow byte is not a model field: it must equal the lease
  observation of the model (`255` free, `255 - n` for `n` shared, `0` exclusive) in both
  states. The argument of an unwinding `Ref::map` returns no object while the
  model keeps its lease (`retainLease`); the checker excuses exactly that slot
  from having an object (it shows only in the borrow byte). Every other live
  model slot must be held by a recorded guard object.

Results: an `AddressRef`/`OwnerRef` is the header field its native reference
addresses (and its current bytes), a `DataRef` is the cell and range its native
reference addresses, its bytes (`DataRef.read`) and its mutability (its type),
a `Guard` is the identity under which the driver stores the returned object.
-/

set_option autoImplicit false

open Lean (Json)

open Solanalib.Specs.SolanaAccountView

namespace SolanalibTest.Conformance.Library.Families.AccountsV1.View

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView
open SolanalibTest.Conformance.Library.Families.AccountsV1

abbrev State := Solanalib.Specs.Core.AccountView.State

/-! ## Native state -/

structure NativeAccount where
  borrowState : Nat
  signer : Nat
  writable : Nat
  executable : Nat
  resizeDelta : Int
  address : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  lamports : Nat
  dataLen : Nat
  backing : Solanalib.Runtime.Bytes

structure Native where
  accounts : List NativeAccount
  guards : List (GuardEntry Slice)
  /-- The region outside the headers of the cells and allocated data areas. -/
  frame : Solanalib.Runtime.Bytes

def sliceOf (j : Json) : Result Slice := do pure ⟨← natField j "offset", ← natField j
  "length"⟩

def sliceJson (v : Slice) : Json := Json.mkObj [("offset", v.offset), ("length", v.length)]

def accountOf (j : Json) : Result NativeAccount := do
  return {
    borrowState := ← asUInt 8 (← field j "borrow_state")
    signer := ← asUInt 8 (← field j "is_signer")
    writable := ← asUInt 8 (← field j "is_writable")
    executable := ← asUInt 8 (← field j "executable")
    resizeDelta := ← asSInt 32 (← field j "resize_delta")
    address := ← pubkeyOf (← field j "address")
    owner := ← pubkeyOf (← field j "owner")
    lamports := ← asUInt 64 (← field j "lamports")
    dataLen := ← asUInt 64 (← field j "data_len")
    backing := ← asBytes (← field j "backing") }

def nativeOf (j : Json) : Result Native := do
  let accounts ← (← arrField j "accounts").mapM accountOf
  let guards ← guardsOf sliceOf j
  return ⟨accounts, guards, ← asBytes (← field j "frame")⟩

/-- The native borrow byte of a lease. -/
def borrowByte : Solanalib.Runtime.Lease → Nat
  | .free => 255
  | .shared n => 255 - n
  | .exclusive => 0

def flag (b : Nat) : Bool := b != 0

def accountFits (n : NativeAccount) (a : Account) : Bool :=
  decide (n.resizeDelta = a.resizeDelta ∧ n.address = a.metadata.address ∧ n.owner = a.owner ∧
    n.lamports = a.lamports ∧ n.dataLen = a.dataLen ∧ n.backing = a.backing ∧
    flag n.signer = a.metadata.signer ∧ flag n.writable = a.metadata.writable ∧
    flag n.executable = a.metadata.executable)

/-- The native borrow byte of every cell is the lease observation of the model. -/
def borrowFits (n : Native) (s : State) : Bool :=
  n.accounts.zipIdx.all fun (a, k) => a.borrowState == borrowByte (s.lease ⟨k⟩)

/-- The recorded native state is the projection of the model state; `consumed`
are the slots the call keeps leased without an object (derived from the call). -/
def stateFitsExcept (consumed : List Nat) (n : Native) (s : State) : Bool :=
  n.accounts.length == s.cells.length &&
  (n.accounts.zip s.cells).all (fun (a, c) => accountFits a c.value) &&
  borrowFits n s && guardsMatch n.guards consumed s

/-- The recorded native state is the projection of the model state, every live
slot held by a recorded guard object. -/
def stateFits (n : Native) (s : State) : Bool := stateFitsExcept [] n s

/-- A call keeps what the projection does not show: the frame, and the raw
flag bytes (the model sees only whether they are nonzero). -/
def frameKept (before after : Native) : Bool :=
  decide (before.frame = after.frame) &&
  (before.accounts.zip after.accounts).all fun (a, b) =>
    a.signer == b.signer && a.writable == b.writable && a.executable == b.executable

def accountJson (s : State) (k : Nat) (a : Account) : Json := Json.mkObj [
  ("borrow_state", borrowByte (s.lease ⟨k⟩)),
  ("is_signer", a.metadata.signer), ("is_writable", a.metadata.writable),
  ("executable", a.metadata.executable), ("resize_delta", a.resizeDelta),
  ("address", pubkeyJson a.metadata.address), ("owner", pubkeyJson a.owner),
  ("lamports", a.lamports), ("data_len", a.dataLen), ("backing", bytesJson a.backing),
  ("entry_len", a.entryLen), ("owner_epoch", a.ownerEpoch)]

def stateJson (s : State) : Json := Json.mkObj [
  ("accounts", Json.arr (s.cells.zipIdx.map fun (c, k) => accountJson s k c.value).toArray),
  ("guards", liveSlotsJson sliceJson s)]

/-- The model account of a recorded cell, with its ghost entry length and owner epoch. -/
def accountValue (a : NativeAccount) (entryLen ownerEpoch : Nat) : Account :=
  ⟨⟨a.address, flag a.signer, flag a.writable, flag a.executable⟩, a.owner, a.lamports, a.dataLen,
    entryLen, a.backing, a.resizeDelta, ownerEpoch⟩

/-- The state before: native state, ghost bookkeeping and their model state. -/
structure Before where
  native : Native
  state : State

def natList (j : Json) (k : String) : Result (List Nat) := do (← arrField j k).mapM (·.getNat?)

def beforeOf (j : Json) : Result Before := do
  let n ← nativeOf j
  let g ← field j "ghost"
  let entry ← natList g "entry_len"
  let epoch ← natList g "owner_epoch"
  unless entry.length = n.accounts.length ∧ epoch.length = n.accounts.length do
    throw "ghost entry lengths and epochs must be given per account"
  let cells := (n.accounts.zip (entry.zip epoch)).map fun (a, e, o) =>
    (⟨accountValue a e o, Borrow.Policy.accountView⟩ : Borrow.Cell Account)
  let slots ← slotsOf n.guards (← natField g "slots") (← natList g "generations")
  let s : State := ⟨cells, slots⟩
  unless n.guards.all (fun x => x.cell < cells.length) do throw "guard on an unknown cell"
  unless borrowFits n s do throw "borrow bytes disagree with the guards held before the \
    call"
  return ⟨n, s⟩

/-- The handle argument. Whether it names a cell is the precondition of the members
(`HasAccount`), which their checkers decide. -/
def handleArg (_ : Before) (args : Json) : Result Handle := do
  return ⟨← natField args "handle"⟩

/-! ## Outcomes -/

def renderOutcome {S V : Type} (value : V → Json) (state : S → Json) : Outcome S V String Empty →
  Json
  | .returned v s => Json.mkObj [("exit", "returned"), ("result", value v), ("state", state s)]
  | .unwound r s => Json.mkObj [("exit", "unwound"), ("reason", r), ("state", state s)]
  | .terminated r => nomatch r

def renderReturns {S V : Type} (value : V → Json) (state : S → Json) : Outcome S V Empty Empty →
  Json
  | .returned v s => Json.mkObj [("exit", "returned"), ("result", value v), ("state", state s)]
  | .unwound r _ => nomatch r
  | .terminated r => nomatch r

def errorOf (s : String) : Result AccountView.Error :=
  match s with
  | "AccountBorrowFailed" => pure .accountBorrowFailed
  | "InvalidRealloc" => pure .invalidRealloc
  | other => throw s!"unknown AccountView error {other}"

def errorJson : AccountView.Error → Json
  | .accountBorrowFailed => "AccountBorrowFailed"
  | .invalidRealloc => "InvalidRealloc"

/-- `{"ok": v}` or `{"err": "AccountBorrowFailed" | "InvalidRealloc"}`. -/
def resultOf {α : Type} (value : Json → Result α) (j : Json) : Result (Except AccountView.Error α)
  :=
  asExcept (fun e => do errorOf (← e.getStr?)) value j

/-! ## AccountView methods: total references, decided through their graph -/

/-- Whether a corpus may hold inputs outside the registered precondition of a member. -/
inductive Domain where
  /-- Every record satisfies the precondition (inputs the loader and the library produce). -/
  | precondition
  /-- Forged headers: a record outside the precondition must show the documented native behavior of
  the member there (`outside`), and is then classified as
  outside the precondition, where the contract claims nothing. -/
  | forged

/-- The documented native behavior of a member outside its precondition: the
panic reason of the input, or `none` if none is documented. -/
abbrev Outside (A : Type) := Before → A → Option String

def noOutside {A : Type} : Outside A := fun _ _ => none

/-- Decide the registered precondition of a member (`requires`) and, inside it,
`returnsOf model` (the registered reference is the function `model`) up to the
ghost components of the state after. A main-corpus record outside the
precondition is a FAIL. A forged record outside it must unwind with its
documented reason and leave the state as before (the panic precedes every
write); it is then admitted as outside the precondition. -/
def methodCheck {A V RV : Type} (contract : Solanalib.Contracts.Model State A V)
    (pre : ∀ s a, Decidable (contract.requires s a))
    (model : State → A → V × State) (args : Before → Json → Result A)
    (value : Json → Result RV) (valueFits : RV → V → State → Bool) (render : V → Json)
    (outside : Outside A) (domain : Domain) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state
  let a ← args b c.args
  let recorded ← parseRecorded value nativeOf c.outcome
  if @decide (contract.requires b.state a) (pre b.state a) then
    let fits := matchOutcome (U := Empty) (T := Empty) valueFits
      (fun n s => stateFits n s && frameKept b.native n) noMatch noMatch recorded
    return admits (returnsOf model b.state a) _ (returnsOf_graph model b.state a) fits
      (renderReturns render stateJson)
  else
    match domain, recorded, outside b a with
    | .precondition, _, _ => throw "the input is outside the registered precondition"
    | .forged, .unwound reason n, some expected =>
      unless reason == expected do
        throw
          s!"outside the precondition: unwind reason {reason.quote}, documented \
            {expected.quote}"
      unless stateFits n b.state && frameKept b.native n do
        throw "outside the precondition: the documented panic leaves the state as before"
      return ⟨true, Json.mkObj [("outside_precondition", Json.str expected)]⟩
    | .forged, _, _ => throw "outside the precondition, without its documented native \
      behavior"

def method {A V RV : Type} (function reference : String) (contract : Solanalib.Contracts.Model
  State A V)
    (pre : ∀ s a, Decidable (contract.requires s a)) (model : State → A → V × State)
    (args : Before → Json → Result A) (value : Json → Result RV) (valueFits : RV → V → State → Bool)
    (render : V → Json) (domain : Domain) (outside : Outside A := noOutside) : Checker where
  function := function
  generics := []
  reference := reference
  check := methodCheck contract pre model args value valueFits render outside domain
  decides := [reference]
  decidesRequires := [reference]

/-- Cell presence, as the observation and update contracts require it. -/
instance hasAccountDecidable (s : State) (h : Handle) : Decidable (s.HasAccount h) :=
  match hc : s.lookupCell h with
  | some c => isTrue ⟨c, hc⟩
  | none => isFalse fun ⟨_, hc'⟩ => by rw [hc] at hc'; cases hc'

/-! The `i32` arithmetic of the source of `resize` and `close` (solana-account-view 1.0.0
`resize_unchecked`, `close`) panics in a dev build exactly where the registered preconditions
(`ResizeArithmetic`, `CloseArithmetic`) fail on a header whose length fits `i32`: the addition
`resize_delta + (new_len - data_len)` and the subtraction `resize_delta - data_len` overflow. -/

def resizeOutside : Outside (Handle × Nat) := fun b (h, _) =>
  if (b.state.account h).dataLen ≤ I32_MAX then some "attempt to add with overflow" else none

def closeOutside : Outside Handle := fun b h =>
  if (b.state.account h).dataLen ≤ I32_MAX then some "attempt to subtract with overflow" else none

def natValue (j : Json) : Result Nat := j.getNat?
def boolValue (j : Json) : Result Bool := j.getBool?

/-- A native reference to a header field: its cell, the offset of the field in the header and its
bytes.
-/
structure FieldRef where
  cell : Nat
  field : Nat
  bytes : Solanalib.Runtime.Bytes

def fieldRefOf (j : Json) : Result FieldRef := do
  pure ⟨← natField j "cell", ← natField j "field", ← asBytes (← field j "bytes")⟩

def handleJson (h : Handle) : Json := Json.mkObj [("cell", h.cell)]

namespace V1
open AccountView.Pool

def present {A V : Type} {c : Solanalib.Contracts.Model State A V} (key : A → Handle)
    (same : ∀ s a, c.requires s a = s.HasAccount (key a)) : ∀ s a, Decidable (c.requires s a) :=
  fun s a => by rw [same]; infer_instance

def always {A V : Type} {c : Solanalib.Contracts.Model State A V} (same : ∀ s a, c.requires s a =
  True) :
    ∀ s a, Decidable (c.requires s a) :=
  fun s a => by rw [same]; infer_instance

def observe (function reference : String) (contract : Solanalib.Contracts.Model State Handle Nat)
    (same : ∀ s a, contract.requires s a = s.HasAccount a) (model : State → Handle → Nat × State)
    (domain : Domain) : Checker :=
  method function reference contract (present id same) model handleArg natValue (fun r v _ => r ==
    v)
    (fun v => v) domain

def observeBool (function reference : String) (contract : Solanalib.Contracts.Model State Handle
  Bool)
    (same : ∀ s a, contract.requires s a = s.HasAccount a) (model : State → Handle → Bool × State)
    (domain : Domain) : Checker :=
  method function reference contract (present id same) model handleArg boolValue (fun r v _ => r ==
    v)
    (fun v => v) domain

def resizeRequires : ∀ s a, Decidable
  (AccountView.Pool.resize_contract.requires s a) :=
  fun s a => inferInstanceAs (Decidable (s.HasAccount a.1 ∧ ResizeArithmetic s a))

def closeRequires : ∀ s a, Decidable
  (AccountView.Pool.close_with_resize_delta_contract.requires s
  a) :=
  fun s a => inferInstanceAs (Decidable (s.HasAccount a ∧ CloseArithmetic .v1 s a))

def checkers (domain : Domain) : List Checker := [
  observe "solana_account_view::AccountView::lamports"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_model"
      AccountView.Pool.lamports_contract (fun _ _ => rfl)
      lamports_model domain,
  observe "solana_account_view::AccountView::data_len"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.data_len_model"
      AccountView.Pool.data_len_contract (fun _ _ => rfl)
      data_len_model domain,
  observeBool "solana_account_view::AccountView::is_data_empty"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_data_empty_model"
      AccountView.Pool.is_data_empty_contract (fun _ _ => rfl)
      is_data_empty_model domain,
  observeBool "solana_account_view::AccountView::is_signer"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_signer_model"
      AccountView.Pool.is_signer_contract (fun _ _ => rfl)
      is_signer_model domain,
  observeBool "solana_account_view::AccountView::is_writable"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_writable_model"
      AccountView.Pool.is_writable_contract (fun _ _ => rfl)
      is_writable_model domain,
  method "<solana_account_view::AccountView as core::clone::Clone>::clone"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.clone_model"
      AccountView.Pool.clone_contract (always fun _ _ => rfl)
    clone_model handleArg (fun j => natField j "cell") (fun r h _ => r == h.cell) handleJson domain,
  -- The returned `&Address` addresses the address field (offset 8) of the cell.
  method "solana_account_view::AccountView::address"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.address_model"
      AccountView.Pool.address_contract (always fun _ _ => rfl)
    address_model handleArg fieldRefOf
    (fun r v s => r.cell == v.account.cell && r.field == 8 && decide (r.bytes = (v.value s).bytes))
    (fun v => handleJson v.account) domain,
  -- The returned `&Address` addresses the owner field (offset 40); the epoch is ghost.
  method "solana_account_view::AccountView::owner"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.owner_model"
      AccountView.Pool.owner_contract (always fun _ _ => rfl)
    owner_model handleArg fieldRefOf
    (fun r v s => r.cell == v.account.cell && r.field == 40 && decide (r.bytes = (v.value s).bytes))
    (fun v => Json.mkObj [("cell", v.account.cell), ("epoch", v.epoch)]) domain,
  method "solana_account_view::AccountView::owned_by"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_model"
      AccountView.Pool.owned_by_contract
    (present Prod.fst fun _ _ => rfl) owned_by_model
    (fun b j => do return (← handleArg b j, ← pubkeyOf (← field j "program")))
    boolValue (fun r v _ => r == v) (fun v => v) domain,
  method "solana_account_view::AccountView::set_lamports"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_model"
      AccountView.Pool.set_lamports_contract
    (present Prod.fst fun _ _ => rfl) set_lamports_model
    (fun b j => do return (← handleArg b j, ← asUInt 64 (← field j "lamports")))
    asUnit (fun _ _ _ => true) (fun _ => Json.null) domain,
  method "solana_account_view::AccountView::try_borrow"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model"
      AccountView.Pool.try_borrow_contract (always fun _ _ => rfl)
    try_borrow_model handleArg
    (resultOf (fun j => natField j "guard"))
    (fun r v _ => match r, v with
      | .ok id, .ok g => id == g.id
      | .error e, .error e' => decide (e = e')
      | _, _ => false)
    (exceptJson errorJson fun g => Json.mkObj [("guard", g.id), ("generation", g.generation)])
      domain,
  method "solana_account_view::AccountView::try_borrow_mut"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_mut_model"
      AccountView.Pool.try_borrow_mut_contract (always fun _ _ =>
      rfl)
    try_borrow_mut_model handleArg
    (resultOf (fun j => natField j "guard"))
    (fun r v _ => match r, v with
      | .ok id, .ok g => id == g.id
      | .error e, .error e' => decide (e = e')
      | _, _ => false)
    (exceptJson errorJson fun g => Json.mkObj [("guard", g.id), ("generation", g.generation)])
      domain,
  method "solana_account_view::AccountView::resize"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model"
      AccountView.Pool.resize_contract resizeRequires resize_model
    (fun b j => do return (← handleArg b j, ← natField j "new_len"))
    (resultOf asUnit) (fun r v _ => decide (r = v)) (exceptJson errorJson fun _ => Json.null)
    domain resizeOutside,
  method "solana_account_view::AccountView::close"
    "Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_model"
      AccountView.Pool.close_with_resize_delta_contract
      closeRequires close_with_resize_delta_model
    handleArg (resultOf asUnit) (fun r v _ => decide (r = v)) (exceptJson errorJson fun _ =>
      Json.null)
    domain closeOutside
]

end V1

/-! ## Guards: families at the byte-range index `sliceProfile` -/

abbrev World := State × Unit

/-- The guard argument: the object of the driver `id`, the current token of the slot.
A dead identity gives a token that resolves to nothing; whether the guard is
live is the release and map precondition, which their checkers decide. -/
def guardArg (b : Before) (args : Json) : Result Guard := do
  let id ← natField args "guard"
  match b.state.lookupSlot id with
  | some slot => pure ⟨id, slot.generation⟩
  | none => pure ⟨id, 0⟩

def worldJson (w : World) : Json := stateJson w.1

/-- The dereference families are graphs of total functions, by definition. -/
theorem ref_deref_evaluated : Ref.deref_model sliceProfile =
    returnsOf (Unwind := Empty) (Terminal := Empty)
      (fun (before : World) (guard : Guard) => ((⟨guard, false⟩ : DataRef), before)) := rfl

theorem refmut_deref_mut_evaluated : RefMut.deref_mut_model
  sliceProfile =
    returnsOf (Unwind := Empty) (Terminal := Empty)
      (fun (before : World) (guard : Guard) => ((⟨guard, true⟩ : DataRef), before)) := rfl

/-- The release families perform the `release` of the registry, by definition. -/
theorem ref_release_evaluated : Ref.release_model sliceProfile =
    returnsOf (Unwind := Empty) (Terminal := Empty)
      (fun (before : World) (guard : Guard) => ((), ((Borrow.release before.1 guard).2, before.2)))
        := rfl

theorem refmut_release_evaluated : RefMut.release_model
  sliceProfile =
    returnsOf (Unwind := Empty) (Terminal := Empty)
      (fun (before : World) (guard : Guard) => ((), ((Borrow.release before.1 guard).2, before.2)))
        := rfl

/-- A native reference returned by a dereference. -/
structure NativeRef where
  cell : Nat
  view : Slice
  bytes : Solanalib.Runtime.Bytes
  writable : Bool

def nativeRefOf (j : Json) : Result NativeRef := do
  pure ⟨← natField j "cell", ← sliceOf (← field j "view"), ← asBytes (← field j "bytes"),
    ← boolField j "writable"⟩

/-- The native reference denotes the `DataRef`: the current target of its guard,
the bytes `DataRef.read` gives and its mutability. -/
def dataRefFits (r : NativeRef) (d : DataRef) (w : World) : Bool :=
  r.writable == d.writable &&
  match w.1.resolve d.guard with
  | some slot => decide (slot.cell = ⟨r.cell⟩ ∧ slot.view = r.view ∧ d.read w.1 = .ok r.bytes)
  | none => false

def dataRefJson (d : DataRef) : Json :=
  Json.mkObj [("guard", d.guard.id), ("generation", d.guard.generation), ("writable", d.writable)]

def guardCheck {V RV : Type} (contract : Solanalib.Contracts.Model World Guard V)
    (pre : ∀ w g, Decidable (contract.requires w g))
    (relation : World → Guard → Outcome World V Empty Empty → Prop)
    (model : World → Guard → V × World) (evaluated : relation = returnsOf model)
    (value : Json → Result RV) (valueFits : RV → V → World → Bool) (render : V → Json)
    (c : Case) : Result Verdict := do
  let b ← beforeOf c.state
  let g ← guardArg b c.args
  unless @decide (contract.requires (b.state, ()) g) (pre (b.state, ()) g) do
    throw "the input is outside the registered precondition"
  let recorded ← parseRecorded value nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty) valueFits
    (fun n w => stateFits n w.1 && frameKept b.native n) noMatch noMatch recorded
  return admits (relation (b.state, ()) g) _
    (fun o => by rw [evaluated]; exact returnsOf_graph model (b.state, ()) g o) fits
    (renderReturns render worldJson)

/-- Dereference requires nothing; release requires a live guard. -/
def derefPre (contract : Solanalib.Contracts.Model World Guard DataRef)
    (same : ∀ w g, contract.requires w g = True) : ∀ w g, Decidable (contract.requires w g) :=
  fun w g => by rw [same]; infer_instance

def releasePre (contract : Solanalib.Contracts.Model World Guard Unit)
    (same : ∀ w g, contract.requires w g = ∃ slot, w.1.resolve g = some slot) :
    ∀ w g, Decidable (contract.requires w g) :=
  fun w g => by rw [same]; infer_instance

def generic (t : String) : List (String × String) := [("T", t)]

def derefChecker (t : String) : Checker where
  function := "<solana_account_view::Ref<'_, T> as core::ops::deref::Deref>::deref"
  generics := generic t
  reference := "Solanalib.Specs.SolanaAccountView.Ref.deref_model"
  check := guardCheck (Ref.deref_contract.contract sliceProfile)
    (derefPre _ fun _ _ => rfl) (Ref.deref_model sliceProfile) _
    ref_deref_evaluated nativeRefOf dataRefFits dataRefJson
  decides := ["Solanalib.Specs.SolanaAccountView.Ref.deref_model"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountView.Ref.deref_model"]

def derefMutChecker (t : String) : Checker where
  function := "<solana_account_view::RefMut<'_, T> as \
    core::ops::deref::DerefMut>::deref_mut"
  generics := generic t
  reference := "Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_model"
  check := guardCheck (RefMut.deref_mut_contract.contract
    sliceProfile)
    (derefPre _ fun _ _ => rfl) (RefMut.deref_mut_model
      sliceProfile) _
    refmut_deref_mut_evaluated nativeRefOf dataRefFits dataRefJson
  decides := ["Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_model"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_model"]

def releaseChecker (t : String) : Checker where
  function := "<solana_account_view::Ref<'_, T> as core::ops::drop::Drop>::drop"
  generics := generic t
  reference := "Solanalib.Specs.SolanaAccountView.Ref.release_model"
  check := guardCheck (Ref.release_contract.contract sliceProfile)
    (releasePre _ fun _ _ => rfl) (Ref.release_model
      sliceProfile) _
    ref_release_evaluated asUnit (fun _ _ _ => true) (fun _ => Json.null)
  decides := ["Solanalib.Specs.SolanaAccountView.Ref.release_model"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountView.Ref.release_model"]

def releaseMutChecker (t : String) : Checker where
  function := "<solana_account_view::RefMut<'_, T> as core::ops::drop::Drop>::drop"
  generics := generic t
  reference := "Solanalib.Specs.SolanaAccountView.RefMut.release_model"
  check := guardCheck (RefMut.release_contract.contract
    sliceProfile)
    (releasePre _ fun _ _ => rfl) (RefMut.release_model
      sliceProfile) _
    refmut_release_evaluated asUnit (fun _ _ _ => true) (fun _ => Json.null)
  decides := ["Solanalib.Specs.SolanaAccountView.RefMut.release_model"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountView.RefMut.release_model"]

/-! ## `Ref::map` over a scripted closure -/

/-- The callback relation of a closure given as a function. -/
def fnCallback (profile : MapProfile)
    (f : profile.target.World → Handle → profile.target.View →
      Outcome profile.target.World (Except Empty profile.target.View) profile.Unwind
        profile.Terminal) :
    Borrow.MapCallback Account profile.target.View profile.target.Aux Empty profile.Unwind
      profile.Terminal :=
  fun w h v o => f w h v = o

/-- The source outcome embedded by `protocolOutcome ∘ mapOutcome`, if any. -/
def unprotocol {W U T : Type} : Outcome W (Borrow.TryMapResult Empty) U T → Option (Outcome W Guard
  U T)
  | .returned (.ok (.ok g)) s => some (.returned g s)
  | .returned (.ok (.error (e, _))) _ => nomatch e
  | .returned (.error _) _ => none
  | .unwound r s => some (.unwound r s)
  | .terminated r => some (.terminated r)

theorem protocol_map_iff (profile : MapProfile)
    (o : Outcome profile.target.World Guard profile.Unwind profile.Terminal)
    (p : Outcome profile.target.World (Borrow.TryMapResult Empty) profile.Unwind profile.Terminal) :
    protocolOutcome profile.fallible (mapOutcome profile o) = p ↔ unprotocol p = some o := by
  constructor
  · rintro rfl
    cases o <;> rfl
  · intro h
    rcases p with ⟨r, s'⟩ | ⟨r, s'⟩ | r
    · rcases r with e | (⟨e, _⟩ | g')
      · simp [unprotocol] at h
      · exact e.elim
      · simp only [unprotocol, Option.some.injEq] at h
        subst h
        rfl
    · simp only [unprotocol, Option.some.injEq] at h
      subst h
      rfl
    · simp only [unprotocol, Option.some.injEq] at h
      subst h
      rfl

/-- The outcome of the map reference with a function callback: the finished
callback outcome at a live guard, none otherwise. -/
def mapComputed (profile : MapProfile)
    (f : profile.target.World → Handle → profile.target.View →
      Outcome profile.target.World (Except Empty profile.target.View) profile.Unwind
        profile.Terminal)
    (before : profile.target.World) (guard : Guard) :
    Option (Outcome profile.target.World Guard profile.Unwind profile.Terminal) :=
  match before.1.resolve guard with
  | none => none
  | some slot => match before.1.lookupCell slot.cell with
    | none => none
    | some _ => unprotocol (Borrow.finishTryMap .retainLease guard slot.view (f before slot.cell
      slot.view))

/-- The registered `Ref::map` reference, at a function callback, is the graph of `mapComputed`. -/
theorem map_evaluated (profile : MapProfile)
    (f : profile.target.World → Handle → profile.target.View →
      Outcome profile.target.World (Except Empty profile.target.View) profile.Unwind
        profile.Terminal)
    (before : profile.target.World) (guard : Guard)
    (o : Outcome profile.target.World Guard profile.Unwind profile.Terminal) :
    Ref.map_model profile before ⟨guard, fnCallback profile f⟩ o ↔
      mapComputed profile f before guard = some o := by
  show Borrow.tryMap .retainLease (fnCallback profile f) before guard
    (protocolOutcome profile.fallible (mapOutcome profile o)) ↔ _
  unfold Borrow.tryMap mapComputed
  cases h1 : before.1.resolve guard with
  | none =>
    dsimp only
    exact protocol_map_iff profile o _
  | some slot =>
    dsimp only
    cases h2 : before.1.lookupCell slot.cell with
    | none =>
      dsimp only
      exact protocol_map_iff profile o _
    | some cell =>
      dsimp only
      constructor
      · rintro ⟨p, hp, he⟩
        simp only [fnCallback] at hp
        subst hp
        exact (protocol_map_iff profile o _).mp he
      · intro h
        exact ⟨_, rfl, (protocol_map_iff profile o _).mpr h⟩

/-- The test index: byte-range targets, panic messages as unwind reasons, no terminal exit. -/
def mapProfile : MapProfile := ⟨sliceProfile, String, Empty⟩

/-- The script of the closure: `set_lamports` effects on cells, then a subrange of
its input (relative to the input range) or a panic. -/
inductive MapExit where
  | ret (offset length : Nat)
  | panic (message : String)

structure MapScript where
  effects : List (Nat × Nat)
  exit : MapExit

/-- The captured `set_lamports` calls of the closure, by the registered `set_lamports` model. -/
def applyEffects (effects : List (Nat × Nat)) (s : State) : State :=
  effects.foldl (fun s (h, v) =>
    (AccountView.Pool.set_lamports_model s (⟨h⟩, v)).2) s

def scriptRun (script : MapScript) (w : World) (_ : Handle) (v : Slice) :
    Outcome World (Except Empty Slice) String Empty :=
  let after : World := (applyEffects script.effects w.1, w.2)
  match script.exit with
  | .ret o l => .returned (.ok ⟨v.offset + o, l⟩) after
  | .panic m => .unwound m after

def scriptOf (j : Json) : Result MapScript := do
  let effects ← (← arrField j "effects").mapM fun e => do
    return (← natField e "handle", ← asUInt 64 (← field e "lamports"))
  let exit ← field j "exit"
  match exit.getObjVal? "return", exit.getObjVal? "panic" with
  | .ok r, .error _ => do
    let v ← sliceOf r
    return ⟨effects, .ret v.offset v.length⟩
  | .error _, .ok m => return ⟨effects, .panic (← m.getStr?)⟩
  | _, _ => throw s!"unknown closure exit {exit.compress}"

/-! ### The registered `Ref::map` precondition at a function callback

`genericTryMapContract` requires a live guard of the shared mode on an existing
cell, and `CallbackSafe`: every exit of the callback at that guard respects the
callback frame (`CallbackAdmissible`) and returns a valid target in a
well-formed pool (`CallbackValid`). With a function callback the exit is the value of the
function, so the quantifier over exits is one evaluation. -/

instance mapCallbackValidDecidable (handle : Handle) (original : Slice)
    (produced : Outcome World (Except Empty Slice) String Empty) :
    Decidable (mapProfile.fallible.CallbackValid handle original produced) :=
  match produced with
  | .returned (.ok mapped) after =>
    inferInstanceAs (Decidable (PoolWellFormed after.1 ∧
      ∃ cell, after.1.cells[handle.cell]? = some cell ∧ mapped.ValidFor cell.value))
  | .returned (.error e) _ => e.elim
  | .unwound _ after => inferInstanceAs (Decidable (PoolWellFormed after.1))
  | .terminated r => r.elim

theorem map_requires_iff (f : World → Handle → Slice → Outcome World (Except Empty Slice) String
  Empty)
    (before : World) (guard : Guard) :
    (Ref.map_contract.contract mapProfile).requires before
        ⟨guard, fnCallback mapProfile f⟩ ↔
      (∃ slot, before.1.resolve guard = some slot ∧
        ∃ cell, before.1.lookupCell slot.cell = some cell ∧ slot.mode = .shared) ∧
      (∀ slot, before.1.resolve guard = some slot → ∀ cell, before.1.lookupCell slot.cell = some
        cell →
        Borrow.CallbackAdmissible sliceFootprint before.1 guard (f before slot.cell slot.view) ∧
        mapProfile.fallible.CallbackValid slot.cell slot.view (f before slot.cell slot.view)) := by
  show ((∃ slot cell, before.1.resolve guard = some slot ∧ before.1.lookupCell slot.cell = some
    cell ∧
      slot.mode = .shared) ∧ mapProfile.fallible.CallbackSafe before ⟨guard, fnCallback mapProfile
        f⟩) ↔ _
  constructor
  · rintro ⟨⟨slot, cell, live, present, mode⟩, safe⟩
    refine ⟨⟨slot, live, cell, present, mode⟩, fun slot live cell present => ?_⟩
    exact safe slot cell live present _ rfl
  · rintro ⟨⟨slot, live, cell, present, mode⟩, safe⟩
    refine ⟨⟨slot, cell, live, present, mode⟩, fun slot cell live present produced called => ?_⟩
    change f before slot.cell slot.view = produced at called
    subst called
    exact safe slot live cell present

def mapPre (f : World → Handle → Slice → Outcome World (Except Empty Slice) String Empty)
    (before : World) (guard : Guard) :
    Decidable ((Ref.map_contract.contract mapProfile).requires
      before
      ⟨guard, fnCallback mapProfile f⟩) :=
  decidable_of_iff _ (map_requires_iff f before guard).symm

def mapCheck (c : Case) : Result Verdict := do
  let b ← beforeOf c.state
  let g ← guardArg b c.args
  let script ← scriptOf (← field c.args "callback")
  for (h, _) in script.effects do
    unless h < b.state.cells.length do throw s!"closure effect on unknown cell {h}"
  unless @decide _ (mapPre (scriptRun script) (b.state, ()) g) do
    throw "the input is outside the registered precondition"
  -- The native closure indexes its input (`&d[o..o + l]`, `&d[o]`): a target
  -- beyond the current range of the guard panics there, which the script does not
  -- describe, so such a record is outside the domain of the script.
  match script.exit, b.state.lookupSlot g.id with
  | .ret o l, some slot =>
    unless o + l ≤ slot.view.length do
      throw s!"the closure target {o}+{l} leaves its input of length {slot.view.length}"
  | _, _ => pure ()
  let recorded ← parseRecorded (fun j => natField j "guard") nativeOf c.outcome
  -- Only an unwinding map leaves the lease of its argument without an object.
  let fits := matchOutcomeBy (fun id (g' : Guard) _ => id == g'.id)
    (fun n (w : World) => stateFits n w.1 && frameKept b.native n)
    (fun n (w : World) => stateFitsExcept [g.id] n w.1 && frameKept b.native n)
    (fun r (r' : String) => r == r') noMatch recorded
  let f := scriptRun script
  return admits (Ref.map_model mapProfile (b.state, ()) ⟨g,
    fnCallback mapProfile f⟩)
    (mapComputed mapProfile f (b.state, ()) g) (map_evaluated mapProfile f (b.state, ()) g) fits
    (renderOutcome (fun (g' : Guard) => Json.mkObj [("guard", g'.id), ("generation",
      g'.generation)])
      worldJson)

def mapChecker (u : String) : Checker where
  function := "solana_account_view::Ref::<'a, T>::map"
  generics := [("T", "[u8]"), ("U", u), ("F", "scripted closure")]
  reference := "Solanalib.Specs.SolanaAccountView.Ref.map_model"
  check := mapCheck
  decides := ["Solanalib.Specs.SolanaAccountView.Ref.map_model"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountView.Ref.map_model"]

def checkers : List Checker :=
  V1.checkers .precondition ++
  ["[u8]", "u8"].map derefChecker ++ ["[u8]"].map derefMutChecker ++
  ["[u8]", "u8"].map releaseChecker ++ ["[u8]"].map releaseMutChecker ++
  ["[u8]", "u8"].map mapChecker

/-- The members recorded on forged headers. -/
def forgedCheckers : List Checker :=
  (V1.checkers .forged).filter fun c => [
    "solana_account_view::AccountView::resize", "solana_account_view::AccountView::close",
    "solana_account_view::AccountView::is_signer", "solana_account_view::AccountView::is_wr\
      itable",
    "solana_account_view::AccountView::set_lamports"].contains c.function

end SolanalibTest.Conformance.Library.Families.AccountsV1.View
