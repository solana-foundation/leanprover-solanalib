/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Values
import SolanalibTest.Conformance.Library.Runtime
import Solanalib.Specs.Core.AccountInfo

/-!
# AccountInfo worlds from loader input regions

The accounts of a record are a loader input (`rust/accounts`), deserialized by
solana-program-entrypoint 3.1.1 into `AccountInfo`s. The model world
(`AccountInfo.State`, cells and guard slots) is built from it: the `k`-th
distinct account has its lamports cell at `2k` and its data cell at `2k + 1`
(policy `refCell 64`), and owner reference `k`; a duplicate entry is the same
`AccountInfo` value as its first occurrence. Borrows the case holds across the
call (`"borrows"`) are live guard slots before the call.

After the call the driver reads the region back and probes the `RefCell` of each cell
(`try_borrow_mut`, `try_borrow`): free, shared or exclusive. Guard
identities and the slot history are ghost state; a model world is compared
through its cell contents and the lease of each cell (`observeCells`).
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor

open Solanalib.Contracts.Model Solanalib.Specs.Core SolanalibTest.Conformance.Library.Runtime

/-- The target binding of every native run: 64-bit `RefCell` counters, unwinding panics. -/
def profile : AccountInfo.Profile := ⟨64, false⟩

def policy : Borrow.Policy := profile.policy

/-- Indices (into the input entries) of the distinct accounts, in order. -/
def distinctOf : List InputEntry → List InputAccount
  | [] => []
  | .account a :: rest => a :: distinctOf rest
  | .duplicate _ :: rest => distinctOf rest

/-- The distinct-account number of each entry (duplicates resolve to their target). -/
def entryNumbers (entries : List InputEntry) : List (Option Nat) :=
  let step := fun (acc : List (Option Nat) × Nat) (e : InputEntry) =>
    match e with
    | .account _ => (acc.1 ++ [some acc.2], acc.2 + 1)
    | .duplicate i => (acc.1 ++ [acc.1.getD i none], acc.2)
  (entries.foldl step ([], 0)).1

def toPubkey (b : Solanalib.Runtime.Bytes) : Result Solanalib.Runtime.Pubkey :=
  if h : b.length = 32 then pure ⟨b, h⟩ else throw "address must have 32 bytes"

/-- The `AccountInfo` value of input entry `i`. solana-program-entrypoint
3.1.1 does not deserialize the rent epoch: `AccountInfo::new` sets the
deprecated field to 0. -/
def infoAt (input : LoaderInput) (i : Nat) : Result AccountInfo.Value := do
  let some (some k) := (entryNumbers input.entries)[i]? | throw s!"no account entry {i}"
  let some a := (distinctOf input.entries)[k]? | throw s!"no account {k}"
  pure ⟨← toPubkey a.key, ⟨2 * k⟩, ⟨2 * k + 1⟩, ← toPubkey a.owner, 0,
    a.isSigner, a.isWritable, a.executable, ⟨k⟩⟩

def asMode (j : Json) : Result Borrow.Mode := do
  match ← j.getStr? with
  | "shared" => pure .shared
  | "exclusive" => pure .exclusive
  | other => throw s!"unknown borrow mode {other}"

/-- The model world before the call. -/
def worldOf (input : LoaderInput) (borrows : List (Nat × Borrow.Mode)) : AccountInfo.State :=
  ⟨(distinctOf input.entries).flatMap fun a =>
      [⟨.lamports (UInt64.ofNat a.lamports), policy⟩, ⟨.data a.data, policy⟩],
    borrows.map fun (cell, mode) => some ⟨⟨cell⟩, mode, 0, .whole⟩⟩

def asBorrows (j : Json) : Result (List (Nat × Borrow.Mode)) := do
  (← asArray j).mapM fun b => do pure (← natField b "cell", ← asMode (← field b "mode"))

/-- `{"input": ..., "borrows": [...]}`. -/
def asWorld (state : Json) : Result (LoaderInput × AccountInfo.State) := do
  let input ← loaderInput (← field state "input")
  let borrows ← match state.getObjVal? "borrows" with
    | .ok b => asBorrows b
    | .error _ => pure []
  pure (input, worldOf input borrows)

/-! ## Observation of worlds -/

inductive Lease where
  | free
  | shared
  | exclusive
  deriving DecidableEq, Repr

def asLease (j : Json) : Result Lease := do
  match ← j.getStr? with
  | "free" => pure .free
  | "shared" => pure .shared
  | "exclusive" => pure .exclusive
  | other => throw s!"unknown lease {other}"

def leaseJson : Lease → Json
  | .free => "free"
  | .shared => "shared"
  | .exclusive => "exclusive"

def leaseOf (state : AccountInfo.State) (cell : Nat) : Lease :=
  if state.exclusiveCount ⟨cell⟩ ≠ 0 then .exclusive
  else if state.sharedCount ⟨cell⟩ ≠ 0 then .shared
  else .free

/-- The contents and lease of each cell. -/
abbrev CellsObs := List (AccountInfo.Content × Lease)

def observeCells (state : AccountInfo.State) : CellsObs :=
  state.cells.zipIdx.map fun (cell, i) => (cell.value, leaseOf state i)

def contentJson : AccountInfo.Content → Json
  | .lamports v => tagged "lamports" (toJson v.toNat)
  | .data b => tagged "data" (bytesJson b)

def cellsJson (o : CellsObs) : Json :=
  listJson (fun (c, l) => Json.mkObj [("content", contentJson c), ("lease", leaseJson l)]) o

/-- The recorded cells after the call: the region read back and the probed leases. -/
def asCellsObs (state : Json) : Result CellsObs := do
  let r ← region (← field state "input")
  let leases ← asList asLease (← field state "leases")
  let contents := r.entries.flatMap fun
    | .account a => [AccountInfo.Content.lamports (UInt64.ofNat a.lamports), .data a.data]
    | .duplicate _ => []
  unless contents.length = leases.length do throw "one lease per cell expected"
  pure (contents.zip leases)

/-- The owners of the distinct accounts in the region read back. -/
def asOwnersAfter (state : Json) : Result (List Solanalib.Runtime.Pubkey) := do
  let r ← region (← field state "input")
  (r.entries.filterMap fun
    | .account a => some a.owner
    | .duplicate _ => none).mapM toPubkey

/-! ## The whole region after the call

A model world fixes the lamports, data and (through owner references) owner
of each distinct account. Every other part of the region is not represented
by the AccountInfo models and must be unchanged: the marker (255; AccountInfo
does not use the account-view borrow byte), the flag bytes, the padding word
(the original data length, written by the `deserialize` of solana-program-entrypoint 3.1.1 before
the call), key, rent epoch, the realloc reserve
(`spare_nonzero_at` null), duplicate markers, instruction data and program id. -/

structure WorldObs where
  region : Region
  leases : List Lease
  deriving DecidableEq

def inputOwners (input : LoaderInput) : List Solanalib.Runtime.Pubkey :=
  (distinctOf input.entries).map fun a => (toPubkey a.owner).toOption.getD .zero

def flagByte (b : Bool) : Nat := if b then 1 else 0

/-- The region and leases a model world denotes, given the current owners. -/
def observeWorld (input : LoaderInput) (owners : List Solanalib.Runtime.Pubkey) (state :
  AccountInfo.State) : WorldObs :=
  let step := fun (acc : List RegionEntry × Nat) (e : InputEntry) =>
    match e with
    | .duplicate i => (acc.1 ++ [.duplicate i], acc.2)
    | .account a =>
      let k := acc.2
      let lamports := match (state.lookupCell ⟨2 * k⟩).map (·.value) with
        | some (.lamports v) => v.toNat
        | _ => a.lamports
      let data := match (state.lookupCell ⟨2 * k + 1⟩).map (·.value) with
        | some (.data b) => b
        | _ => a.data
      (acc.1 ++ [.account ⟨255, flagByte a.isSigner, flagByte a.isWritable, flagByte a.executable,
          a.data.length, a.key, (owners.getD k .zero).bytes, lamports, data.length, data,
            a.rentEpoch, none⟩],
        k + 1)
  ⟨⟨(input.entries.foldl step ([], 0)).1, input.instructionData, input.programId⟩,
    (List.range state.cells.length).map (leaseOf state)⟩

def asWorldObs (state : Json) : Result WorldObs := do
  pure ⟨← region (← field state "input"), ← asList asLease (← field state "leases")⟩

def worldObsJson (o : WorldObs) : Json :=
  Json.mkObj [("region", "<region>"), ("leases", listJson leaseJson o.leases)]

/-! ## Slice-bounds panic messages -/

/-- The panic message of the Rust `&s[start..end]` on a slice of length `len`
outside its bounds (`core::slice::index::slice_index_fail`: the start index
first, then the end index, then their order). The slice-bounds panics of the models
carry no indices; a checker derives the message from the inputs of the record. -/
def sliceFailMessage (start stop len : Nat) : String :=
  if start > len then s!"range start index {start} out of range for slice of length {len}"
  else if stop > len then s!"range end index {stop} out of range for slice of length {len}"
  else s!"slice index starts at {start} but ends at {stop}"

/-- The length of the data a handle holds (0 if it holds none). -/
def dataLength (state : AccountInfo.State) (h : Borrow.Handle) : Nat :=
  match state.lookupCell h with
  | some ⟨.data bytes, _⟩ => bytes.length
  | _ => 0

/-! ## Frame conditions outside the models -/

def outcomeState (c : Case) : Result Json := field c.outcome "state"

/-- No syscall during the call: the replies are unchanged and the log is empty. -/
def noSyscalls (c : Case) : Result Bool := do
  let before ← syscallsOf c.state
  let after ← syscallsOf (← outcomeState c)
  pure (decide (after.replies = before.replies) && after.log.isEmpty)

/-- The accounts are as before the call: the whole region and the leases of
the borrows the case holds. -/
def accountsUnchanged (c : Case) : Result Bool := do
  let (input, world) ← asWorld c.state
  let recorded ← asWorldObs (← outcomeState c)
  pure (decide (recorded = observeWorld input (inputOwners input) world))

/-- A checker deciding the registered models `models` (source-map names), one
verdict each (Checker v2): a record is admitted when every model admits it,
and a divergence listing names the one model that must reject it. -/
def ofModels (function : String) (generics : List (String × String)) (reference : String)
    (models : List String) (run : Case → Result (List Verdict)) : Checker where
  function := function
  generics := generics
  reference := reference
  decides := models
  check := fun c => do
    let vs ← run c
    pure ⟨vs.all (·.admitted), Json.mkObj ((models.zip vs).map fun (m, v) => (m, v.expected))⟩
  checkModels := some fun c => do
    let vs ← run c
    pure ((models.zip vs).map fun (m, v) => ⟨m, v.admitted⟩,
      Json.mkObj ((models.zip vs).map fun (m, v) => (m, v.expected)))

/-- `ofModels` for a checker deciding one registered model. -/
def ofModel (function : String) (generics : List (String × String)) (model : String)
    (run : Case → Result Verdict) : Checker :=
  ofModels function generics model [model] fun c => do pure [← run c]

/-- Frame conditions outside the models: unmodelled parts of the state that
must be unchanged. A violated frame makes the verdict of every model a rejection. -/
def withFrame (frames : List (String × (Case → Result Bool))) (ch : Checker) : Checker :=
  let failedOf := fun (c : Case) => frames.filterMapM fun (name, f) => do
    pure (if ← f c then none else some name)
  { ch with
    check := fun c => do
      let v ← ch.check c
      let failed ← failedOf c
      if failed.isEmpty then pure v
      else pure ⟨false, Json.mkObj [("model", v.expected), ("frame_violated", listJson Json.str
        failed)]⟩
    checkModels := ch.checkModels.map fun f c => do
      let (vs, expected) ← f c
      let failed ← failedOf c
      if failed.isEmpty then pure (vs, expected)
      else pure (vs.map fun v => { v with admitted := false },
        Json.mkObj [("models", expected), ("frame_violated", listJson Json.str failed)]) }

/-- Decided preconditions (`requires`) of the models of the checker: a record
outside the precondition of a model is rejected by that model. -/
def withRequires (reqs : List (String × (Case → Result Bool))) (ch : Checker) : Checker :=
  let failedOf := fun (c : Case) => reqs.filterMapM fun (model, f) => do
    pure (if ← f c then none else some model)
  { ch with
    decidesRequires := ch.decidesRequires ++ reqs.map (·.1)
    check := fun c => do
      let v ← ch.check c
      let failed ← failedOf c
      if failed.isEmpty then pure v
      else pure ⟨false, Json.mkObj [("model", v.expected), ("requires_violated", listJson Json.str
        failed)]⟩
    checkModels := ch.checkModels.map fun f c => do
      let (vs, expected) ← f c
      let failed ← failedOf c
      if failed.isEmpty then pure (vs, expected)
      else pure (vs.map fun v => if failed.contains v.model then { v with admitted := false } else
        v,
        Json.mkObj [("models", expected), ("requires_violated", listJson Json.str failed)]) }

end SolanalibTest.Conformance.Library.Families.Anchor
