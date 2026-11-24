/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Runtime

/-!
Finite executable observations of the canonical model for the shared fixtures.
This driver adds no runtime definitions, axioms, or Rust body correctness claims.
Errors of `Except` carry no intermediate state; the output marks those fields
unavailable rather than asserting rollback of individual native setters.
-/

set_option autoImplicit false

open Solanalib.Runtime

namespace SolanalibTest.Conformance.Runtime

private def number (value : String) : Nat :=
  match value.toNat? with
  | some n => n
  | none => panic! s!"invalid natural number: {value}"

private def bytes (value : String) : Bytes :=
  if value == "-" then []
  else (value.splitOn ",").map (fun n => UInt8.ofNat (number n))

private def hex (data : Bytes) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList (data.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

private def status {α : Type} (result : Except InstrError α) : String :=
  match result with
  | .ok _ => "ok"
  | .error error => (reprStr error).replace "Solanalib.Runtime.InstrError." ""

private def frame (writable signer : Bool) (references : Nat) : Frame :=
  { programIdx := 1
    accounts := List.replicate references ⟨0, signer, writable⟩
    data := [7, 8, 9] }

private def context (owner : Nat) (writable signer : Bool) (lamports : Nat)
    (data : Bytes) (executable : Bool) (rentEpoch references : Nat) (deprecated : Bool) : TxState :=
  let instruction := frame writable signer references
  { keys := [Pubkey.ofNat 10, Pubkey.ofNat 20]
    accts := [⟨lamports, data, Pubkey.ofNat owner, executable, rentEpoch⟩,
      ⟨1, [], if deprecated then Ids.bpfLoaderDeprecated else Ids.bpfLoaderUpgradeable, true, 0⟩]
    lamportsDelta := 0
    resizeDelta := 0
    stack := [instruction]
    trace := [⟨1, instruction⟩]
    returnData := (default, [])
    topIndex := 0 }

private def accounts (state : TxState) : String :=
  String.intercalate "|" (state.accts.map fun account =>
    String.intercalate "," [toString account.lamports, hex account.owner.bytes,
      hex account.data, if account.executable then "1" else "0", toString account.rentEpoch])

private def emit (id kind : String) (result : Except InstrError TxState)
    (serialized edited : String) (auxiliary : String := "-") : IO Unit := do
  let observations := match result with
    | .error _ => ["-", "-", "-"]
    | .ok state => [accounts state, toString state.resizeDelta, status (pop state)]
  IO.println (String.intercalate "\t"
    ([id, kind, status result] ++ observations ++ [serialized, edited, auxiliary]))

private def accountCase (fields : Array String) : IO Unit := do
  let state := context (number fields[2]!) (fields[3]! == "1") (fields[4]! == "1")
    (number fields[5]!) (bytes fields[6]!) (fields[7]! == "1") (number fields[8]!) 1 false
  let value := number fields[9]!
  let setter : SetterCtx := ⟨Pubkey.ofNat 20, 0, fields[3]! == "1", .agave_4_3_2⟩
  let result ← match fields[1]! with
    | "read_fields" => pure (.ok state)
    | "set_lamports" => pure (setLamports state setter value)
    | "checked_add" => pure (checkedAddLamports state setter value)
    | "checked_sub" => pure (checkedSubLamports state setter value)
    | "set_data" => pure (setDataFromSlice state setter (bytes fields[10]!))
    | "set_length" => pure (setDataLength state setter value)
    | "set_owner" => pure (setOwner state setter (Pubkey.ofNat value))
    | "set_executable" => pure (setExecutable state mainnet.rent setter (value != 0))
    | "can_data" => pure ((canDataBeChanged state setter).map fun _ => state)
    | "can_resize" => pure ((canDataBeResized state setter value).map fun _ => state)
    | "missing_account" => pure (setLamports state { setter with txIdx := 2 } value)
    | operation => throw (IO.userError s!"unknown account operation: {operation}")
  emit fields[0]! "account" result "-" "-"

private def editBuffer (buffer : Bytes) (edits : String) : IO Bytes := do
  if edits == "-" then return buffer
  let mut result := buffer
  for edit in edits.splitOn ";" do
    let fields := (edit.splitOn ":").toArray
    unless fields.size == 2 do throw (IO.userError s!"invalid edit: {edit}")
    let offset := number fields[0]!
    let replacement := bytes fields[1]!
    unless offset + replacement.length ≤ result.length do
      throw (IO.userError s!"out-of-bounds fixture edit: {edit}")
    result := writeAt result offset replacement
  return result

private def serializationCase (fields : Array String) : IO Unit := do
  let abi := if fields[1]! == "v0" then Abi.v0 else Abi.v1
  let state := context (number fields[3]!) (fields[4]! == "1") (fields[5]! == "1")
    (number fields[6]!) (bytes fields[7]!) (fields[8]! == "1") (number fields[9]!)
    (number fields[2]!) (abi == .v0)
  let instruction := frame (fields[4]! == "1") (fields[5]! == "1") (number fields[2]!)
  match serializeChecked abi mainnet state instruction with
  | .error error => emit fields[0]! "serialization" (.error error) "-" "-"
  | .ok buffer =>
    let edited ← editBuffer buffer fields[10]!
    let result := readBack abi .L 1 edited state (layout abi mainnet state instruction)
    emit fields[0]! "serialization" result (hex buffer) (hex edited)

/-- The no-seed specialization avoids supplying dummy cryptographic primitives. -/
private def unsignedPrepare (p : Profile) (c : InvCtx) (state : TxState) (request : CpiReq) :
    Except InstrError CpiPrep :=
  match translateIx request.ix with
  | .error error => .error error
  | .ok () =>
    match checkAuthorized p request.ix.programId request.ix.data with
    | .error error => .error error
    | .ok () =>
      match prepareCallee state c.frame request.ix [] with
      | .error error => .error error
      | .ok callee =>
        match translateInfos p c state request callee with
        | .error error => .error error
        | .ok translated => .ok ⟨callee, translated⟩

/-- Kernel-checked specialization of the canonical preparation, for every
primitive environment. It is not a Rust implementation refinement theorem. -/
theorem unsignedPrepare_eq (p : Profile) (P : Prims) (c : InvCtx) (state : TxState)
    (request : CpiReq) (noSigners : request.signers = []) :
    cpiPrepare p P c state request = unsignedPrepare p c state request := by
  simp only [cpiPrepare, unsignedPrepare, pdaSigners, pdaSignersCrypto, noSigners,
    List.length_nil, MAX_SIGNERS, Nat.not_lt_zero, ↓reduceIte, mapE]
  rfl

private def cpiResult (c : InvCtx) (before : InvState) (request : CpiReq)
    (calleeExpected calleeData : Bytes) : Except InstrError (InvState × SysAns) := do
  let prepared ← unsignedPrepare mainnet c before.ts request
  let synced ← updateCallee mainnet c before prepared.translated
  let pushed ← push mainnet synced.ts prepared.callee
  let entered := resetReturnData pushed
  -- This local fixture corresponds to the finite behavior of FixtureCallee. Its
  -- deployed implementation and arbitrary program effects remain outside the claim.
  if (entered.acct 0).data != calleeExpected || (entered.acct 0).owner != Pubkey.ofNat 30 then
    throw .InvalidAccountData
  let written ← setDataFromSlice entered
    (setterCtxOf entered prepared.callee.programIdx ⟨0, true, true⟩) calleeData
  let observation := UInt8.ofNat prepared.callee.accounts.length ::
    (prepared.callee.accounts.flatMap fun account =>
      [boolByte account.signer, boolByte account.writable]) ++ (entered.acct 0).data
  let tagged := setNativeReturnData written (Pubkey.ofNat 30) observation
  let popped ← pop tagged
  let (returned, lengths) ← updateCaller mainnet c { synced with ts := popped } prepared.translated
  return (returned, cpiAnswer returned request lengths prepared.translated)

private def cpiCase (fields : Array String) : IO Unit := do
  let entryData := bytes fields[1]!
  let callerData := bytes fields[2]!
  let calleeExpected := bytes fields[3]!
  let calleeData := bytes fields[4]!
  let duplicate := fields[5]! == "1"
  let badPointer := fields[6]! == "1"
  let writable := fields[7]! == "1"
  let caller : Frame := ⟨1, [⟨0, true, writable⟩, ⟨0, true, writable⟩, ⟨2, false, false⟩], [7, 8,
    9]⟩
  let base := context 20 writable true 1000000 entryData false 7 1 false
  let state := { base with
    keys := [Pubkey.ofNat 10, Pubkey.ofNat 20, Pubkey.ofNat 30]
    accts := base.accts ++ [⟨1, [], Ids.nativeLoader, true, 0⟩]
    stack := [caller]
    trace := [⟨1, caller⟩] }
  let buffer := serialize .v1 mainnet state caller
  let c : InvCtx := ⟨.v1, .L, caller, layout .v1 mainnet state caller, 1024, .agave_4_3_2⟩
  let edited := writeAt (writeAt (writeAt buffer 48 (Pubkey.ofNat 30).bytes)
    88 (u64le callerData.length)) 96 callerData
  let before : InvState := ⟨state, edited, 0, []⟩
  let info : CpiAccountInfo :=
    { key := Pubkey.ofNat 10
      keyAddr := MM_INPUT_START + 16
      ownerAddr := MM_INPUT_START + 48
      lamportsAddr := MM_INPUT_START + 80
      dataAddr := MM_INPUT_START + 96 + (if badPointer then 1 else 0)
      dataLen := callerData.length
      boxesBelowInput := true
      lamportsVal := 0
      ownerVal := default
      dataVal := [] }
  let message := UInt8.ofNat calleeExpected.length :: calleeExpected ++
    [UInt8.ofNat calleeData.length] ++ calleeData
  let request : CpiReq :=
    { ix := ⟨Pubkey.ofNat 30, [⟨Pubkey.ofNat 10, 1, 1⟩] ++
        (if duplicate then [⟨Pubkey.ofNat 10, 0, 0⟩] else []), message⟩
      infos := [info]
      infosBelowInput := true
      signers := [] }
  match cpiResult c before request calleeExpected calleeData with
  | .error error => emit fields[0]! "cpi" (.error error) (hex buffer) "-"
  | .ok (returned, answer) =>
    let auxiliary := s!"info_len={leNat (answer.out.headD [])};" ++
      s!"return_program={hex returned.ts.returnData.1.bytes};" ++
      s!"return={hex returned.ts.returnData.2};" ++
      s!"cpi_count={(returned.ts.trace.filter (fun entry => 1 < entry.height)).length};" ++
      s!"stack={returned.ts.stack.length}"
    emit fields[0]! "cpi" (.ok returned.ts) (hex buffer) (hex returned.buf) auxiliary

private def forRows (path : System.FilePath) (apply : Array String → IO Unit)
    (columns : Nat := 11) : IO Unit := do
  let contents ← IO.FS.readFile path
  for line in contents.splitOn "\n" do
    unless line.isEmpty || line.startsWith "#" do
      let fields := (line.splitOn "\t").toArray
      unless fields.size == columns do throw (IO.userError s!"invalid fixture row: {line}")
      apply fields

def run (root : System.FilePath) : IO Unit := do
  forRows (root / "accounts.tsv") accountCase
  forRows (root / "serialization.tsv") serializationCase
  forRows (root / "cpi.tsv") cpiCase 8

end SolanalibTest.Conformance.Runtime

def main (args : List String) : IO Unit := do
  match args with
  | [root] => SolanalibTest.Conformance.Runtime.run root
  | _ => throw (IO.userError "expected the fixture directory argument")
