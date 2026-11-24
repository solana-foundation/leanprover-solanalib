/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Syscall

@[expose] public section

/-!
# Cross-program invocation

The source argument uses Agave 4.3.2, commit
`a203300045b405f86c9c84308b2eae76af69ac3b`; see the
[current CPI justification](../../source-notes/agave-4.3.2.md#cpi).
`program-runtime/src/cpi.rs:773-890` orders `cpi_common` as follows:

1. instruction translation and size limits (`:796`);
2. signer seeds and PDA signers under the caller program id (`:797-806`);
3. the check of authorized callees (`:807`);
4. the callee instruction accounts and the privilege checks (`:808`);
5. account-info translation and the pointer checks (`:810-811`);
6. `update_callee_account`: the caller view into the account, through the setters (`:813-837`);
7. the callee, through `process_instruction` (`:839-843`; cf. `Solanalib.Runtime.Exec`);
8. `update_caller_account`: the account into the caller view (`:849-865`).

This translation-then-synchronization order assumes `pointerChecks = true`, as in
`mainnet`. With that feature disabled, Agave synchronizes each account during
translation (`cpi.rs:1059-1075`), whereas these definitions translate all accounts
first. That configuration therefore has no ordering correspondence here.

Requests summarize VM translation using decoded values and supplied pointer and
metadata facts. Relating them to runtime memory requires valid address translation,
aligned and consistent serialization metadata, and consistent caller flags.
The additional region updates for memory configurations S and D
(`cpi.rs:867-887,1179-1221`) require a separate memory-mapping correspondence.

The runtime ignores the flags of the account infos; privileges come from the metas and
the caller instruction alone.
The callee invocation stays an explicit external execution boundary. In the model a
failure in any step ends the caller with that error. These `Except` definitions retain
the error and erase intermediate local mutations; they do not assert equality of
partially modified caller or account states on failure.
-/

namespace Solanalib.Runtime

/-- The transaction index of an address. -/
def txIndexOf (ts : TxState) (k : Pubkey) : Option Nat := ts.keys.idxOf? k

/-- The first instruction account of `f` with address `k`. -/
def instrAcctOf (ts : TxState) (f : Frame) (k : Pubkey) : Option InstrAcct :=
  f.accounts.find? fun ia => ts.key ia.txIdx == k

/-- The serialized position of the transaction account `t` in the caller input. -/
def serOf (c : InvCtx) (t : Nat) : Option SerAcct :=
  c.layout.find? fun s => match s.slot with
    | .acct ia => ia.txIdx == t
    | .dup _ => false

/-- Step 1 at the translated-value boundary: size limits and flag bytes
(`program-runtime/src/cpi.rs:129-143,538-601,676-742`, Agave 4.3.2).
The raw-memory translation and the intervening compute charges are separate
obligations of the request correspondence. -/
def translateIx (ix : CpiInstruction) : Except InstrError Unit :=
  if MAX_CPI_INSTRUCTION_ACCOUNTS < ix.metas.length then .error .ProgramFailedToComplete
  else if MAX_CPI_INSTRUCTION_DATA_LEN < ix.data.length then .error .ProgramFailedToComplete
  else if ix.metas.any (fun m => decide (1 < m.signerByte ∨ 1 < m.writableByte)) then
    .error .InvalidArgument
  else .ok ()

/-- Step 2: the PDA signers, derived with `create_program_address` under the caller
program id (`program-runtime/src/cpi.rs:631-674`, Agave 4.3.2). The request supplies
the translated seed bytes; `CryptoPrimitives` supplies the address primitives. -/
def pdaSignersCrypto (P : CryptoPrimitives) (caller : Pubkey) (signers : List (List Bytes)) :
    Except InstrError (List Pubkey) :=
  if MAX_SIGNERS < signers.length then .error .ProgramFailedToComplete
  else signers |> mapE fun seeds =>
    if MAX_SEEDS < seeds.length then .error .MaxSeedLengthExceeded
    else match createProgramAddressBytes P seeds caller.bytes with
      | .ok key => .ok (Pubkey.ofBytes key)
      | .error _ => .error .ProgramFailedToComplete

/-- The full primitive environment supplies the same shared address primitives. -/
def pdaSigners (P : Prims) (caller : Pubkey) (signers : List (List Bytes)) :
    Except InstrError (List Pubkey) :=
  pdaSignersCrypto P.toCryptoPrimitives caller signers

/-- The precompile ids selected by the profile. Agave 4.3.2 asks the bank callback
(`program-runtime/src/invoke_context.rs:793-796`, `runtime/src/bank.rs:6780-6783`).
Its table (`precompiles/src/lib.rs:54-82`) enables all three ids unconditionally.
The older secp256r1 feature check is retained only for the 3.1.12 branch. -/
def isPrecompile (p : Profile) (k : Pubkey) : Bool :=
  k == Ids.ed25519Program || k == Ids.secp256k1Program ||
    (k == Ids.secp256r1Program && (p.release != .agave_3_1_12 || p.features.secp256r1Precompile))

/-- Step 3: `check_authorized_program`
(`program-runtime/src/cpi.rs:159-182`, Agave 4.3.2).
Loader v3 accepts `Upgrade` (3), `SetAuthority` (4), `Close` (5), `SetAuthorityChecked` (7)
under its gate. The historical 3.1.12 branch additionally admits
`ExtendProgramChecked` (9) under its gate. -/
def checkAuthorized (p : Profile) (pid : Pubkey) (data : Bytes) : Except InstrError Unit :=
  let d0 := data.head?
  let loaderV3Ok :=
    d0 == some 3 || d0 == some 4 || d0 == some 5 ||
      (p.features.setAuthorityCheckedIx && d0 == some 7) ||
      (p.release == .agave_3_1_12 && p.features.extendProgramChecked && d0 == some 9)
  if pid == Ids.nativeLoader || pid == Ids.bpfLoader || pid == Ids.bpfLoaderDeprecated ||
      (pid == Ids.bpfLoaderUpgradeable && !loaderV3Ok) || isPrecompile p pid then
    .error .ProgramFailedToComplete
  else .ok ()

/-- The disjunction of the flags of an account and of a meta for the same address. -/
def mergeFlags (ia : InstrAcct) (m : CpiMeta) : InstrAcct :=
  ⟨ia.txIdx, ia.signer || m.signerByte == 1, ia.writable || m.writableByte == 1⟩

/-- The transaction lookup and merge pass of `prepare_next_cpi_instruction`
(`program-runtime/src/invoke_context.rs:368-408`, Agave 4.3.2). Repeated addresses
receive the disjunction of their flags. This pass does not inspect the caller:
every transaction lookup precedes every caller-membership or privilege check. -/
def mergeMeta (ts : TxState) (acc : List InstrAcct) (m : CpiMeta) :
    Except InstrError (List InstrAcct) :=
  match txIndexOf ts m.key with
  | none => .error .MissingAccount
  | some t =>
    if acc.any (·.txIdx == t) then
      .ok (acc.map fun ia => if ia.txIdx == t then mergeFlags ia m else ia)
    else .ok (acc ++ [⟨t, m.signerByte == 1, m.writableByte == 1⟩])

/-- The caller-membership and privilege checks of one deduplicated callee account
(`program-runtime/src/invoke_context.rs:434-459`, Agave 4.3.2). Membership precedes
the writable and signer checks for this account, before inspecting the next one.
`Frame.FlagsConsistent` makes the flag queries agree with the first caller
occurrence selected by Agave. -/
def checkPrivileges (ts : TxState) (caller : Frame) (pdas : List Pubkey) (ia : InstrAcct) :
    Except InstrError Unit :=
  if !caller.hasTx ia.txIdx then .error .MissingAccount
  else if ia.writable && !caller.writableTx ia.txIdx then .error .PrivilegeEscalation
  else if ia.signer && !(caller.signerTx ia.txIdx || pdas.contains (ts.key ia.txIdx)) then
    .error .PrivilegeEscalation
  else .ok ()

/-- The callee instruction accounts: for each meta in order, the deduplicated account with
the merged flags. -/
def calleeAccounts (ts : TxState) (ix : CpiInstruction) (dedup : List InstrAcct) : List InstrAcct :=
  ix.metas.filterMap fun m => (txIndexOf ts m.key).bind fun t => dedup.find? (·.txIdx == t)

/-- Step 4: `prepare_next_cpi_instruction`
(`program-runtime/src/invoke_context.rs:349-495`, Agave 4.3.2). First complete
transaction lookup and flag merging. Then check caller membership and privileges
in order of first occurrence. The callee program lookup follows those checks. -/
def prepareCallee (ts : TxState) (caller : Frame) (ix : CpiInstruction) (pdas : List Pubkey) :
    Except InstrError Frame :=
  match foldE (mergeMeta ts) [] ix.metas with
  | .error e => .error e
  | .ok dedup =>
    match forE (checkPrivileges ts caller pdas) dedup with
    | .error e => .error e
    | .ok () =>
      match instrAcctOf ts caller ix.programId with
      | none => .error .MissingAccount
      | some pia =>
        .ok { programIdx := pia.txIdx, accounts := calleeAccounts ts ix dedup, data := ix.data }

/-- A callee account after account-info translation. -/
structure Translated where
  t : Nat
  info : CpiAccountInfo
  infoIdx : Nat
  ser : SerAcct
  /-- The writable flag of the account in the caller, which `update_callee_account` uses. -/
  callerWritable : Bool
  /-- The writable flag in the callee, which selects the accounts of `update_caller_account`. -/
  calleeWritable : Bool
  /-- Whether the four pointers are the serialized addresses. -/
  inRegion : Bool
  deriving Repr

/-- The serialized VM addresses of the key, owner, lamports and data of position `s`. -/
def serAddrs (c : InvCtx) (s : SerAcct) : Nat × Nat × Nat × Nat :=
  (MM_INPUT_START + s.offset + c.abi.keyOff, MM_INPUT_START + s.offset + c.abi.ownerOff s.entryLen,
    MM_INPUT_START + s.offset + c.abi.lamportsOff, MM_INPUT_START + s.offset + c.abi.dataOff)

/-- The growth bound of the caller: 10 KiB, and none for a loader-v1 caller under
the pointer-check switch (`program-runtime/src/cpi.rs:228-238,1249-1257`, Agave 4.3.2). -/
def callerMaxIncrease (p : Profile) (c : InvCtx) : Nat :=
  if p.features.pointerChecks && c.abi == .v0 then 0 else MAX_PERMITTED_DATA_INCREASE

/-- Translation for one callee account (`program-runtime/src/cpi.rs:995-1093`,
Agave 4.3.2), using the address checks of `CallerAccount::from_account_info`
(`:272-405`) or `from_sol_account_info` (`:408-522`) and the growth bound of
`get_serialized_data` (`:228-238`). Pointer validity and serialized metadata are
supplied by the request correspondence. -/
def translateOne (p : Profile) (c : InvCtx) (ts : TxState) (req : CpiReq) (ia : InstrAcct) :
    Except InstrError (Option Translated) :=
  if (ts.acct ia.txIdx).executable then .ok none
  else
    match req.infos.findIdx? (fun i => i.key == ts.key ia.txIdx), serOf c ia.txIdx with
    | none, _ => .error .MissingAccount
    | _, none => .error .MissingAccount
    | some k, some s =>
      let info := req.infos.getD k (req.infos.head!)
      let (ka, oa, la, da) := serAddrs c s
      let inReg := info.keyAddr == ka && info.ownerAddr == oa && info.lamportsAddr == la &&
        info.dataAddr == da
      if p.features.pointerChecks && !(inReg && info.boxesBelowInput) then
        .error .ProgramFailedToComplete
      else if p.cpiEntryEdgeBound && p.release != .agave_3_1_12 &&
          decide (s.entryLen + callerMaxIncrease p c < info.dataLen) then
        .error .InvalidRealloc
      else
        let callerW := match c.frame.accounts.find? (·.txIdx == ia.txIdx) with
          | some cia => cia.writable
          | none => false
        .ok (some ⟨ia.txIdx, info, k, s, callerW, ia.writable, inReg⟩)

/-- The first occurrences among the instruction accounts of a frame. -/
def firstAccounts (f : Frame) : List InstrAcct :=
  (slots f).filterMap fun
    | .acct ia => some ia
    | .dup _ => none

/-- Step 5: the account-info checks (`program-runtime/src/cpi.rs:901-953`) and
first-occurrence translation (`:955-1095`, Agave 4.3.2). Translating all accounts
before `updateCallee` agrees with this source order when `pointerChecks = true`.
Both the excessive-info count and the aggregate pointer predicate produce the
same terminal error here; raw translation faults and compute charges remain
part of the request correspondence. -/
def translateInfos (p : Profile) (c : InvCtx) (ts : TxState) (req : CpiReq) (callee : Frame) :
    Except InstrError (List Translated) :=
  if p.maxCpiAccountInfos < req.infos.length then .error .ProgramFailedToComplete
  else if p.features.pointerChecks && !req.infosBelowInput then .error .ProgramFailedToComplete
  else
    match mapE (translateOne p c ts req) (firstAccounts callee) with
    | .error e => .error e
    | .ok xs => .ok (xs.filterMap id)

/-- The prepared CPI: the callee instruction and the translated accounts. -/
structure CpiPrep where
  callee : Frame
  translated : List Translated
  deriving Repr

/-- Steps 1 to 5 of `cpi_common` (`program-runtime/src/cpi.rs:796-811`, Agave 4.3.2),
subject to the translated-request and feature assumptions stated above. -/
def cpiPrepare (p : Profile) (P : Prims) (c : InvCtx) (ts : TxState) (req : CpiReq) :
    Except InstrError CpiPrep :=
  match translateIx req.ix with
  | .error e => .error e
  | .ok () =>
    match pdaSigners P (ts.key c.frame.programIdx) req.signers with
    | .error e => .error e
    | .ok pdas =>
      match checkAuthorized p req.ix.programId req.ix.data with
      | .error e => .error e
      | .ok () =>
        match prepareCallee ts c.frame req.ix pdas with
        | .error e => .error e
        | .ok callee =>
          match translateInfos p c ts req callee with
          | .error e => .error e
          | .ok tr => .ok { callee := callee, translated := tr }

/-! ## Synchronization of the accounts -/

/-- The caller view of a translated account: lamports, owner, length word and data. -/
def callerView (c : InvCtx) (st : InvState) (x : Translated) : Nat × Pubkey × Nat × Bytes :=
  if x.inRegion then
    (leNat (slice st.buf (x.ser.offset + c.abi.lamportsOff) 8),
      Pubkey.ofBytes (slice st.buf (x.ser.offset + c.abi.ownerOff x.ser.entryLen) 32),
      x.info.dataLen,
      slice st.buf (c.dataStart x.ser) x.info.dataLen)
  else (x.info.lamportsVal, x.info.ownerVal, x.info.dataLen, x.info.dataVal)

/-- `update_callee_account` (`program-runtime/src/cpi.rs:1108-1173`, Agave 4.3.2)
checks lamports, then data, then owner. The setters run in the caller instruction
context: the owner check uses the caller program and the writable check the
caller flag. The separate synchronization pass follows `:813-837` when
`pointerChecks = true`. -/
def updateCalleeOne (p : Profile) (c : InvCtx) (st : InvState) (x : Translated) :
    Except InstrError InvState :=
  let sc : SetterCtx := ⟨st.ts.key c.frame.programIdx, x.t, x.callerWritable, p.release⟩
  let (lam, owner, lenWord, data) := callerView c st x
  match lamportStep st.ts sc lam with
  | .error e => .error e
  | .ok ts1 =>
    let dataResult : Except InstrError InvState :=
      match c.cfg with
      | .L =>
        match dataStepL ts1 sc data data.length with
        | .error e => .error e
        | .ok ts2 => .ok { st with ts := ts2 }
      | cfg =>
        let prevLen := (ts1.acct x.t).data.length
        let buf1 :=
          if cfg != .D && lenWord < prevLen && x.inRegion then
            writeAt st.buf (c.dataStart x.ser + lenWord) (List.replicate (prevLen - lenWord) 0)
          else st.buf
        let boundOk := !(p.release == .agave_3_1_12 && lenWord != prevLen &&
          decide (x.ser.entryLen + callerMaxIncrease p c < lenWord))
        if !boundOk then .error .InvalidRealloc
        else
          let r2 := if lenWord = prevLen then .ok ts1 else setDataLength ts1 sc lenWord
          match r2 with
          | .error e => .error e
          | .ok ts2 =>
            if cfg != .D then
              match canDataBeChanged ts2 sc with
              | .ok () =>
                match setDataFromSlice ts2 sc (if x.inRegion then slice buf1 (c.dataStart x.ser)
                  lenWord else data) with
                | .error e => .error e
                | .ok ts3 => .ok { st with ts := ts3, buf := buf1 }
              | .error _ => .ok { st with ts := ts2, buf := buf1 }
            else .ok { st with ts := ts2, buf := buf1 }
    match dataResult with
    | .error e => .error e
    | .ok st2 =>
      match ownerStep st2.ts sc owner with
      | .error e => .error e
      | .ok ts4 => .ok { st2 with ts := ts4 }

/-- `update_callee_account` for all translated accounts, in callee order. -/
def updateCallee (p : Profile) (c : InvCtx) : InvState → List Translated → Except InstrError
  InvState
  | st, [] => .ok st
  | st, x :: rest =>
    match updateCalleeOne p c st x with
    | .error e => .error e
    | .ok st' => updateCallee p c st' rest

/-- `update_caller_account` for one account writable in the callee
(`program-runtime/src/cpi.rs:1235-1327`, Agave 4.3.2). It writes the caller view
and changes no account. Agave writes lamports and owner before checking the growth
bound; this pure result retains only the terminal error on failure. Successful
results represent the caller view after the writes, under the stated memory
correspondence. The second component is the length word, which the program writes. -/
def updateCallerOne (p : Profile) (c : InvCtx) (st : InvState) (x : Translated) :
    Except InstrError (InvState × Nat) :=
  let a := st.ts.acct x.t
  let prevLen := x.info.dataLen
  let postLen := a.data.length
  let reserved := x.ser.entryLen + callerMaxIncrease p c
  if reserved < postLen && (p.features.pointerChecks || prevLen != postLen) then
    .error .InvalidRealloc
  else if !x.inRegion then .ok (st, postLen)
  else
    let o := x.ser.offset
    let ds := c.dataStart x.ser
    let buf1 := writeAt (writeAt st.buf (o + c.abi.lamportsOff) (u64le a.lamports))
      (o + c.abi.ownerOff x.ser.entryLen) a.owner.bytes
    let buf2 :=
      if prevLen != postLen then
        let z := if postLen < prevLen && c.cfg != .D then
            writeAt buf1 (ds + postLen) (List.replicate (prevLen - postLen) 0) else buf1
        writeAt z (o + c.abi.lenOff) (u64le postLen)
      else buf1
    let buf3 := if c.cfg != .D then writeAt buf2 ds a.data else buf2
    .ok ({ st with buf := buf3 }, postLen)

/-- The answer of a successful CPI: r0 = 0, and for each account info its final length
word, followed by the lamports, owner and data for an info whose pointers lie outside
the input region. -/
def cpiAnswer (st : InvState) (req : CpiReq) (lens : List (Nat × Nat)) (tr : List Translated) :
    SysAns :=
  ⟨0, (List.range req.infos.length).map fun k =>
    let info := req.infos.getD k (req.infos.head!)
    let len := (lens.find? (·.1 == k)).map (·.2) |>.getD info.dataLen
    match tr.find? (fun x => x.infoIdx == k && x.calleeWritable && !x.inRegion) with
    | some x => u64le len ++ u64le (st.ts.acct x.t).lamports ++ (st.ts.acct x.t).owner.bytes ++
        (st.ts.acct x.t).data
    | none => u64le len⟩

/-- `update_caller_account` for all translated accounts writable in the callee,
in the order of `program-runtime/src/cpi.rs:849-865` (Agave 4.3.2). -/
def updateCaller (p : Profile) (c : InvCtx) :
    InvState → List Translated → Except InstrError (InvState × List (Nat × Nat))
  | st, [] => .ok (st, [])
  | st, x :: rest =>
    if !x.calleeWritable then updateCaller p c st rest
    else match updateCallerOne p c st x with
      | .error e => .error e
      | .ok (st', len) =>
        match updateCaller p c st' rest with
        | .error e => .error e
        | .ok (st'', lens) => .ok (st'', (x.infoIdx, len) :: lens)

/-! ## What the synchronization changes -/

/-- The accounts that `update_callee_account` may change: those writable in the caller. -/
def CallerWritable (tr : List Translated) (j : Nat) : Prop :=
  ∃ x ∈ tr, x.t = j ∧ x.callerWritable = true

theorem Changes.of_updateCalleeOne {p : Profile} {c : InvCtx} {st st' : InvState} {x : Translated}
    (h : updateCalleeOne p c st x = .ok st') :
    Changes st.ts st'.ts (fun j => j = x.t ∧ x.callerWritable = true) := by
  unfold updateCalleeOne at h
  simp only at h
  split at h
  · cases h
  · rename_i ts1 h1
    have c1 := Changes.of_lamportStep h1
    split at h
    · cases h
    · rename_i st2 h2
      have c2 : Changes ts1 st2.ts (fun j => j = x.t ∧ x.callerWritable = true) := by
        split at h2
        · split at h2
          · cases h2
          · rename_i ts2 h3
            cases h2
            exact Changes.of_dataStep (cfg := .L) (by simpa [dataStep] using h3)
        · split at h2
          · cases h2
          · split at h2
            · cases h2
            · rename_i ts2 h3
              have c3 : Changes ts1 ts2 (fun j => j = x.t ∧ x.callerWritable = true) := by
                split at h3
                · cases h3; exact Changes.refl _ _
                · exact Changes.of_setterStep (SetterStep.of_setDataLength h3)
              split at h2
              · split at h2
                · split at h2
                  · cases h2
                  · rename_i ts3 h4
                    cases h2
                    exact c3.trans (Changes.of_setterStep (SetterStep.of_setDataFromSlice h4))
                · cases h2; exact c3
              · cases h2; exact c3
      split at h
      · cases h
      · rename_i ts4 h4
        cases h
        exact c1.trans (c2.trans (Changes.of_ownerStep h4))

theorem Changes.of_updateCallee {p : Profile} {c : InvCtx} :
    ∀ {tr : List Translated} {st st' : InvState}, updateCallee p c st tr = .ok st' →
      Changes st.ts st'.ts (CallerWritable tr)
  | [], st, st', h => by cases h; exact Changes.refl _ _
  | x :: rest, st, st', h => by
    unfold updateCallee at h
    split at h
    · cases h
    · rename_i st1 h1
      refine ((Changes.of_updateCalleeOne h1).mono ?_).trans
        ((Changes.of_updateCallee h).mono ?_)
      · rintro j ⟨rfl, hw⟩; exact ⟨x, List.mem_cons_self .., rfl, hw⟩
      · rintro j ⟨y, hy, hj, hw⟩; exact ⟨y, List.mem_cons_of_mem _ hy, hj, hw⟩

theorem updateCallerOne_ts {p : Profile} {c : InvCtx} {st st' : InvState} {x : Translated}
    {n : Nat} (h : updateCallerOne p c st x = .ok (st', n)) : st'.ts = st.ts := by
  unfold updateCallerOne at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h; rfl

theorem updateCaller_ts {p : Profile} {c : InvCtx} :
    ∀ {tr : List Translated} {st st' : InvState} {lens : List (Nat × Nat)},
      updateCaller p c st tr = .ok (st', lens) → st'.ts = st.ts
  | [], st, st', lens, h => by cases h; rfl
  | x :: rest, st, st', lens, h => by
    unfold updateCaller at h
    split at h
    · exact updateCaller_ts h
    · split at h
      · cases h
      · rename_i st1 n h1
        split at h
        · cases h
        · rename_i st2 lens2 h2
          cases h
          exact (updateCaller_ts h2).trans (updateCallerOne_ts h1)

end Solanalib.Runtime
