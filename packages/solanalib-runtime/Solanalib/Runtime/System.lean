/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Cpi

@[expose] public section

/-!
# The System program

The instructions of Agave 4.3.2, `programs/system/src/system_processor.rs`, that
create, fund, allocate and assign accounts, with their value-level order of checks.
System nonce instruction execution remains an opaque builtin (`Havoc` in
`Solanalib.Runtime.Exec`); the separate transaction nonce-admission check does not
supply an execution semantics for those instructions.
Errors of `SystemError` are `Custom` with the discriminant from
solana-system-interface 3.3.0. The source mapping, decoding assumptions and
instruction scope are in
[System instructions](../../source-notes/agave-4.3.2.md#system-instructions).
-/

namespace Solanalib.Runtime

/-! ## Bincode reading -/

/-- A reader over instruction data: the value and the next offset. -/
abbrev Reader (α : Type) := Bytes → Nat → Option (α × Nat)

def readLE (k : Nat) : Reader Nat := fun d off =>
  if off + k ≤ d.length then some (leNat (slice d off k), off + k) else none

def readPubkey : Reader Pubkey := fun d off =>
  if off + 32 ≤ d.length then some (Pubkey.ofBytes (slice d off 32), off + 32) else none

/-- A bincode `String`: a `u64` length and UTF-8 bytes. -/
def readString (P : Prims) : Reader Bytes := fun d off =>
  match readLE 8 d off with
  | none => none
  | some (n, off') =>
    if off' + n ≤ d.length && P.isUtf8 (slice d off' n) then some (slice d off' n, off' + n)
    else none

/-- The System instructions (`solana-system-interface-3.3.0/src/instruction.rs`). -/
inductive SystemIx where
  | createAccount (lamports space : Nat) (owner : Pubkey)
  | assign (owner : Pubkey)
  | transfer (lamports : Nat)
  | createAccountWithSeed (base : Pubkey) (seed : Bytes) (lamports space : Nat) (owner : Pubkey)
  | advanceNonceAccount
  | withdrawNonceAccount (lamports : Nat)
  | initializeNonceAccount (authority : Pubkey)
  | authorizeNonceAccount (authority : Pubkey)
  | allocate (space : Nat)
  | allocateWithSeed (base : Pubkey) (seed : Bytes) (space : Nat) (owner : Pubkey)
  | assignWithSeed (base : Pubkey) (seed : Bytes) (owner : Pubkey)
  | transferWithSeed (lamports : Nat) (fromSeed : Bytes) (fromOwner : Pubkey)
  | upgradeNonceAccount
  | createAccountAllowPrefund (lamports space : Nat) (owner : Pubkey)
  deriving Repr

/-- The represented `limited_deserialize` of solana-bincode 3.1.0: fixed-integer
encoding with a `u32` tag, then the fields, a 1232-byte consumed-data limit and
trailing bytes allowed. See
[System instructions](../../source-notes/agave-4.3.2.md#system-instructions). -/
def decodeSystemIx (P : Prims) (d : Bytes) : Option SystemIx := do
  let (tag, o) ← readLE 4 d 0
  let ix ← match tag with
    | 0 => do
      let (l, o) ← readLE 8 d o; let (s, o) ← readLE 8 d o; let (w, o) ← readPubkey d o
      pure (SystemIx.createAccount l s w, o)
    | 1 => do let (w, o) ← readPubkey d o; pure (.assign w, o)
    | 2 => do let (l, o) ← readLE 8 d o; pure (.transfer l, o)
    | 3 => do
      let (b, o) ← readPubkey d o; let (sd, o) ← readString P d o
      let (l, o) ← readLE 8 d o; let (s, o) ← readLE 8 d o; let (w, o) ← readPubkey d o
      pure (.createAccountWithSeed b sd l s w, o)
    | 4 => pure (.advanceNonceAccount, o)
    | 5 => do let (l, o) ← readLE 8 d o; pure (.withdrawNonceAccount l, o)
    | 6 => do let (a, o) ← readPubkey d o; pure (.initializeNonceAccount a, o)
    | 7 => do let (a, o) ← readPubkey d o; pure (.authorizeNonceAccount a, o)
    | 8 => do let (s, o) ← readLE 8 d o; pure (.allocate s, o)
    | 9 => do
      let (b, o) ← readPubkey d o; let (sd, o) ← readString P d o
      let (s, o) ← readLE 8 d o; let (w, o) ← readPubkey d o
      pure (.allocateWithSeed b sd s w, o)
    | 10 => do
      let (b, o) ← readPubkey d o; let (sd, o) ← readString P d o; let (w, o) ← readPubkey d o
      pure (.assignWithSeed b sd w, o)
    | 11 => do
      let (l, o) ← readLE 8 d o; let (sd, o) ← readString P d o; let (w, o) ← readPubkey d o
      pure (.transferWithSeed l sd w, o)
    | 12 => pure (.upgradeNonceAccount, o)
    | 13 => do
      let (l, o) ← readLE 8 d o; let (s, o) ← readLE 8 d o; let (w, o) ← readPubkey d o
      pure (.createAccountAllowPrefund l s w, o)
    | _ => none
  if ix.2 ≤ 1232 then some ix.1 else none

/-! ## Processing -/

/-- The `SystemError` codes. -/
def sysErr (n : Nat) : InstrError := .Custom n

/-- The context of a System instruction: the program, the instruction and the signers. -/
structure SysCtx where
  ts : TxState
  f : Frame
  release : Release := .agave_4_3_2

namespace SysCtx

def acctAt (c : SysCtx) (j : Nat) : InstrAcct := c.f.accounts.getD j default
def keyAt (c : SysCtx) (j : Nat) : Pubkey := c.ts.key (c.acctAt j).txIdx
def sc (c : SysCtx) (ts : TxState) (j : Nat) : SetterCtx :=
  setterCtxOf ts c.f.programIdx (c.acctAt j) c.release
def isSigner (c : SysCtx) (k : Pubkey) : Bool :=
  c.f.accounts.any fun ia => ia.signer && c.ts.key ia.txIdx == k

end SysCtx

/-- `check_number_of_instruction_accounts`. -/
def needAccounts (f : Frame) (n : Nat) : Except InstrError Unit :=
  if f.accounts.length < n then .error .MissingAccount else .ok ()

/-- `Address::create`: the address of an account, re-derived from a seed when one is
given; the signer of a derived address is its base. -/
def sysAddress (P : Prims) (addr : Pubkey) (withSeed : Option (Pubkey × Bytes × Pubkey)) :
    Except InstrError (Pubkey × Option Pubkey) :=
  match withSeed with
  | none => .ok (addr, none)
  | some (base, seed, owner) =>
    match createWithSeed P base seed owner with
    | .error e => .error (InstrError.fromU64 e)
    | .ok derived => if addr ≠ derived then .error (sysErr 5) else .ok (addr, some base)

def addrSigned (c : SysCtx) (a : Pubkey × Option Pubkey) : Bool :=
  match a.2 with
  | some base => c.isSigner base
  | none => c.isSigner a.1

/-- `allocate` in Agave 4.3.2, `programs/system/src/system_processor.rs`. -/
def sysAllocate (c : SysCtx) (ts : TxState) (j : Nat) (a : Pubkey × Option Pubkey) (space : Nat) :
    Except InstrError TxState :=
  let acc := ts.acct (c.acctAt j).txIdx
  if !addrSigned c a then .error .MissingRequiredSignature
  else if !acc.data.isEmpty || acc.owner ≠ Ids.systemProgram then .error (sysErr 0)
  else if MAX_ACCOUNT_DATA_LEN < space then .error (sysErr 3)
  else setDataLength ts (c.sc ts j) space

/-- `assign` in Agave 4.3.2, `programs/system/src/system_processor.rs`. -/
def sysAssign (c : SysCtx) (ts : TxState) (j : Nat) (a : Pubkey × Option Pubkey) (owner : Pubkey) :
    Except InstrError TxState :=
  if (ts.acct (c.acctAt j).txIdx).owner = owner then .ok ts
  else if !addrSigned c a then .error .MissingRequiredSignature
  else setOwner ts (c.sc ts j) owner

def sysAllocateAndAssign (c : SysCtx) (ts : TxState) (j : Nat) (a : Pubkey × Option Pubkey)
    (space : Nat) (owner : Pubkey) : Except InstrError TxState :=
  match sysAllocate c ts j a space with
  | .error e => .error e
  | .ok ts1 => sysAssign c ts1 j a owner

/-- `transfer_verified` in Agave 4.3.2, `programs/system/src/system_processor.rs`. -/
def sysTransferVerified (c : SysCtx) (ts : TxState) (src dst lamports : Nat) :
    Except InstrError TxState :=
  let fromAcct := ts.acct (c.acctAt src).txIdx
  if !fromAcct.data.isEmpty then .error .InvalidArgument
  else if fromAcct.lamports < lamports then .error (sysErr 1)
  else
    match checkedSubLamports ts (c.sc ts src) lamports with
    | .error e => .error e
    | .ok ts1 => checkedAddLamports ts1 (c.sc ts1 dst) lamports

/-- `transfer` in Agave 4.3.2, `programs/system/src/system_processor.rs`. -/
def sysTransfer (c : SysCtx) (ts : TxState) (src dst lamports : Nat) : Except InstrError TxState :=
  if !(c.acctAt src).signer then .error .MissingRequiredSignature
  else sysTransferVerified c ts src dst lamports

/-- `create_account` in Agave 4.3.2, `programs/system/src/system_processor.rs`. -/
def sysCreateAccount (c : SysCtx) (ts : TxState) (a : Pubkey × Option Pubkey)
    (lamports space : Nat) (owner : Pubkey) : Except InstrError TxState :=
  if 0 < (ts.acct (c.acctAt 1).txIdx).lamports then .error (sysErr 0)
  else match sysAllocateAndAssign c ts 1 a space owner with
    | .error e => .error e
    | .ok ts1 => sysTransfer c ts1 0 1 lamports

/-- The System program. The result is `none` for the nonce instructions, which the
model does not interpret. -/
def systemProcess (p : Profile) (P : Prims) (ts : TxState) (f : Frame) :
    Option (Except InstrError TxState) :=
  let c : SysCtx := ⟨ts, f, p.release⟩
  match decodeSystemIx P f.data with
  | none => some (.error .InvalidInstructionData)
  | some ix =>
    match ix with
    | .createAccount l s w => some <|
      match needAccounts f 2 with
      | .error e => .error e
      | .ok () => sysCreateAccount c ts (c.keyAt 1, none) l s w
    | .createAccountWithSeed b sd l s w => some <|
      match needAccounts f 2 with
      | .error e => .error e
      | .ok () =>
        match sysAddress P (c.keyAt 1) (some (b, sd, w)) with
        | .error e => .error e
        | .ok a => sysCreateAccount c ts a l s w
    | .assign w => some <|
      match needAccounts f 1 with
      | .error e => .error e
      | .ok () => sysAssign c ts 0 (c.keyAt 0, none) w
    | .transfer l => some <|
      match needAccounts f 2 with
      | .error e => .error e
      | .ok () => sysTransfer c ts 0 1 l
    | .transferWithSeed l sd w => some <|
      match needAccounts f 3 with
      | .error e => .error e
      | .ok () =>
        if !(c.acctAt 1).signer then .error .MissingRequiredSignature
        else match createWithSeed P (c.keyAt 1) sd w with
          | .error e => .error (InstrError.fromU64 e)
          | .ok derived =>
            if c.keyAt 0 ≠ derived then .error (sysErr 5)
            else sysTransferVerified c ts 0 2 l
    | .allocate s => some <|
      match needAccounts f 1 with
      | .error e => .error e
      | .ok () => sysAllocate c ts 0 (c.keyAt 0, none) s
    | .allocateWithSeed b sd s w => some <|
      match needAccounts f 1 with
      | .error e => .error e
      | .ok () =>
        match sysAddress P (c.keyAt 0) (some (b, sd, w)) with
        | .error e => .error e
        | .ok a => sysAllocateAndAssign c ts 0 a s w
    | .assignWithSeed b sd w => some <|
      match needAccounts f 1 with
      | .error e => .error e
      | .ok () =>
        match sysAddress P (c.keyAt 0) (some (b, sd, w)) with
        | .error e => .error e
        | .ok a => sysAssign c ts 0 a w
    | .createAccountAllowPrefund l s w => some <|
      if !p.features.createAccountAllowPrefund then .error .InvalidInstructionData
      else
        match needAccounts f (if 0 < l then 2 else 1) with
        | .error e => .error e
        | .ok () =>
          match sysAllocateAndAssign c ts 0 (c.keyAt 0, none) s w with
          | .error e => .error e
          | .ok ts1 => if 0 < l then sysTransfer c ts1 1 0 l else .ok ts1
    | .advanceNonceAccount | .withdrawNonceAccount _ | .initializeNonceAccount _
    | .authorizeNonceAccount _ | .upgradeNonceAccount => none

end Solanalib.Runtime
