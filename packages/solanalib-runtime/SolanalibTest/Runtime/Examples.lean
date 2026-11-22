/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Theorems
public meta import Solanalib.Runtime.Theorems

@[expose] public section

/-!
# Examples

Evaluations that check the definitions against the inventories.
Each `#guard` runs when the file is compiled.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.Examples

def key1 : Pubkey := Pubkey.ofNat 1
def owner1 : Pubkey := Pubkey.ofNat 2
def prog : Pubkey := Pubkey.ofNat 3

def acct1 : Account := ⟨1000, [1, 2, 3, 4, 5], owner1, false, 7⟩
def progAcct : Account := ⟨1, [], Ids.bpfLoaderUpgradeable, true, 0⟩

/-- Whether a result is success with the given accounts. -/
def okWith (r : Except InstrError (List Account)) (as : List Account) : Bool :=
  match r with
  | .ok x => x == as
  | .error _ => false

/-- Whether a result is the given error. -/
def errWith (r : Except InstrError (List Account)) (e : InstrError) : Bool :=
  match r with
  | .error x => x == e
  | .ok _ => false

def ts0 : TxState := initTxState [key1, prog] [acct1, progAcct]
def f0 : Frame := { programIdx := 1, accounts := [⟨0, true, true⟩], data := [9, 8, 7] }
def buf0 : Bytes := serialize .v1 mainnet ts0 f0
def lay0 : List SerAcct := layout .v1 mainnet ts0 f0

/-! ## A concrete aligned serialization

One non-duplicate account with 5 data bytes and an instruction with 3 data bytes.
The field order follows `serialize_parameters_for_abiv1` in Agave 4.3.2; see
[serialization and read-back](../../source-notes/agave-4.3.2.md#serialization-and-read-back). -/

#guard instrDataOffset .v1 mainnet ts0 f0 = 10360
#guard buf0.length = 10395
#guard slice buf0 0 8 = u64le 1
#guard slice buf0 8 4 = [0xFF, 1, 1, 0]
#guard slice buf0 96 5 = [1, 2, 3, 4, 5]
#guard slice buf0 101 10240 = List.replicate 10240 0
-- Agave 4.3.2 serializes the rent epoch as `u64::MAX` unconditionally.
#guard slice buf0 10344 8 = u64le U64_MAX
#guard slice buf0 10352 8 = u64le 3
#guard slice buf0 10360 3 = [9, 8, 7]
#guard slice buf0 10363 32 = prog.bytes

/-! ## Duplicates -/

def f1 : Frame := { programIdx := 1, accounts := [⟨0, true, true⟩, ⟨0, true, true⟩], data := [] }
#guard slots f1 = [.acct ⟨0, true, true⟩, .dup 0]
#guard (serialize .v1 mainnet ts0 f1).length = 8 + 10344 + 8 + 8 + 0 + 32
#guard slice (serialize .v1 mainnet ts0 f1) (8 + 10344) 8 = [0, 0, 0, 0, 0, 0, 0, 0]

/-! ## Read-back -/

/-- The result of a read-back, as an error or the accounts. -/
def rb (buf : Bytes) : Except InstrError (List Account) :=
  (readBack .v1 .L 1 buf ts0 lay0).map (·.accts)

-- An unchanged buffer reads back to unchanged accounts.
#guard okWith (rb buf0) ts0.accts
-- The account is writable and owned by `owner1`, not by the program: a debit fails ...
#guard errWith (rb (writeAt buf0 (8 + 72) (u64le 900))) .ExternalAccountLamportSpend
-- ... a credit passes read-back (the pop then fails with `UnbalancedInstruction`) ...
#guard (rb (writeAt buf0 (8 + 72) (u64le 1100))).toBool
-- ... and a change of data fails.
#guard errWith (rb (writeAt buf0 (8 + 88) [7])) .ExternalAccountDataModified
-- Growth beyond 10 KiB over the length at entry fails before the data step.
#guard errWith (rb (writeAt buf0 (8 + 80) (u64le (5 + 10241)))) .InvalidRealloc
-- A write to the input buffer that is undone before exit leaves the account unchanged.
#guard okWith (rb (writeAt (writeAt buf0 (8 + 88) [7]) (8 + 88) [1])) ts0.accts

/-- The same account owned by the program. -/
def ts1 : TxState := initTxState [key1, prog] [{ acct1 with owner := prog }, progAcct]
def buf1 : Bytes := serialize .v1 mainnet ts1 f0
def rb1 (buf : Bytes) : Except InstrError (List Account) :=
  (readBack .v1 .L 1 buf ts1 (layout .v1 mainnet ts1 f0)).map (·.accts)

-- The owner may change the data and grow it by up to 10 KiB.
#guard (rb1 (writeAt (writeAt buf1 (8 + 80) (u64le 7)) (8 + 88) [1, 2, 3, 4, 5, 6, 7])).toBool
-- It may not assign a new owner while the data is not zero.
#guard errWith (rb1 (writeAt buf1 (8 + 40) key1.bytes)) .ModifiedProgramId
-- It may close the account: zero data length and new owner, applied in this order.
#guard (rb1 (writeAt (writeAt buf1 (8 + 80) (u64le 0)) (8 + 40) Ids.systemProgram.bytes)).toBool

/-! ## Errors from r0 -/

#guard InstrError.fromU64 (InstrError.builtin 20) = .InvalidRealloc
#guard InstrError.fromU64 42 = .Custom 42
#guard InstrError.fromU64 (InstrError.builtin 1) = .Custom 0
#guard InstrError.fromU64 (InstrError.builtin 100) = .InvalidError

/-! ## Rent

The active post-execution rule of Agave 4.3.2 allows an account below the rent-exempt
minimum to gain lamports while retaining its size and owner. The inactive-feature
branch retains the preceding rent-state rule. See
[accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/

def small (l : Nat) : Account := ⟨l, List.replicate 10 0, owner1, false, 0⟩

#guard mainnetRent.minBalance 10 = (128 + 10) * 5080
-- The old rule: such an account may lose lamports and may not gain them.
#guard transitionAllowed (rentState mainnetRent (small 1000)) (rentState mainnetRent (small 500))
#guard !transitionAllowed (rentState mainnetRent (small 1000)) (rentState mainnetRent (small 2000))
-- The active rule: such an account may gain lamports and may lose them only by closing.
#guard !relaxedMinBalanceOk mainnetRent (small 1000) (small 500)
#guard relaxedMinBalanceOk mainnetRent (small 1000) (small 2000)
#guard relaxedMinBalanceOk mainnetRent (small 1000) (small 0)

/-! ## The Instructions sysvar -/

def msg0 : Message :=
  { numRequiredSignatures := 1, numReadonlySigned := 0, numReadonlyUnsigned := 1,
    staticKeys := [key1, prog], loadedWritable := [], loadedReadonly := [], recentBlockhash := [],
    instructions := [{ programIdIndex := 1, accounts := [0], data := [9, 8, 7] }] }

-- The count, one offset (4), the entry: one account with flags signer and writable (3),
-- its key, the program id, the data length and the data, and the index 0.
#guard ixSysvarData mainnet msg0 =
  u16le 1 ++ u16le 4 ++ (u16le 1 ++ (3 :: key1.bytes) ++ prog.bytes ++ u16le 3 ++ [9, 8, 7]) ++
    u16le 0
-- An invoked program is demoted to read-only unless loader v3 is among the keys.
#guard !msg0.isWritable mainnet 1
#guard msg0.isWritable mainnet 0

end SolanalibTest.Runtime.Examples
