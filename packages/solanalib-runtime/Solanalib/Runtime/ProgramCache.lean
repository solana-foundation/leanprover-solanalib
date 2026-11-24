/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Ids

@[expose] public section

/-!
# Program-cache modifications

The loader-v3 management operations in Agave 4.3.2 write either a `Closed`
tombstone or an `Unloaded` entry with a deployment slot. The executable program
and its behavior remain an input of the bank. This data-only overlay records
the entries modified during execution without putting program predicates into
the account context.

The overlay has newest-first lookup, corresponding to `modified_entries` in
`ProgramCacheForTxBatch`. Only a successful transaction merges its modifications
into the retained cache used by later transactions of the batch. Fresh cache
loading, including a new batch in the same bank, remains a separate bank-input
correspondence obligation.
-/

namespace Solanalib.Runtime

/-- The two entries written by loader-v3 management in Agave 4.3.2.
`deploy::deploy_program` writes `Unloaded`, not `Loaded`, after verification.
Both variants reject invocation through this retained cache view. -/
inductive ModifiedProgram where
  | closed (deploymentSlot : Nat)
  | unloaded (deploymentSlot : Nat)
  deriving DecidableEq, Repr

/-- The slot stored in a modified cache entry. -/
def ModifiedProgram.deploymentSlot : ModifiedProgram → Nat
  | .closed slot | .unloaded slot => slot

/-- `ProgramCacheEntry::effective_slot`: unloaded programs have one slot of
delayed visibility; the source addition saturates at the maximum `u64`. -/
def ModifiedProgram.effectiveSlot : ModifiedProgram → Nat
  | .closed slot => slot
  | .unloaded slot => min (slot + 1) U64_MAX

/-- The implicit `DelayVisibility` test performed by cache lookup. An unloaded
entry still rejects dispatch when it is not an implicit visibility tombstone. -/
def ModifiedProgram.delayedAt (entry : ModifiedProgram) (slot : Nat) : Bool :=
  decide (entry.deploymentSlot ≤ slot ∧ slot < entry.effectiveSlot)

/-- A finite cache overlay. The most recent write to a program is first; older
writes to that key are shadowed, as in the source map of modified entries. -/
abbrev ProgramCacheChanges := List (Pubkey × ModifiedProgram)

namespace ProgramCacheChanges

/-- Modified-entry lookup, before consulting the initial cache of the bank. -/
def lookup : ProgramCacheChanges → Pubkey → Option ModifiedProgram
  | [], _ => none
  | (key, entry) :: rest, wanted =>
    if wanted = key then some entry else lookup rest wanted

/-- `ProgramCacheForTxBatch::store_modified_entry`, observed through lookup. -/
def store (changes : ProgramCacheChanges) (key : Pubkey) (entry : ModifiedProgram) :
    ProgramCacheChanges := (key, entry) :: changes

@[simp] theorem lookup_nil (key : Pubkey) : lookup [] key = none := rfl

@[simp] theorem lookup_store_same (changes : ProgramCacheChanges) (key : Pubkey)
    (entry : ModifiedProgram) : lookup (store changes key entry) key = some entry := by
  simp [store, lookup]

@[simp] theorem lookup_store_ne (changes : ProgramCacheChanges) (key other : Pubkey)
    (entry : ModifiedProgram) (different : other ≠ key) :
    lookup (store changes key entry) other = lookup changes other := by
  simp [store, lookup, different]

end ProgramCacheChanges

end Solanalib.Runtime
