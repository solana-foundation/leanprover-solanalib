/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserializeSDK
public import Solanalib.Specs.Core.EntryDeserializePinocchio
public import Solanalib.Specs.Core.EntryDeserializePinocchioAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SolanalibTest.Specs.Core.EntryDeserialize

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.EntryDeserialize

/-- The test serializer deliberately keeps arbitrary flag bytes and nonzero padding/reserve
controls available. It is not used by the registered parser or contracts. -/
def encodeAccount (data : Solanalib.Runtime.Bytes) (balance : Nat) : Solanalib.Runtime.Bytes :=
  [255, 2, 0, 9] ++ List.replicate 4 0 ++ List.replicate 32 7 ++
    List.replicate 32 8 ++ Solanalib.Runtime.u64le balance ++ Solanalib.Runtime.u64le data.length
      ++ data ++
    List.replicate 10240 0 ++ List.replicate ((8 - data.length % 8) % 8) 0 ++
      Solanalib.Runtime.u64le 19

/-- A duplicate-of-duplicate and equal-key distinct account are both present. -/
def bytes : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.u64le 4 ++ encodeAccount [10, 20, 30] 42 ++ [0, 1, 2, 3, 4, 5, 6, 7] ++
    encodeAccount [] 99 ++ [1, 7, 6, 5, 4, 3, 2, 1] ++ Solanalib.Runtime.u64le 3 ++ [4, 5, 6] ++
      List.replicate 32 9

def accountA : Account :=
  ⟨8, 2, 0, 9, 0, Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 7),
    Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 8), 42, [10, 20, 30],
    List.replicate 10240 0, List.replicate 5 0, 19⟩

def accountB : Account :=
  ⟨10360, 2, 0, 9, 0, Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 7),
    Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 8), 99, [],
    List.replicate 10240 0, [], 19⟩

def parsed : Parsed :=
  ⟨[⟨8, none, [], accountA⟩, ⟨10352, some 0, [1, 2, 3, 4, 5, 6, 7], accountA⟩,
    ⟨10360, none, [], accountB⟩, ⟨20696, some 1, [7, 6, 5, 4, 3, 2, 1], accountA⟩],
    20704, [4, 5, 6], 20715, Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 9), 20747⟩

theorem parse_bytes : parse bytes = some parsed := by decide +kernel

theorem parsed_count : parsed.slots.length = 4 := by decide
def pinBefore : Pinocchio.State := ⟨bytes, [none, some 999, some 777, some 666, some 555]⟩
def pinAfter : Pinocchio.State := ⟨bytes, [some 8, some 8, some 10360, some 8, some 555]⟩

theorem pin_retains_suffix :
    Pinocchio.execute 5 pinBefore = some (⟨parsed.views, 4⟩, pinAfter) := by
  simp [Pinocchio.execute, pinBefore, parse_bytes, pinAfter]
  decide

theorem pin_skips_to_instruction :
    Pinocchio.execute 2 ⟨bytes, [none, none]⟩ =
      some (⟨parsed.views, 2⟩, ⟨bytes, [some 8, some 8]⟩) := by
  simp [Pinocchio.execute, parse_bytes]
  decide

theorem pin_nonzero_flags :
    parsed.accounts.map (fun account => (account.signer != 0, account.executable != 0)) =
      [(true, true), (true, true), (true, true), (true, true)] := by decide

theorem pin_zero_capacity_rejected : ¬Pinocchio.Admitted 0 ⟨bytes, []⟩ := by
  intro h
  obtain ⟨p, hp, empty⟩ := Pinocchio.zero_capacity_requires_empty _ h
  rw [parse_bytes] at hp
  cases hp
  have count := parsed_count
  rw [empty] at count
  contradiction

def sdkOutcome := SDK.process SDK.traceIndex parsed.views 0 parsed.slots []
  { SDK.emptyState bytes with vectors := [[]], allocator := [⟨.vector 4, bytes⟩] }

def sdkAfter : SDK.State (List SDK.AllocationRequest) :=
  match sdkOutcome with
  | some (.returned _ after) => after
  | _ => SDK.emptyState []

theorem sdk_counts : sdkAfter.rcStrong = [3, 3, 1, 1] := by decide +kernel
theorem sdk_lamport_aliases :
    (sdkAfter.vectors.getD 0 []).map (fun info => info.value.lamports.cell) = [0, 0, 2, 0] := by
      decide +kernel
theorem sdk_data_aliases :
    (sdkAfter.vectors.getD 0 []).map (fun info => info.value.data.cell) = [1, 1, 3, 1] := by
      decide +kernel
theorem sdk_owner_aliases :
    (sdkAfter.vectors.getD 0 []).map (fun info => info.value.ownerRef.id) = [0, 0, 1, 0] := by
      decide +kernel
theorem sdk_allocation_order :
    sdkAfter.allocator.map SDK.AllocationRequest.site =
      [.vector 4, .lamports 8, .data 8, .lamports 10360, .data 10360] := by decide +kernel
theorem sdk_write_between_allocations :
    (sdkAfter.allocator.map fun request => word? request.input 12 4) =
      [some 0, some 0, some 3, some 3, some 3] := by decide +kernel

def pinAccounts := PinocchioAccounts.install parsed

theorem pin_account_bridge_aliases :
    (pinAccounts.map fun world => world.handles.map (·.cell)) = some [0, 0, 1, 0] := by
  decide +kernel

theorem pin_account_bridge_data :
    (PinocchioAccounts.input accountA).data.backing = [10, 20, 30] ++ List.replicate 10240 0 ∧
    (PinocchioAccounts.input accountA).data.entryLen = 3 ∧
    (PinocchioAccounts.input accountA).data.resizeDelta = 0 := by decide +kernel

theorem pin_signed_delta_preserved :
    (PinocchioAccounts.input { accountA with reserved := 4294967295 }).data.resizeDelta = -1 ∧
    (PinocchioAccounts.input { accountA with reserved := 4294967295 }).data.entryLen = 4 := by
  decide +kernel

/-- A provider failure at the data allocation propagates a terminal, after the header
write request observation. It is not a returned empty vector or an unwind. -/
def failData : SDK.Index where
  Aux := Unit
  Terminal := SDK.Allocation
  allocate := fun _ request =>
    if request.site = .data 8 then some (.terminated request.site)
    else some (.returned () ())

theorem sdk_allocation_failure :
    SDK.execute failData ⟨bytes, ⟨⟨[], []⟩, [], []⟩, [], [], ()⟩ =
      some (.terminated (.data 8)) := by
  simp [SDK.execute, parse_bytes, parsed, SDK.allocateThen, failData]
  rfl

end SolanalibTest.Specs.Core.EntryDeserialize
