/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Syscall

@[expose] public section

/-!
# Processed sibling outputs

The source cases follow Agave 4.3.2 `syscalls/src/lib.rs:2061-2104`: translate
only the header on a length mismatch, and all four outputs when the lengths
match. The output macro checks host ranges (`662-711`), while an empty mutable
slice uses a dangling address (`program-runtime/src/memory.rs:65-69`).

Nonempty outputs below lie in disjoint portions of one writable, aligned heap
unless a test explicitly introduces overlap. Account payloads, keys and supplied
primitives remain parameters; the tests do not stand in for binary admission.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.SiblingOutputsTest

def currentFrame : Frame := ⟨1, [], []⟩

def emptySibling : Frame := ⟨0, [], []⟩

def dataSibling : Frame := ⟨0, [], [7]⟩

def accountSibling : Frame := ⟨0, [⟨2, false, false⟩], []⟩

def context : InvCtx :=
  { abi := .v1, cfg := .L, frame := currentFrame, layout := [], heapSize := 32768 }

def invocation (state : TxState) (sibling : Frame) : InvState :=
  { ts := { state with
      stack := [currentFrame]
      trace := [⟨1, sibling⟩, ⟨1, currentFrame⟩] }
    buf := serialize .v1 mainnet state currentFrame
    heapPos := 0
    logs := [] }

def reply (P : Prims) (sv : Sysvars) (stake : Option Pubkey → Nat)
    (state : TxState) (sibling : Frame) (request : SysReq) : Except InstrError SysAns :=
  (sysStep mainnet P sv stake context (invocation state sibling) request).map Prod.fst

def headerDst : Nat := MM_HEAP_START

def programDst : Nat := MM_HEAP_START + 32

def dataDst : Nat := MM_HEAP_START + 64

def accountsDst : Nat := MM_HEAP_START + 80

/-- Ranges follow the order of the four-output `translate_mut!` in the source. -/
def outputs (dataAddr dataLen accountsAddr accountsLen : Nat) : List (Nat × Nat) :=
  [(programDst, 32), (dataAddr, dataLen), (accountsAddr, 34 * accountsLen), (headerDst, 16)]

example : mainnet.memConfig = .L := by rfl
example : mainnet.features.pointerChecks = true := by rfl
example : context.heapSize = 32768 := by rfl
example : headerDst % 8 = 0 := by decide
example : accountsDst + 34 < MM_INPUT_START := by decide
example : accountsDst + 34 - MM_HEAP_START < context.heapSize := by decide

section Replies

variable (P : Prims) (sv : Sysvars) (stake : Option Pubkey → Nat) (state : TxState)

/-- Both empty arrays may start inside the mapped program-ID output. -/
theorem empty_outputs_inside_program_id :
    reply P sv stake state emptySibling
      (.getProcessedSibling 0 0 0 (outputs (programDst + 1) 0 (programDst + 1) 0)) =
      .ok ⟨1, [u64le 0 ++ u64le 0, (state.key 0).bytes, [], []]⟩ := by
  rfl

/-- An empty data output may start inside a nonempty account-meta output. -/
theorem empty_data_inside_account_metas :
    reply P sv stake state accountSibling
      (.getProcessedSibling 0 0 1 (outputs (accountsDst + 1) 0 accountsDst 1)) =
      .ok ⟨1, [u64le 0 ++ u64le 1, (state.key 0).bytes, [],
        (state.key 2).bytes ++ [0, 0]]⟩ := by
  change (Except.ok ⟨1, [u64le 0 ++ u64le 1, (state.key 0).bytes, [],
    ((state.key 2).bytes ++ [0, 0]) ++ []]⟩ : Except InstrError SysAns) = _
  simp only [List.append_nil]

/-- An empty account-meta output may share the start of nonempty data. -/
theorem empty_account_metas_at_data_start :
    reply P sv stake state dataSibling
      (.getProcessedSibling 0 1 0 (outputs dataDst 1 dataDst 0)) =
      .ok ⟨1, [u64le 1 ++ u64le 0, (state.key 0).bytes, [7], []]⟩ := by
  rfl

/-- Empty array translation does not inspect its VM address, even when unmapped. -/
theorem empty_outputs_ignore_unmapped_starts :
    reply P sv stake state emptySibling
      (.getProcessedSibling 0 0 0 (outputs U64_MAX 0 U64_MAX 0)) =
      .ok ⟨1, [u64le 0 ++ u64le 0, (state.key 0).bytes, [], []]⟩ := by
  rfl

/-- The program-ID output still conflicts with a nonempty data output. -/
theorem nonempty_data_overlapping_program_id :
    reply P sv stake state dataSibling
      (.getProcessedSibling 0 1 0 (outputs (programDst + 1) 1 accountsDst 0)) =
      .error .ProgramFailedToComplete := by
  rfl

/-- The nonempty account-meta output still conflicts with the header. -/
theorem nonempty_account_metas_overlapping_header :
    reply P sv stake state accountSibling
      (.getProcessedSibling 0 0 1 (outputs dataDst 0 headerDst 1)) =
      .error .ProgramFailedToComplete := by
  rfl

/-- Ignoring empty arrays does not remove the header/program-ID overlap check. -/
theorem header_overlapping_program_id :
    reply P sv stake state emptySibling
      (.getProcessedSibling 0 0 0
        [(headerDst + 8, 32), (dataDst, 0), (accountsDst, 0), (headerDst, 16)]) =
      .error .ProgramFailedToComplete := by
  rfl

/-- A length mismatch translates and updates only the header. -/
theorem header_mismatch_skips_other_output_overlap :
    reply P sv stake state emptySibling
      (.getProcessedSibling 0 1 1 (outputs programDst 1 programDst 1)) =
      .ok ⟨1, [u64le 0 ++ u64le 0]⟩ := by
  rfl

/-- No preceding sibling at the requested index means no output translation. -/
theorem missing_sibling_skips_output_overlap :
    reply P sv stake state emptySibling
      (.getProcessedSibling 1 1 1 (outputs programDst 1 programDst 1)) =
      .ok ⟨0, []⟩ := by
  rfl

/-- The raw `sol_memcpy_` overlap rejection is independent of sibling outputs. -/
theorem memcpy_nonempty_overlap_unchanged :
    reply P sv stake state emptySibling (.memcpy programDst (programDst + 1) 2) =
      .error .ProgramFailedToComplete := by
  rfl

theorem memcpy_empty_unchanged :
    reply P sv stake state emptySibling (.memcpy programDst programDst 0) = .ok .ok0 := by
  rfl

/-- Return-data outputs keep their existing nonempty overlap rejection. -/
theorem return_data_nonempty_overlap_unchanged :
    reply P sv stake { state with returnData := (state.key 0, [7]) } emptySibling
      (.getReturnData 1 (programDst + 1) programDst) = .error .ProgramFailedToComplete := by
  rfl

end Replies

/-- Empty ranges retain their supplied starts in the raw VM predicate. -/
theorem raw_vm_empty_start_unchanged :
    nonOverlapping programDst 32 (programDst + 1) 0 = false := by
  rfl

end SolanalibTest.Runtime.SiblingOutputsTest
