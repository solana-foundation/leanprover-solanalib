/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedTypes

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.PdaAdmission

/-- At a representable input of the actual source wrapper, every successful
primitive reply initializes the address output. This gate precedes decoding:
it mentions neither a completed find result nor a callback post-state law.
Nonzero replies, unwind and terminal exits impose no output obligation. -/
def Ready (types : Types) : Prop :=
  ∀ (before : World types.Extra) (inputs : Address.Syscall.PdaInputs), inputs.Bounded →
    ∀ (reply : Address.Syscall.PdaReply) (after : World types.Extra),
    types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.returned reply after) →
    reply.status = 0 → ∃ address, reply.addressOutput = some address

/-- An actual initialized success is decoded and returned with exactly its
key, bump and syscall state. The source operations remain their raw relations. -/
theorem initialized_success {types : Types} {before after : World types.Extra}
    {inputs : Address.Syscall.PdaInputs} (bounded : inputs.Bounded)
    {reply : Address.Syscall.PdaReply}
    (called : types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.returned reply after))
    (zero : reply.status = 0) {address : Address.Value}
    (initialized : reply.addressOutput = some address) :
    types.findPda before inputs (.returned (address, reply.bumpOutput) after) := by
  refine ⟨bounded, .returned (some (address, reply.bumpOutput)) after, ?_, rfl⟩
  apply Address.Syscall.tryRun_returned types.pdaSyscall before after inputs reply
    (some (address, reply.bumpOutput)) called
  simp only [Address.Syscall.decodePda, zero, ↓reduceIte]
  exact ⟨address, initialized, rfl⟩

/-- Admission consumes a real status-zero primitive return and supplies its
full source-wrapper continuation, without assuming that wrapper has an exit. -/
theorem Ready.success_retain {types : Types} (ready : Ready types)
    {before after : World types.Extra} {inputs : Address.Syscall.PdaInputs}
    (bounded : inputs.Bounded) {reply : Address.Syscall.PdaReply}
    (called : types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.returned reply after))
    (zero : reply.status = 0) :
    ∃ address, reply.addressOutput = some address ∧
      types.findPda before inputs (.returned (address, reply.bumpOutput) after) := by
  obtain ⟨address, initialized⟩ := ready before inputs bounded reply after called zero
  exact ⟨address, initialized, initialized_success bounded called zero initialized⟩

/-- A nonzero reply reaches the exact local panic site in the returned state of the syscall. Each
actual downstream panic exit is retained; no panic
termination or initialized failure output is assumed. -/
theorem nonzero_retain {types : Types} {before after : World types.Extra}
    {inputs : Address.Syscall.PdaInputs} (bounded : inputs.Bounded)
    {reply : Address.Syscall.PdaReply}
    (called : types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.returned reply after))
    (nonzero : reply.status ≠ 0)
    {produced : Outcome (World types.Extra) Empty types.Unwind types.Terminal}
    (raised : types.raise after .noViableProgramAddress produced) :
    types.findPda before inputs
      (Outcome.map (fun impossible : Empty => nomatch impossible) produced) := by
  refine ⟨bounded, .returned none after, ?_, ?_⟩
  · apply Address.Syscall.tryRun_returned types.pdaSyscall before after inputs reply none called
    simp only [Address.Syscall.decodePda, nonzero, ↓reduceIte]
  · exact ⟨produced, raised, rfl⟩

/-- A syscall unwind bypasses decoding and the local panic, preserving its
actual reason and state with no unused output-initialization premise. -/
theorem unwind_retain {types : Types} {before after : World types.Extra}
    {inputs : Address.Syscall.PdaInputs} (bounded : inputs.Bounded) {reason : types.Unwind}
    (called : types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.unwound reason after)) :
    types.findPda before inputs (.unwound reason after) :=
  ⟨bounded, .unwound reason after, ⟨.unwound reason after, called, rfl⟩, rfl⟩

/-- A direct terminal syscall exit also bypasses decoding and local panic;
there is no post-state or fabricated continuation effect. -/
theorem terminal_retain {types : Types} {before : World types.Extra}
    {inputs : Address.Syscall.PdaInputs} (bounded : inputs.Bounded) {reason : types.Terminal}
    (called : types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.terminated reason)) :
    types.findPda before inputs (.terminated reason) :=
  ⟨bounded, .terminated reason, ⟨.terminated reason, called, rfl⟩, rfl⟩

end Solanalib.Specs.Core.Token.OnchainAllocated.PdaAdmission
