/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSystemExitWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorSystem

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem

/-- Every version profile and wrapper has a genuine admitted execution. -/
theorem all_wrappers_execute (profile : Profile) (operation : Operation) :
    FamilyHasExecution (family profile operation) (reference profile operation) (Sample.index
      profile) :=
  Sample.execution profile operation

/-- Transfer uses the fixed System program, not the unrelated context program. -/
theorem transfer_program :
    (instruction (Sample.args .boxedModern .transfer)).programId = Instruction.systemProgramId ∧
    (instruction (Sample.args .boxedModern .transfer)).programId.bytes ≠
      (_root_.Solanalib.Runtime.Pubkey.ofNat 9).bytes := by
  exact ⟨rfl, by decide⟩

/-- Meta flags are set by the constructor, independently of AccountInfo flags. -/
theorem transfer_metas :
    metas (Sample.args .boxedModern .transfer) =
      [Instruction.accountMeta (Sample.info 1).key true true,
       Instruction.accountMeta (Sample.info 2).key false true] := rfl

/-- Create requires its second meta to sign, unlike transfer. -/
theorem create_metas :
    metas (Sample.args .inlineLegacy .createAccount) =
      [Instruction.accountMeta (Sample.info 1).key true true,
       Instruction.accountMeta (Sample.info 2).key true true] := rfl

/-- Exact bincode tag, width and little-endian amount for transfer. -/
theorem transfer_bytes :
    (data (Sample.args .boxedLegacy .transfer)).bytes =
      [2, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- the tag and multi-byte space of Allocate are independently checked. -/
theorem allocate_bytes :
    (data (Sample.args .boxedModern .allocate)).bytes =
      [8, 0, 0, 0, 1, 32, 0, 0, 0, 0, 0, 0] := by decide

/-- Owner bytes follow the tag without an invented vector length. -/
theorem assign_bytes :
    (data (Sample.args .boxedLegacy .assign)).bytes =
      [1, 0, 0, 0] ++ (_root_.Solanalib.Runtime.Pubkey.ofNat 23).bytes := rfl

/-- Create uses lamports, space, owner in that order. -/
theorem create_bytes :
    (data (Sample.args .inlineLegacy .createAccount)).bytes =
      [0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 1, 16, 0, 0, 0, 0, 0, 0] ++
        (_root_.Solanalib.Runtime.Pubkey.ofNat 23).bytes := by decide

/-- A same-account transfer preserves both moved owners and both metas. -/
theorem repeated_accounts :
    let input : Args (Sample.index .boxedModern).resources .programId .transfer :=
      { Sample.args .boxedModern .transfer with accounts := (Sample.info 1, Sample.info 1) }
    movedAccounts input = [Sample.info 1, Sample.info 1] ∧
    (metas input).map (·.key) = [(Sample.info 1).key, (Sample.info 1).key] := by
  exact ⟨rfl, rfl⟩

/-- Remaining accounts are cleanup resources, not additional invocation operands. -/
theorem request_operands :
    request (Sample.afterBuild (Sample.before .boxedModern) (Sample.args .boxedModern .transfer))
      (Sample.args .boxedModern .transfer) (Sample.builtValue (Sample.before .boxedModern)) =
      some ⟨instruction (Sample.args .boxedModern .transfer), [Sample.info 1, Sample.info 2],
        [[[1, 2], [], [1, 2]], [[255]]]⟩ := Sample.request_exact _ _

/-- An altered meta order fails exact request correspondence. -/
theorem reject_swapped_accounts :
    request (Sample.afterBuild (Sample.before .boxedModern) (Sample.args .boxedModern .transfer))
      (Sample.args .boxedModern .transfer) (Sample.builtValue (Sample.before .boxedModern)) ≠
      some ⟨instruction (Sample.args .boxedModern .transfer), [Sample.info 2, Sample.info 1],
        [[[1, 2], [], [1, 2]], [[255]]]⟩ := by
  rw [Sample.request_exact]
  intro wrong
  have impossible := congrArg (fun value : Option (CpiRequest.Request AccountInfo.Value) =>
    value.map (fun current => current.accounts.map (fun account => account.lamports.cell))) wrong
  contradiction

/-- A retired byte resource has no fabricated default instruction. -/
theorem unreadable_instruction :
    request (Sample.dropByte
        (Sample.afterBuild (Sample.before .boxedModern) (Sample.args .boxedModern .transfer)) 0)
      (Sample.args .boxedModern .transfer) (Sample.builtValue (Sample.before .boxedModern)) = none
        := by
  decide

/-- Constructor allocation, serialization and two vector drops all occur, in order. -/
theorem constructor_cleanup_events :
    (Sample.afterScope (Sample.afterInvoke (Sample.before .boxedModern)
        (Sample.args .boxedModern .transfer)) (Sample.args .boxedModern .transfer)
      (Sample.builtValue (Sample.before .boxedModern))).construction.events = [10, 20, 40, 41] :=
        rfl

/-- Cleanup retains repeated remaining-account occurrences and drops each Rc field. -/
theorem modern_drop_events :
    (Sample.afterScope (Sample.afterInvoke (Sample.before .boxedModern)
        (Sample.args .boxedModern .transfer)) (Sample.args .boxedModern .transfer)
      (Sample.builtValue (Sample.before .boxedModern))).rcEvents =
      [.drop .lamports ⟨2⟩, .drop .data ⟨3⟩,
       .drop .lamports ⟨4⟩, .drop .data ⟨5⟩,
       .drop .lamports ⟨6⟩, .drop .data ⟨7⟩,
       .drop .lamports ⟨2⟩, .drop .data ⟨3⟩,
       .drop .lamports ⟨6⟩, .drop .data ⟨7⟩] := rfl

/-- The legacy context additionally owns its program account. -/
theorem legacy_program_drop :
    (Sample.afterScope (Sample.afterInvoke (Sample.before .inlineLegacy)
        (Sample.args .inlineLegacy .allocate)) (Sample.args .inlineLegacy .allocate)
      (Sample.builtValue (Sample.before .inlineLegacy))).rcEvents.drop 8 =
      [.drop .lamports ⟨18⟩, .drop .data ⟨19⟩] := rfl

/-- Vector destruction reads current contents after provider mutation. -/
theorem current_remaining_drop :
    (Sample.dropRemaining
      { Sample.before .boxedModern with remaining := [some [Sample.info 4]] } 0).rcEvents =
      [.drop .lamports ⟨8⟩, .drop .data ⟨9⟩] := rfl

/-- Legacy String-bearing errors retain the exact existing String handle. -/
theorem legacy_owned_error :
    AnchorErrorOperations.currentPayload .boxed (Sample.errors .boxedLegacy)
      (Sample.afterConversion .boxedLegacy (Sample.before .boxedLegacy) (.borshIoError 7))
      (Sample.convertedError .boxedLegacy (Sample.before .boxedLegacy) (.borshIoError 7)) =
      some (.program ⟨.borshIoError 7, none, none⟩) :=
  Sample.converted_payload .boxedLegacy (Sample.before .boxedLegacy) (.borshIoError 7)

/-- Anchor 0.27 has no error-box allocation. -/
theorem inline_error_no_box :
    Sample.afterConversion .inlineLegacy (Sample.before .inlineLegacy) (.borshIoError 7) =
      Sample.before .inlineLegacy := rfl

/-- Modern Anchor allocates one box, while preserving the complete program error. -/
theorem boxed_error_allocation :
    (Sample.afterConversion .boxedModern (Sample.before .boxedModern) (.custom 77)).boxes =
      [some (.program ⟨.custom 77, none, none⟩)] := rfl

/-- Every opaque returned error follows the registered execution and cleanup relation. -/
theorem returned_error (profile : Profile) (operation : Operation) (error : profile.Program Nat) :
    run (Sample.errorIndex profile error) (Sample.before profile) (Sample.args profile operation)
      (.returned (.error (Sample.convertedError profile
          (Sample.afterInvoke (Sample.before profile) (Sample.args profile operation)) error))
        (Sample.afterScope (Sample.afterConversion profile
            (Sample.afterInvoke (Sample.before profile) (Sample.args profile operation)) error)
          (Sample.args profile operation) (Sample.builtValue (Sample.before profile)))) :=
  Sample.run_error profile operation error

/-- Unwinding is not silently converted to an ordinary error. -/
theorem opaque_unwind (profile : Profile) (operation : Operation) :
    run (Sample.unwindIndex profile 91) (Sample.before profile) (Sample.args profile operation)
      (.unwound (91 : Nat) (Sample.afterScope
        (Sample.afterInvoke (Sample.before profile) (Sample.args profile operation))
        (Sample.args profile operation) (Sample.builtValue (Sample.before profile)))) :=
  Sample.run_unwind profile operation 91

/-- A terminal provider has no invented after-state or cleanup success. -/
theorem opaque_terminal (profile : Profile) (operation : Operation) :
    run (Sample.terminalIndex profile 92) (Sample.before profile) (Sample.args profile operation)
      (.terminated (92 : Nat)) := Sample.run_terminal profile operation 92

/-- The full wrapper cannot manufacture a finite exit for a provider without one. -/
theorem absent_provider_exit (profile : Profile) (operation : Operation)
    (outcome : Outcome (Sample.State (profile.Program Nat))
      (Except (Error (Sample.index profile)) Unit) Nat Nat) :
    ¬ run (Sample.noExitIndex profile) (Sample.before profile) (Sample.args profile operation)
      outcome :=
  Sample.no_fabricated_exit profile operation outcome

end SolanalibTest.Specs.Core.AnchorSystem
