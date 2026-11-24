/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedTypes
public import Solanalib.Specs.Core.OwnedArrayProgress

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

open AllocatedControl

/-- Literal construction uses primitive work/completion/storage operations,
but its element destructor is the ordinary AccountInfo Rc sequence and its
double-unwind policy is the surrounding source policy. The duplicate generic
provider fields do not replace either local SDK operation. -/
def Types.literalProvider (types : Types) :
    Owned.Array.Provider (World types.Extra) AccountInfo.Value types.InfoResource
      types.Unwind types.Terminal :=
  { types.infoLiteral with
    drop := fun state info => AccountInfoRc.lift (AccountInfoRc.dropCall types.rc) state info
    double := types.doubleUnwind }

/-- The initial four literal expressions clone source, mint, destination and
authority in that exact index order. Constructor work may happen before or
between them; the callback receives its actual state. -/
def initialInfoAt (types : Types) (args : Onchain.Args) :
    Callback.Run (World types.Extra) Nat AccountInfo.Value types.Unwind types.Terminal :=
  fun state index outcome =>
    match [args.source, args.mint, args.destination, args.authority][index]? with
    | some info => AccountInfoRc.lift (AccountInfoRc.cloneCall types.rc) state info outcome
    | none => False

/-- The initial literal constructor owns its evaluated clones. Original
function arguments remain in the surrounding scope of the caller. No allocation
ordering relative to expression evaluation is assumed by the SDK model. -/
def initialInfos (types : Types) (args : Onchain.Args) : Run types types.InfoResource :=
  perform fun state => types.literalProvider.run 4 (initialInfoAt types args) state

/-- the first four literal expressions of Execute move the arguments of the helper;
the fifth creates one validation-account clone. Pure moves have no callbacks,
and the concrete Rc clone has no unwind exit. -/
def executeInfoAt (types : Types) (args : Onchain.Args) (validation : AccountInfo.Value) :
    Callback.Run (World types.Extra) Nat AccountInfo.Value types.Unwind types.Terminal :=
  fun state index outcome =>
    match index with
    | 0 => outcome = .returned args.source state
    | 1 => outcome = .returned args.mint state
    | 2 => outcome = .returned args.destination state
    | 3 => outcome = .returned args.authority state
    | 4 => AccountInfoRc.lift (AccountInfoRc.cloneCall types.rc) state validation outcome
    | _ => False

/-- Lifting the fixed Rc outcome vocabulary cannot introduce an unwind. -/
theorem rcLift_no_unwind (types : Types) (info : AccountInfo.Value)
    (before after : World types.Extra) (reason : types.Unwind)
    (execution : AccountInfoRc.lift (Unwind := types.Unwind)
      (AccountInfoRc.cloneCall types.rc) before info (.unwound reason after)) : False := by
  obtain ⟨produced, _, same⟩ := execution
  cases produced with
  | returned _ _ => cases same
  | unwound impossible _ => exact nomatch impossible
  | terminated _ => cases same

/-- No Execute expression can unwind after partially consuming an original
argument. Consequently the completed count exactly determines the originals
still owned by the surrounding source scope on a surviving constructor unwind. -/
theorem executeInfoAt_no_unwind (types : Types) (args : Onchain.Args)
    (validation : AccountInfo.Value) (before after : World types.Extra)
    (index : Nat) (reason : types.Unwind)
    (execution : executeInfoAt types args validation before index (.unwound reason after)) : False
      := by
  unfold executeInfoAt at execution
  split at execution
  all_goals first
    | exact rcLift_no_unwind types validation before after reason execution
    | cases execution

/-- Every surviving Execute-constructor unwind reports a completed prefix
within the five source expressions, and cannot originate in an expression.
These facts justify the remaining-original suffix used by the enclosing scope. -/
theorem executeLiteral_unwind_progress (types : Types) (args : Onchain.Args)
    (validation : AccountInfo.Value) (before after : World types.Extra)
    (failure : Owned.Array.Failure) (reason : types.Unwind)
    (execution : types.literalProvider.runDetailed 5 (executeInfoAt types args validation)
      before (.unwound (failure, reason) after)) :
    failure.completed ≤ 5 ∧ failure.site ≠ .evaluate := by
  have progress := Owned.Array.Trace.unwound_progress execution rfl (Nat.zero_le 5)
  refine ⟨progress.2.1, ?_⟩
  exact Owned.Array.Trace.unwound_not_evaluate
    (fun current index why final =>
      executeInfoAt_no_unwind types args validation current final index why) execution rfl

/-- Original arguments not yet moved into the partial array of Execute remain
caller-owned and drop in reverse declaration order, after the constructor
and all earlier locals of the inner source block have been cleaned. -/
def executeRemainder (types : Types) (args : Onchain.Args) (completed : Nat) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  ([args.source, args.mint, args.destination, args.authority].drop completed).reverse.map
    (dropInfo types)

/-- the literal constructor of Execute exposes progress for exact exceptional
cleanup: its evaluated elements/storage first, the earlier instruction local
next, and then still-unmoved arguments from the outer function scope. On
success the instruction remains owned and all evaluated owners transfer to
the vector. Terminal exits bypass every remaining cleanup. -/
def executeInfos (types : Types) (args : Onchain.Args) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    Run types types.InfoResource :=
  fun before outcome => ∃ detailed,
    types.literalProvider.runDetailed 5 (executeInfoAt types args validation) before detailed ∧
    match detailed with
    | .returned resource after => outcome = .returned (.ok resource) after
    | .unwound (failure, reason) after =>
      Owned.cleanup types.doubleUnwind
        (instructionDrops types instruction ++ executeRemainder types args failure.completed)
        (.unwound reason after) outcome
    | .terminated reason => outcome = .terminated reason

end Solanalib.Specs.Core.Token.OnchainAllocated
