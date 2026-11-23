/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedHooks
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

/-- The actual clone sequence retains the value of the selected source account. -/
private theorem initialInfoAt_value (types : Types) (args : Onchain.Args)
    (before after : World types.Extra) (index : Nat) (value : AccountInfo.Value)
    (execution : initialInfoAt types args before index (.returned value after)) :
    [args.source, args.mint, args.destination, args.authority][index]? = some value := by
  unfold initialInfoAt at execution
  split at execution
  · rename_i info selected
    obtain ⟨produced, cloned, same⟩ := execution
    cases produced with
    | returned actual current =>
      cases same
      have identity := AccountInfoRc.clone_identity types.rc cloned
      simpa only [identity] using selected
    | unwound impossible _ => cases impossible
    | terminated reason => cases same
  · cases execution

/-- Indexed calls assemble the source prefix even when construction work
changes state between them. Only the returned identity of the callback is needed. -/
private theorem initialInfoPrefix_values (types : Types) (args : Onchain.Args)
    {prior values : List AccountInfo.Value} {before after : World types.Extra}
    (execution : Owned.Array.PrefixTrace types.literalProvider 4 (initialInfoAt types args)
      prior before values after) :
    prior = [args.source, args.mint, args.destination, args.authority].take prior.length →
      values = [args.source, args.mint, args.destination, args.authority].take values.length := by
  induction execution with
  | stop => exact id
  | again _ _ _ _ _ _ _ induction => exact induction
  | next prior values before ready middle after value _ _ expression _ induction =>
    intro current
    apply induction
    have selected := initialInfoAt_value types args ready middle prior.length value expression
    simpa only [List.length_append, List.length_singleton, List.take_add_one, selected,
      Option.toList_some] using congrArg (fun prior => prior ++ [value]) current

/-- A successful initial literal contains exactly source, mint, destination
and authority, including repeated identities. The completion law links the
actual indexed clone results to the current contents of the returned vector. -/
theorem initialInfos_success_current (types : Types) (args : Onchain.Args)
    (law : types.literalProvider.CurrentLaw types.infos)
    (before after : World types.Extra) (resource : types.InfoResource)
    (execution : initialInfos types args before (.returned (.ok resource) after)) :
    types.infos.current after resource =
      some [args.source, args.mint, args.destination, args.authority] := by
  obtain ⟨produced, called, same⟩ := execution
  cases produced with
  | returned actual current =>
    cases same
    obtain ⟨values, ready, trace, count, observed⟩ :=
      Owned.Array.Provider.run_returned_current law called
    have exactValues := initialInfoPrefix_values types args trace rfl
    have sameValues : values = [args.source, args.mint, args.destination, args.authority] := by
      simpa only [count, List.take_succ_cons, List.take_zero] using exactValues
    simpa only [sameValues] using observed
  | unwound reason current => cases same
  | terminated reason => cases same

/-- A successful SDK collection returns a current vector with one element per
source account. The local provider trace and completion law establish this
result without assuming that collection succeeds or preserves unrelated state. -/
theorem collectRefs_success_length (types : Types) (deps : Dependencies types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal)
    (conforms : deps.collect.Conforms protocol)
    (laws : AllocatedCollect.ResourceLaws protocol types.guards)
    (resource : types.InfoResource) (before after : World types.Extra)
    (collected : types.GuardResource) (infos : List AccountInfo.Value)
    (current : types.infos.current before resource = some infos)
    (execution : collectRefs types deps resource before (.returned (.ok collected) after)) :
    ∃ elements, types.guards.current after collected = some elements ∧
      elements.length = infos.length := by
  obtain ⟨_, ⟨actual, observed, rfl⟩, called⟩ := execution
  have same : actual = infos := Option.some.inj (observed.symm.trans current)
  subst actual
  exact AllocatedCollect.Provider.success_length conforms laws
    (infoIterator types resource infos.length) (AllocatedCollect.borrowElement types.raise)
    before after collected called

end Solanalib.Specs.Core.Token.OnchainAllocated
