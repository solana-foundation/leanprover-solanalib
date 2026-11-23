/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedLiteral

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.LiteralAdmission

/-- The only two owned AccountInfo literals in this source preparation. -/
inductive Kind where
  /-- The caller clones four original arguments. -/
  | initial
  /-- The Execute helper moves four arguments and clones validation. -/
  | execute
  deriving DecidableEq

/-- The exact number of source expressions at each literal site. -/
def Kind.count : Kind → Nat
  | .initial => 4
  | .execute => 5

/-- Admission for the local command and cleanup checks, restricted to the
two source counts. It assumes neither completion nor an expression/drop exit.
Returned storage contents have separate ordinary-resource obligations. -/
structure Ready (types : Types) : Prop where
  /-- An actual evaluate request still has an expression in the literal. -/
  evaluate_bound : ∀ (kind : Kind) before values after,
    values.length ≤ kind.count →
    types.infoLiteral.work before (kind.count, values) (.returned .evaluate after) →
      values.length < kind.count
  /-- An actual finish request has exactly the completed source count. -/
  finish_count : ∀ (kind : Kind) before values after,
    values.length ≤ kind.count →
    types.infoLiteral.work before (kind.count, values) (.returned .finish after) →
      values.length = kind.count
  /-- The selected cleanup order contains each evaluated occurrence once. -/
  cleanup_order : ∀ (kind : Kind) state (values : List AccountInfo.Value), values.length ≤
    kind.count →
    (types.infoLiteral.cleanupOrder state values).Perm (List.finRange values.length)

/-- A general mathematical constructor interpretation can discharge the
smaller source-count gate using its existing three control laws. -/
theorem Ready.of_conforms {types : Types} (law : types.infoLiteral.Conforms) : Ready types :=
  ⟨fun kind _ _ _ bounded called => law.evaluate_bound _ kind.count _ _ bounded called,
    fun kind _ _ _ bounded called => law.finish_count _ kind.count _ _ bounded called,
    fun _ _ _ _ => law.cleanup_permutation _ _⟩

/-- An actual evaluate command selects a real initial source expression.
Every actual Rc-clone exit at that selection is then the exact expression
exit; the provider cannot request the out-of-range empty branch. -/
theorem Ready.initial_expression {types : Types} (ready : Ready types)
    {args : Onchain.Args} {before during : World types.Extra} {values : List AccountInfo.Value}
    (bounded : values.length ≤ 4)
    (called : types.infoLiteral.work before (4, values) (.returned .evaluate during)) :
    ∃ info, [args.source, args.mint, args.destination, args.authority][values.length]? = some info ∧
      ∀ produced, AccountInfoRc.lift (AccountInfoRc.cloneCall types.rc) during info produced →
        initialInfoAt types args during values.length produced := by
  have bound := ready.evaluate_bound .initial before values during bounded called
  have within : values.length < [args.source, args.mint, args.destination, args.authority].length :=
    by simpa only [Kind.count, List.length_cons, List.length_nil] using bound
  let info := [args.source, args.mint, args.destination, args.authority][values.length]
  have selected : [args.source, args.mint, args.destination, args.authority][values.length]? =
      some info := List.getElem?_eq_some_iff.mpr ⟨within, rfl⟩
  refine ⟨info, selected, ?_⟩
  intro produced expression
  simpa only [initialInfoAt, selected] using expression

/-- Each actual normal expression exit extends the same raw trace in source
order. The rest is an actual downstream continuation, not a termination law. -/
theorem Ready.evaluate_returned {types : Types} (ready : Ready types) (kind : Kind)
    {evaluate : Callback.Run (World types.Extra) Nat AccountInfo.Value
      types.Unwind types.Terminal}
    {values : List AccountInfo.Value} {before during after : World types.Extra}
    {value : AccountInfo.Value}
    {final : Outcome (World types.Extra) types.InfoResource
      (Owned.Array.Failure × types.Unwind) types.Terminal}
    (bounded : values.length ≤ kind.count)
    (called : types.infoLiteral.work before (kind.count, values) (.returned .evaluate during))
    (expression : evaluate during values.length (.returned value after))
    (rest : Owned.Array.Trace types.literalProvider kind.count evaluate (values ++ [value]) after
      final) :
    Owned.Array.Trace types.literalProvider kind.count evaluate values before final :=
  .next values before during after value final
    (ready.evaluate_bound kind before values during bounded called) called expression rest

/-- An actual terminal expression is retained after an admitted evaluate
command; it does not run constructor cleanup. -/
theorem Ready.evaluate_terminal {types : Types} (ready : Ready types) (kind : Kind)
    {evaluate : Callback.Run (World types.Extra) Nat AccountInfo.Value
      types.Unwind types.Terminal}
    {values : List AccountInfo.Value} {before during : World types.Extra}
    {reason : types.Terminal} (bounded : values.length ≤ kind.count)
    (called : types.infoLiteral.work before (kind.count, values) (.returned .evaluate during))
    (expression : evaluate during values.length (.terminated reason)) :
    Owned.Array.Trace types.literalProvider kind.count evaluate values before (.terminated reason)
      :=
  .evaluateTerminal values before during reason
    (ready.evaluate_bound kind before values during bounded called) called expression

/-- A finite finish command and actual constructor return complete the raw
trace at the exact count, with its real resource and state. -/
theorem Ready.finish_returned {types : Types} (ready : Ready types) (kind : Kind)
    {evaluate : Callback.Run (World types.Extra) Nat AccountInfo.Value
      types.Unwind types.Terminal}
    {values : List AccountInfo.Value} {before during after : World types.Extra}
    {resource : types.InfoResource} (bounded : values.length ≤ kind.count)
    (called : types.infoLiteral.work before (kind.count, values) (.returned .finish during))
    (finished : types.infoLiteral.finish during values (.returned resource after)) :
    Owned.Array.Trace types.literalProvider kind.count evaluate values before (.returned resource
      after) :=
  .finishReturn values before during after resource
    (ready.finish_count kind before values during bounded called) called finished

/-- A terminal finish exit also survives the count check and bypasses every
element/storage destructor. -/
theorem Ready.finish_terminal {types : Types} (ready : Ready types) (kind : Kind)
    {evaluate : Callback.Run (World types.Extra) Nat AccountInfo.Value
      types.Unwind types.Terminal}
    {values : List AccountInfo.Value} {before during : World types.Extra}
    {reason : types.Terminal} (bounded : values.length ≤ kind.count)
    (called : types.infoLiteral.work before (kind.count, values) (.returned .finish during))
    (finished : types.infoLiteral.finish during values (.terminated reason)) :
    Owned.Array.Trace types.literalProvider kind.count evaluate values before (.terminated reason)
      :=
  .finishTerminal values before during reason
    (ready.finish_count kind before values during bounded called) called finished

/-- The cleanup-order gate forwards each actual destructor/policy exit into
the annotated close relation of the source. It does not assume those exits exist. -/
theorem Ready.close {types : Types} (ready : Ready types) (kind : Kind)
    {values : List AccountInfo.Value} {site : Owned.Array.FailureSite}
    {before : World types.Extra} {reason : types.Unwind}
    {pending : Outcome (World types.Extra) types.InfoResource types.Unwind types.Terminal}
    (bounded : values.length ≤ kind.count)
    (cleaned : Owned.cleanup types.doubleUnwind
      (types.literalProvider.cleanupActions values (types.infoLiteral.cleanupOrder before values))
      (.unwound reason before) pending) :
    types.literalProvider.close values site before reason
      (Owned.Array.annotate ⟨values.length, site⟩ pending) :=
  ⟨ready.cleanup_order kind before values bounded, pending, cleaned, rfl⟩

/-- A real work unwind retains every actual source cleanup exit, including
a destructor-induced terminal exit, with the exact completed prefix. -/
theorem Ready.work_unwind {types : Types} (ready : Ready types) (kind : Kind)
    {evaluate : Callback.Run (World types.Extra) Nat AccountInfo.Value
      types.Unwind types.Terminal}
    {values : List AccountInfo.Value} {before after : World types.Extra} {reason : types.Unwind}
    {pending : Outcome (World types.Extra) types.InfoResource types.Unwind types.Terminal}
    (bounded : values.length ≤ kind.count)
    (called : types.infoLiteral.work before (kind.count, values) (.unwound reason after))
    (cleaned : Owned.cleanup types.doubleUnwind
      (types.literalProvider.cleanupActions values (types.infoLiteral.cleanupOrder after values))
      (.unwound reason after) pending) :
    Owned.Array.Trace types.literalProvider kind.count evaluate values before
      (Owned.Array.annotate ⟨values.length, .work⟩ pending) :=
  .workUnwind values before after reason _ called (ready.close kind bounded cleaned)

/-- A real finish unwind uses both the completion-count and cleanup-order
guarantees before forwarding each actual downstream cleanup exit. -/
theorem Ready.finish_unwind {types : Types} (ready : Ready types) (kind : Kind)
    {evaluate : Callback.Run (World types.Extra) Nat AccountInfo.Value
      types.Unwind types.Terminal}
    {values : List AccountInfo.Value} {before during after : World types.Extra} {reason :
      types.Unwind}
    {pending : Outcome (World types.Extra) types.InfoResource types.Unwind types.Terminal}
    (bounded : values.length ≤ kind.count)
    (called : types.infoLiteral.work before (kind.count, values) (.returned .finish during))
    (finished : types.infoLiteral.finish during values (.unwound reason after))
    (cleaned : Owned.cleanup types.doubleUnwind
      (types.literalProvider.cleanupActions values (types.infoLiteral.cleanupOrder after values))
      (.unwound reason after) pending) :
    Owned.Array.Trace types.literalProvider kind.count evaluate values before
      (Owned.Array.annotate ⟨values.length, .finish⟩ pending) :=
  .finishUnwind values before during after reason _
    (ready.finish_count kind before values during bounded called) called finished
    (ready.close kind bounded cleaned)

end Solanalib.Specs.Core.Token.OnchainAllocated.LiteralAdmission
