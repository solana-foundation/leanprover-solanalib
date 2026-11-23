/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorLang.Views
import SolanalibTest.Conformance.Library.Families.AnchorViews.Lamports
import SolanalibTest.Conformance.Library.Families.AnchorViews.Graph
import SolanalibTest.Conformance.Library.Families.AnchorViews.Admission

/-! Each selected relation and admission below names the versioned registered
contract. Owned AccountInfo fields select the separate 0.27 model. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

theorem returnsGraph {S A V U T : Type} (run : S → A → V × S) (s : S) (args : A) :
    PGraph (returnsOf (Unwind := U) (Terminal := T) run s args)
      (some (.returned (run s args).1 (run s args).2)) := by
  intro o
  exact (returnsOf_iff run s args o).trans ⟨fun h => congrArg some h, fun h => Option.some.inj h⟩

def projectionTypes : ProjectionTypes := ⟨Nat, Effects⟩

/-- One selected registered relation, its executable graph, and its decided
admission. Concrete values below mention exactly one source contract. -/
structure Binding (S A V U T : Type) where
  model : String
  run : S → A → Outcome S V U T → Prop
  value : S → A → Option (Outcome S V U T)
  graph : ∀ s a, PGraph (run s a) (value s a)
  ready : S → A → Bool

def keyReady (s : World Nat Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p := (accounts.wrapper_key_contract.contract
    projectionTypes).requires s g) _ (readableB_iff s.1 g)

def mutableReady (debug : Bool) (s : World Nat Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p := (accounts.account.Account.deref_mut_contract.contract
    (mutableTypes debug)).requires s g) _ (writableB_iff s.1 g)

def infoReadyBorrowed (s : World Nat Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p := (accounts.borrowed_info_ref_contract.contract
    projectionTypes).requires s g)
    _ (readableB_iff s.1 g)

def infoBindingBorrowed : Binding (World Nat Effects) Borrow.Guard InfoRef Empty Empty where
  model := "Solanalib.Specs.AnchorLang.accounts.borrowed_info_ref_run"
  run := accounts.borrowed_info_ref_run projectionTypes
  value := (fun s g => some (.returned (infoReference .borrowed s g).1 (infoReference .borrowed s
    g).2))
  graph := fun s g => returnsGraph _ s g
  ready := infoReadyBorrowed

def cloneReadyBorrowed (mode : Nat) (s : World Nat Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p :=
    (accounts.account.Account.clone_borrowed_info_contract.contract
    (cloneTypes .borrowed mode)).requires s g)
    _ (readableB_iff s.1 g)

def cloneBindingBorrowed (mode : Nat) : Binding (World Nat Effects) Borrow.Guard Borrow.Handle
  String String where
  model := "Solanalib.Specs.AnchorLang.accounts.account.Account.clone_borrowed_info_run"
  run := accounts.account.Account.clone_borrowed_info_run (cloneTypes
    .borrowed mode)
  value := cloneFn .borrowed mode
  graph := clone_graph .borrowed mode
  ready := cloneReadyBorrowed mode

def infoCloneReadyBorrowed (s : World Unit Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p := (accounts.clone_borrowed_info_contract.contract
    (infoCloneTypes .borrowed)).requires s g)
    _ (readableB_iff s.1 g)

def infoCloneBindingBorrowed : Binding (World Unit Effects) Borrow.Guard Borrow.Handle Empty String
  where
  model := "Solanalib.Specs.AnchorLang.accounts.clone_borrowed_info_run"
  run := accounts.clone_borrowed_info_run (infoCloneTypes .borrowed)
  value := infoCloneFn .borrowed
  graph := infoClone_graph .borrowed
  ready := infoCloneReadyBorrowed

/-- A concrete release supplies its selected contracts before checkers are
built; no executable checker closes over a dispatch to another release. -/
structure Sources where
  storage : InfoStorage
  info : Binding (World Nat Effects) Borrow.Guard InfoRef Empty Empty
  clone : Nat → Binding (World Nat Effects) Borrow.Guard Borrow.Handle String String
  infoClone : Binding (World Unit Effects) Borrow.Guard Borrow.Handle Empty String

def sourcesBorrowed : Sources := ⟨.borrowed, infoBindingBorrowed, cloneBindingBorrowed,
  infoCloneBindingBorrowed⟩

def lamportsReady (s : Lamports.S) (args : Lamports.Args) : Bool :=
  decideBy (p := (Lamports.get_lamports_contract.contract
    Lamports.types).requires s args)
    _ (Lamports.readyB_iff s args)


end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

def moveReadyBorrowed (s : World Nat Effects) (g : Borrow.Handle) : Bool :=
  decideBy (p := (accounts.account.Account.into_inner_contract.contract
    (moveTypes .borrowed)).requires s g)
    _ (movableB_iff s.1 g)

def moveBindingBorrowed : Binding (World Nat Effects) Borrow.Handle Nat Empty String where
  model := "Solanalib.Specs.AnchorLang.accounts.account.Account.into_inner_run"
  run := accounts.account.Account.into_inner_run (moveTypes .borrowed)
  value := intoInnerFn .borrowed
  graph := intoInner_graph .borrowed
  ready := moveReadyBorrowed

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

def payloadReady (s : World Nat Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p := (accounts.sysvar.Sysvar.deref_contract.contract
    projectionTypes).requires s g) _ (readableB_iff s.1 g)

def setReady (mode : Nat) (s : World Nat Effects) (args : Borrow.Guard × Nat) : Bool :=
  decideBy (p := (accounts.account.Account.set_inner_contract.contract
    (setTypes mode)).requires s args) _ (writableB_iff s.1 args.1)

def infoReadyOwned (s : World Nat Effects) (g : Borrow.Guard) : Bool :=
  decideBy (p := (accounts.owned_info_ref_contract.contract
    projectionTypes).requires s g)
    _ (readableB_iff s.1 g)

def infoBindingOwned : Binding (World Nat Effects) Borrow.Guard InfoRef Empty Empty where
  model := "Solanalib.Specs.AnchorLang.accounts.owned_info_ref_run"
  run := accounts.owned_info_ref_run projectionTypes
  value := (fun s g => some (.returned (infoReference .owned s g).1 (infoReference .owned s g).2))
  graph := fun s g => returnsGraph _ s g
  ready := infoReadyOwned

end SolanalibTest.Conformance.Library.Families.AnchorViews
