/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.CollectionChecks

/-! Kernel checks for inputs the native parser cannot construct: a data cell
where lamports are required, a lamports cell where data are required, and a
missing Box. Version-specific declarations apply these to the exact registered
contracts. Invalid source representations are never added to the native corpus. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

namespace AdmissionControls

def step : Step := ⟨.zero, none, none, 41, 0, false, [1, 2]⟩
def script : Script := ⟨[step, step], [step], [step, step], [step], [step], [step], [step], [step],
  [step], "discriminator"⟩

def illTyped : W := (⟨[⟨.data [], ⟨32⟩⟩, ⟨.lamports 0, ⟨32⟩⟩], []⟩, {
  owners := [.zero], counts := [1, 1], log := [], strings := [], boxes := [], payload := 11,
  extraLive := 0, programString := none, buffers := [none, none], payloadBoxes := [] })

def info : AccountInfo.Value := AccountInfo.sampleInfo
def reference : AccountReference := ⟨0, info⟩
def args : AccountInfo.Args := ⟨profile, info⟩
def closeArgs : CloseArgs := ⟨profile, info, info⟩
def accounts : AccountsState Nat := ⟨[reference], 0, []⟩
def accountsArgs : AccountsArgs := ⟨profile, .zero, []⟩

def exitArgs (kind : PayloadKind) : ExitArgs kind Nat :=
  match kind with
  | .account => ⟨profile, ⟨11, info⟩, .zero⟩
  | .interfaceAccount => ⟨profile, ⟨⟨11, info⟩, .zero⟩, .zero⟩

theorem decision_iff {family : Family} (contracts : FamilyContracts family)
    (contracts_eq : contracts = family.contract) (index : family.Index)
    (state : family.State index) (arguments : family.Args index) (b : Bool)
    (equivalent : b = true ↔ (family.contract index).requires state arguments) :
    decideRequires contracts contracts_eq index state arguments b equivalent = true ↔
      (contracts index).requires state arguments := by
  unfold decideRequires Anchor.RequiresCheck.decideBy
  exact @decide_eq_true_iff _ (decidable_of_iff (b = true) (by rw [contracts_eq]; exact equivalent))

theorem decision_bool {family : Family} (contracts : FamilyContracts family)
    (contracts_eq : contracts = family.contract) (index : family.Index)
    (state : family.State index) (arguments : family.Args index) (b : Bool)
    (equivalent : b = true ↔ (family.contract index).requires state arguments) :
    decideRequires contracts contracts_eq index state arguments b equivalent = b := by
  apply Bool.eq_iff_iff.mpr
  rw [decision_iff, contracts_eq]
  exact equivalent.symm

theorem rejects {family : Family} (contracts : FamilyContracts family)
    (contracts_eq : contracts = family.contract) (index : family.Index)
    (state : family.State index) (arguments : family.Args index) (b : Bool)
    (equivalent : b = true ↔ (family.contract index).requires state arguments) (rejected : b =
      false) :
    ¬ (contracts index).requires state arguments := by
  intro admitted
  have yes := (decision_iff contracts contracts_eq index state arguments b equivalent).mpr admitted
  rw [decision_bool, rejected] at yes
  exact Bool.false_ne_true yes

theorem admits {family : Family} (contracts : FamilyContracts family)
    (contracts_eq : contracts = family.contract) (index : family.Index)
    (state : family.State index) (arguments : family.Args index) (b : Bool)
    (equivalent : b = true ↔ (family.contract index).requires state arguments) (admitted : b =
      true) :
    (contracts index).requires state arguments := by
  apply (decision_iff contracts contracts_eq index state arguments b equivalent).mp
  rw [decision_bool, admitted]

end AdmissionControls
end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
