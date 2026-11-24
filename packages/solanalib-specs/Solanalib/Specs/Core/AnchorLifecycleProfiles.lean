/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleSourceCollections
public import Solanalib.Specs.Core.AnchorLifecycleReloadSamples
public import Solanalib.Specs.Core.AnchorLifecycleCloseSamples
public import Solanalib.Specs.Core.AnchorLifecycleExit
public import Solanalib.Specs.Core.AnchorLifecycleErrorFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

/-- The source version fixes the representation of the Error enum of Anchor. This
selection belongs to the family index, separately from the mathematical
precondition on each input. In particular the 0.27 facade cannot select the
boxed constructor, diagnostic update or destructor. -/
def familyAtStorage (family : Family)
    (select : family.Index → AnchorErrorOperations.Storage)
    (storage : AnchorErrorOperations.Storage) : Family where
  Index := { index : family.Index // select index = storage }
  State := fun index => family.State index.val
  Args := fun index => family.Args index.val
  Value := fun index => family.Value index.val
  Unwind := fun index => family.Unwind index.val
  Terminal := fun index => family.Terminal index.val
  contract := fun index => family.contract index.val

def familyAtStorageRun (family : Family)
    (select : family.Index → AnchorErrorOperations.Storage)
    (storage : AnchorErrorOperations.Storage) (run : FamilyRun family) :
    FamilyRun (familyAtStorage family select storage) := fun index => run index.val

theorem familyAtStorage_reference {family : Family}
    {select : family.Index → AnchorErrorOperations.Storage}
    {storage : AnchorErrorOperations.Storage} {run : FamilyRun family}
    (correct : FamilyReference family run) :
    FamilyReference (familyAtStorage family select storage)
      (familyAtStorageRun family select storage run) := fun index => correct index.val

/-- Every selected index really uses the error storage of the source version; this
is not an additional provider promise or a condition on successful outcomes. -/
theorem familyAtStorage_selected {family : Family}
    {select : family.Index → AnchorErrorOperations.Storage}
    {storage : AnchorErrorOperations.Storage}
    (index : (familyAtStorage family select storage).Index) : select index.val = storage :=
  index.property

end Solanalib.Specs.Core.AnchorLifecycle
