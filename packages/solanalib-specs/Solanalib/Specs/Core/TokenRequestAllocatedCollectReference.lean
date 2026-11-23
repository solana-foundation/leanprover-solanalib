/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocus
import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedCollect

/-- Reference storage for collected guard vectors; identities and values are
mathematical ledger entries, not a source allocation layout. -/
abbrev ReferenceExtra := Owned.VectorState Element

/-- The exact account guard world plus the storage ledger of the reference collector. -/
abbrev ReferenceWorld := World ReferenceExtra

/-- Storage operations alone, focused into the auxiliary state. Their drop
retires only the vector slot; element guards are handled by the protocol. -/
def referenceStorage : Owned.VectorOps ReferenceWorld Element Nat Nat Nat :=
  Owned.vectorReference.focus Owned.Focus.snd

/-- One concrete collection interpretation: borrow callbacks run in order,
then the complete array is placed in a fresh reference-ledger slot. This is a
consistency witness with one selected internal schedule, not a Rust collect
algorithm or an allocator success claim. -/
def referenceProtocol : Protocol ReferenceExtra Nat Nat Nat where
  internal := fun _ _ _ _ => False
  finish := referenceStorage.fromList
  retire := fun resource _ before outcome => match resource with
    | none => outcome = .returned () before
    | some identity => referenceStorage.drop before identity outcome
  double := fun _ original later terminal => terminal = original + later

/-- The sample returned vector owns its live guard elements. Drop first
releases those actual references, then retires its storage, with no duplicate
release hidden in the final storage operation. -/
def referenceVectors : Owned.VectorOps ReferenceWorld Element Nat Nat Nat :=
  { referenceStorage with
    drop := fun before resource outcome =>
      ∃ acquired, referenceStorage.current before resource = some acquired ∧
        Owned.cleanup referenceProtocol.double
          (referenceProtocol.drops (some resource) acquired) (.returned () before) outcome }

/-- The reference collection dependency admits exactly the finite protocol traces. -/
def referenceProvider : Provider ReferenceExtra Nat Nat Nat := protocolProvider referenceProtocol

/-- Closed correctness of the sample collection provider against its primitive
callback-order and cleanup protocol. -/
theorem reference_conforms : referenceProvider.Conforms referenceProtocol :=
  protocolProvider_conforms referenceProtocol

/-- Closed exact linkage between successful collected values and the current ordered contents of the
returned vector. Its actual destructor is defined separately. -/
theorem reference_resource_laws : ResourceLaws referenceProtocol referenceVectors := by
  constructor
  intro before acquired resource after finished
  exact (Owned.VectorOps.focus_laws Owned.vectorReference_laws Owned.Focus.snd).list_current
    before acquired resource after finished

end Solanalib.Specs.Core.Token.AllocatedCollect
