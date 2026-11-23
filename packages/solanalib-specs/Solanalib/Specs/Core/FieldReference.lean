/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core

universe u v w x y

/-- A borrowed field retains its parent reference and the selected field.
It stores no pointee snapshot and allocates or consumes no borrow guard. A
source binding must relate both identities to the same live source borrow. -/
structure FieldReference (Parent : Type u) (Field : Type v) where
  /-- Identity of the already borrowed parent. -/
  parent : Parent
  /-- The field chosen when the derived reference was formed. -/
  field : Field
  deriving DecidableEq, Repr

namespace FieldReference

/-- Current observations through an existing parent reference. `live` is an
explicit admission for lifetime, permissions and valid access; `current` is
the corresponding value observation. Neither field proves a Rust memory
representation, and `current` alone does not license a source read. -/
structure Access (State : Type u) (Parent : Type v) (Value : Type w) where
  /-- The existing parent borrow permits a read in this state. -/
  live : State → Parent → Prop
  /-- Its current represented value, when available. -/
  current : State → Parent → Option Value

/-- A parent read requires both current admission and represented contents. -/
def Access.Reads {State : Type u} {Parent : Type v} {Value : Type w}
    (access : Access State Parent Value) (state : State) (parent : Parent) (value : Value) : Prop :=
  access.live state parent ∧ access.current state parent = some value

/-- Observe the fixed field in the current parent. This value observation
does not independently establish access permission; use `Reads` for that. -/
def current {State : Type u} {Parent : Type v} {ParentValue : Type w}
    {Field : Type x} {Value : Type y} (access : Access State Parent ParentValue)
    (project : Field → ParentValue → Value) (state : State)
    (reference : FieldReference Parent Field) : Option Value :=
  (access.current state reference.parent).map (project reference.field)

/-- A field read follows the retained parent in the actual read state.
Admission is inherited from that parent; there is no new borrow acquisition. -/
def Reads {State : Type u} {Parent : Type v} {ParentValue : Type w}
    {Field : Type x} {Value : Type y} (access : Access State Parent ParentValue)
    (project : Field → ParentValue → Value) (state : State)
    (reference : FieldReference Parent Field) (value : Value) : Prop :=
  access.live state reference.parent ∧ current access project state reference = some value

/-- Every admitted current parent value gives a read of the retained field. -/
theorem reads_of_parent {State : Type u} {Parent : Type v} {ParentValue : Type w}
    {Field : Type x} {Value : Type y} (access : Access State Parent ParentValue)
    (project : Field → ParentValue → Value) (state : State)
    (reference : FieldReference Parent Field) (parentValue : ParentValue)
    (read : access.Reads state reference.parent parentValue) :
    Reads access project state reference (project reference.field parentValue) := by
  exact ⟨read.1, by simp [current, read.2]⟩

/-- An expired or inaccessible parent cannot license a field read, even if
an independent value observation still contains old data. -/
theorem no_read_of_not_live {State : Type u} {Parent : Type v} {ParentValue : Type w}
    {Field : Type x} {Value : Type y} (access : Access State Parent ParentValue)
    (project : Field → ParentValue → Value) (state : State)
    (reference : FieldReference Parent Field) (notLive : ¬ access.live state reference.parent) :
    ∀ value, ¬ Reads access project state reference value := by
  intro value read
  exact notLive read.1

/-- A missing current representation cannot be replaced by a saved value. -/
theorem no_read_of_missing {State : Type u} {Parent : Type v} {ParentValue : Type w}
    {Field : Type x} {Value : Type y} (access : Access State Parent ParentValue)
    (project : Field → ParentValue → Value) (state : State)
    (reference : FieldReference Parent Field)
    (missing : access.current state reference.parent = none) :
    ∀ value, ¬ Reads access project state reference value := by
  intro value read
  simpa [current, missing] using read.2

/-- Two permitted reads in the same state observe the same field value. -/
theorem reads_unique {State : Type u} {Parent : Type v} {ParentValue : Type w}
    {Field : Type x} {Value : Type y} (access : Access State Parent ParentValue)
    (project : Field → ParentValue → Value) (state : State)
    (reference : FieldReference Parent Field) {left right : Value}
    (readLeft : Reads access project state reference left)
    (readRight : Reads access project state reference right) : left = right :=
  Option.some.inj (readLeft.2.symm.trans readRight.2)

end FieldReference

end Solanalib.Specs.Core
