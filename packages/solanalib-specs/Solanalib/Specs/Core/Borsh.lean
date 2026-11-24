/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borsh

universe u v w x y

/-- The selected address serializer delegates one complete byte slice to
`Write::write_all`. The callback owns its error and partial-write semantics;
an error does not roll its state back. -/
def serializeBytes {State : Type u} {Error : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (writer : Callback.Run State Solanalib.Runtime.Bytes (Except Error Unit) Unwind Terminal) :
    Callback.Run State Solanalib.Runtime.Bytes (Except Error Unit) Unwind Terminal := writer

@[simp] theorem serializeBytes_iff {State : Type u} {Error : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (writer : Callback.Run State Solanalib.Runtime.Bytes (Except Error Unit) Unwind Terminal)
    (before : State) (bytes : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) :
    serializeBytes writer before bytes outcome ↔ writer before bytes outcome := Iff.rfl


end Solanalib.Specs.Core.Borsh
