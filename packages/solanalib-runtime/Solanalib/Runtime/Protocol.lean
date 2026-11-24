/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Runtime

universe u v w

/-- The semantic environment carries its own state. A concrete Solana instance
uses runtime state and explicit request and answer encodings. -/
structure Protocol (State : Type u) (Request : Type v) (Reply : Type w) where
  step : State → Request → Reply → State → Prop

def Protocol.forgetState {State : Type u} {Request : Type v} {Reply : Type w}
    (P : Protocol State Request Reply) (request : Request) (reply : Reply) : Prop :=
  ∃ before after, P.step before request reply after

theorem Protocol.step_covered {State : Type u} {Request : Type v} {Reply : Type w}
    (P : Protocol State Request Reply) {before after : State} {request : Request} {reply : Reply}
    (h : P.step before request reply after) : P.forgetState request reply :=
  ⟨before, after, h⟩

/-- A property of one request and reply can be transported through forgetting
only when it holds for every state that the environment permits. -/
theorem Protocol.uniform_post {State : Type u} {Request : Type v} {Reply : Type w}
    (P : Protocol State Request Reply) (post : Request → Reply → Prop)
    (hpost : ∀ before request reply after, P.step before request reply after → post request reply)
    {request : Request} {reply : Reply} (h : P.forgetState request reply) : post request reply := by
  obtain ⟨before, after, hs⟩ := h
  exact hpost before request reply after hs

end Solanalib.Runtime
