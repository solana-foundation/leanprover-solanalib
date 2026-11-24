/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Frame

@[expose] public section

/-!
# The environment relation

Interface B of the report: one relation answers every syscall of an invocation except
CPI, whose answer runs a callee (`Exec.cpi`).
Its context is fixed for the invocation (`World` and `InvCtx`), and the state it threads
is the invocation state, which syscalls other than CPI change only in the return data,
the heap position and the logs.

A trace of records is valid when one sequence of states carries every record through
the relation (`ValidTrace`). The answers to sysvar requests depend on the fixed context,
which gives Clock constancy within that context (`sysvar_answer_constant`,
`ValidTrace.clock_constant`). Implementations connect their call behavior to this
relation; forgetting its state does not preserve correlations between separate calls.

See the [model report](../../README.md#model-report) for runtime services and
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives)
for the translation, output-write and primitive premises needed for a
correspondence with the selected runtime.
-/

namespace Solanalib.Runtime

/-- The environment relation of one invocation, for requests other than CPI. -/
def Env (W : World) (c : InvCtx) (st : InvState) (req : SysReq) (ans : SysAns) (st' : InvState) :
    Prop :=
  req.registered W.prof = true ∧ (∀ q, req ≠ .invoke q) ∧
    ((req ≠ .remainingComputeUnits ∧
      sysStep W.prof W.prims W.sysvars W.epochStake c st req = .ok (ans, st')) ∨
     (req = .remainingComputeUnits ∧ ans.out = [] ∧ st' = st))

/-- A trace of syscall records is valid when a sequence of states carries every record
through the environment relation. -/
inductive ValidTrace (W : World) (c : InvCtx) : InvState → List (SysReq × SysAns) → Prop
  | nil {st : InvState} : ValidTrace W c st []
  | cons {st st' : InvState} {req : SysReq} {ans : SysAns} {rest : List (SysReq × SysAns)} :
      Env W c st req ans st' → ValidTrace W c st' rest → ValidTrace W c st ((req, ans) :: rest)

/-- Whether a request reads a sysvar. -/
def SysReq.isSysvarRead : SysReq → Bool
  | .getSysvarTyped _ _ => true
  | .getSysvar _ _ _ _ => true
  | _ => false

/-- The answer to a sysvar request depends on the context alone: two states give the same
answer. -/
theorem sysvar_answer_constant {W : World} {c : InvCtx} {st₁ st₂ st₁' st₂' : InvState}
    {req : SysReq} {a₁ a₂ : SysAns} (hreq : req.isSysvarRead = true)
    (h₁ : Env W c st₁ req a₁ st₁') (h₂ : Env W c st₂ req a₂ st₂') : a₁ = a₂ := by
  obtain ⟨_, _, h₁⟩ := h₁
  obtain ⟨_, _, h₂⟩ := h₂
  cases req with
  | getSysvarTyped which dst =>
    rcases h₁ with ⟨_, h₁⟩ | ⟨h₁, _⟩
    · rcases h₂ with ⟨_, h₂⟩ | ⟨h₂, _⟩
      · simp only [sysStep] at h₁ h₂
        repeat' split at h₁ <;> (try cases h₁) <;> (repeat' split at h₂) <;> (try cases h₂) <;>
          (try simp_all)
      · cases h₂
    · cases h₁
  | getSysvar id offset len dst =>
    rcases h₁ with ⟨_, h₁⟩ | ⟨h₁, _⟩
    · rcases h₂ with ⟨_, h₂⟩ | ⟨h₂, _⟩
      · simp only [sysStep] at h₁ h₂
        repeat' split at h₁ <;> (try cases h₁) <;> (repeat' split at h₂) <;> (try cases h₂) <;>
          (try simp_all)
      · cases h₂
    · cases h₁
  | _ => simp [SysReq.isSysvarRead] at hreq

/-- In a valid trace, all successful reads of the Clock receive the same bytes. -/
theorem ValidTrace.clock_constant {W : World} {c : InvCtx} {st : InvState}
    {recs : List (SysReq × SysAns)} (h : ValidTrace W c st recs) {d₁ d₂ : Nat} {a₁ a₂ : SysAns}
    (h₁ : (SysReq.getSysvarTyped .clock d₁, a₁) ∈ recs)
    (h₂ : (SysReq.getSysvarTyped .clock d₂, a₂) ∈ recs) : a₁ = a₂ := by
  have hall : ∀ q ∈ recs, ∃ s s', Env W c s q.1 q.2 s' := by
    clear h₁ h₂
    induction h with
    | nil => intro q hq; cases hq
    | cons he _ ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨_, _, he⟩
      · exact ih q hq
  obtain ⟨s₁, s₁', e₁⟩ := hall _ h₁
  obtain ⟨s₂, s₂', e₂⟩ := hall _ h₂
  obtain ⟨_, _, e₁⟩ := e₁
  obtain ⟨_, _, e₂⟩ := e₂
  rcases e₁ with ⟨_, e₁⟩ | ⟨e₁, _⟩
  · rcases e₂ with ⟨_, e₂⟩ | ⟨e₂, _⟩
    · simp only [sysStep] at e₁ e₂
      repeat' split at e₁ <;> (try cases e₁) <;> (repeat' split at e₂) <;> (try cases e₂) <;>
        (try simp_all)
    · cases e₂
  · cases e₁

end Solanalib.Runtime
