/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Builders

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.BuilderErrors

/-- A property of ordinary values imposes no constraint on an exceptional
exit. Cleanup may change the exit kind, but cannot invent a different value. -/
def Returned {State Value Unwind Terminal : Type} (property : Value → Prop) :
    Outcome State Value Unwind Terminal → Prop
  | .returned value _ => property value
  | .unwound _ _ | .terminated _ => True

theorem cleanup {State Value Unwind Terminal : Type} (property : Value → Prop)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (pending final : Outcome State Value Unwind Terminal)
    (holds : Returned property pending) (cleaned : Owned.cleanup double drops pending final) :
    Returned property final := by
  induction drops generalizing pending final with
  | nil => cases cleaned; exact holds
  | cons action rest induction =>
    cases pending with
    | terminated reason => cases cleaned; trivial
    | returned value state =>
      obtain ⟨dropped, _, next⟩ := cleaned
      cases dropped with
      | returned result after =>
        cases result; exact induction (.returned value after) final holds next
      | unwound reason after => exact induction (.unwound reason after) final True.intro next
      | terminated reason => cases next; trivial
    | unwound reason state =>
      obtain ⟨dropped, _, next⟩ := cleaned
      cases dropped with
      | returned result after =>
        cases result; exact induction (.unwound reason after) final True.intro next
      | unwound later after => obtain ⟨_, _, rfl⟩ := next; trivial
      | terminated terminal => cases next; trivial

theorem protect_property {State Args Value Unwind Terminal : Type} (property : Value → Prop)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal)
    (before : State) (args : Args) (final : Outcome State Value Unwind Terminal)
    (valid : ∀ pending, body before args pending → Returned property pending)
    (called : Owned.protect double drops body before args final) : Returned property final := by
  obtain ⟨pending, called, next⟩ := called
  have holds := valid pending called
  cases pending with
  | returned value state => cases next; exact holds
  | unwound reason state => exact cleanup property double drops _ _ holds next
  | terminated reason => exact cleanup property double drops _ _ holds next

theorem scope_property {State Args Value Unwind Terminal : Type} (property : Value → Prop)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal)
    (before : State) (args : Args) (final : Outcome State Value Unwind Terminal)
    (valid : ∀ pending, body before args pending → Returned property pending)
    (called : Owned.scope double drops body before args final) : Returned property final := by
  obtain ⟨pending, called, next⟩ := called
  exact cleanup property double drops pending final (valid pending called) next

theorem bound {State Args Value Next Unwind Terminal : Type} (property : Next → Prop)
    (body : Callback.Run State Args Value Unwind Terminal)
    (next : Value → State → Outcome State Next Unwind Terminal → Prop)
    (before : State) (args : Args) (final : Outcome State Next Unwind Terminal)
    (valid : ∀ value state pending, next value state pending → Returned property pending)
    (called : Callback.bind body next before args final) : Returned property final := by
  obtain ⟨pending, _, called⟩ := called
  cases pending with
  | returned value state => exact valid value state final called
  | unwound reason state => cases called; trivial
  | terminated reason => cases called; trivial

theorem mapped {State Args Value Next Unwind Terminal : Type} (property : Next → Prop)
    (mapping : Value → Next) (body : Callback.Run State Args Value Unwind Terminal)
    (before : State) (args : Args) (final : Outcome State Next Unwind Terminal)
    (valid : ∀ value, property (mapping value))
    (called : Callback.map mapping body before args final) : Returned property final := by
  obtain ⟨pending, _, rfl⟩ := called
  cases pending with
  | returned value _ => exact valid value
  | unwound _ _ | terminated _ => trivial

/-- The only local constructor errors in the reviewed wrappers. Opaque
invocation errors are not translated through this classification. -/
def ErrorAllowed (error : Token.Error) : Prop :=
  error = .IncorrectProgramId ∨ error = .InvalidArgument

def ResultAllowed {Value : Type} : Except Token.Error Value → Prop
  | .ok _ => True
  | .error error => ErrorAllowed error

theorem program_error (programs : Token.Instruction.ProgramSet) (program : Solanalib.Runtime.Pubkey)
    (error : Token.Error) (rejected : Token.Instruction.checkProgram programs program = .error
      error) :
    ErrorAllowed error := by
  unfold Token.Instruction.checkProgram at rejected
  split at rejected
  · cases rejected
  · cases rejected; exact Or.inl rfl

theorem ordinary (types : Token.InstructionAllocated.Types) (before : types.State)
    (plan : Token.InstructionAllocated.Plan)
    (final : Outcome types.State (Except Token.Error (Token.InstructionAllocated.Value types))
      types.Unwind types.Terminal)
    (called : Token.InstructionAllocated.run types before plan final) :
    Returned ResultAllowed final := by
  unfold Token.InstructionAllocated.run at called
  split at called
  next error rejected => cases called; exact program_error _ _ _ rejected
  next accepted =>
    split at called
    · apply bound ResultAllowed _ _ _ _ _ (called := called)
      intro data state pending protectedCall
      apply protect_property ResultAllowed _ _ _ _ _ _ (called := protectedCall)
      intro pending called
      apply bound ResultAllowed _ _ _ _ _ (called := called)
      intro result state pending mappedCall
      apply mapped ResultAllowed _ _ _ _ _ (called := mappedCall)
      intro value
      trivial
    · apply bound ResultAllowed _ _ _ _ _ (called := called)
      intro metas state pending protectedCall
      apply protect_property ResultAllowed _ _ _ _ _ _ (called := protectedCall)
      intro pending mappedCall
      apply mapped ResultAllowed _ _ _ _ _ (called := mappedCall)
      intro value
      trivial

theorem optional_error (key : Option Solanalib.Runtime.Pubkey) (error : Token.Error)
    (rejected : Token.MetadataPointer.optionalNonzero key = .error error) : ErrorAllowed error := by
  cases key with
  | none => cases rejected
  | some key =>
    by_cases zero : key = .zero
    · simp only [Token.MetadataPointer.optionalNonzero, zero, ↓reduceIte] at rejected
      cases rejected; exact Or.inr rfl
    · simp only [Token.MetadataPointer.optionalNonzero, zero, ↓reduceIte] at rejected
      cases rejected

theorem pointer_fields (args : Token.MetadataPointer.Args) (error : Token.Error)
    (rejected : Token.MetadataPointer.fields args = .error error) : ErrorAllowed error := by
  cases first : Token.MetadataPointer.optionalNonzero args.authority with
  | error failure =>
    have equal : failure = error := by simpa only [Token.MetadataPointer.fields, first, bind,
      Except.bind, pure, Except.pure, Except.error.injEq] using rejected
    exact equal ▸ optional_error args.authority failure first
  | ok authority =>
    cases second : Token.MetadataPointer.optionalNonzero args.metadataAddress with
    | error failure =>
      have equal : failure = error := by simpa only [Token.MetadataPointer.fields, first, second,
        bind, Except.bind, pure, Except.pure, Except.error.injEq] using rejected
      exact equal ▸ optional_error args.metadataAddress failure second
    | ok address => simp only [Token.MetadataPointer.fields, first, second, bind, Except.bind,
      pure, Except.pure, reduceCtorEq] at rejected

theorem pointer (tag : UInt8) (types : Token.InstructionAllocated.Types)
    (before : types.State) (args : Token.MetadataPointer.Args)
    (final : Outcome types.State (Except Token.Error (Token.InstructionAllocated.Value types))
      types.Unwind types.Terminal)
    (called : Token.MetadataPointer.run tag types before args final) :
    Returned ResultAllowed final := by
  unfold Token.MetadataPointer.run at called
  split at called
  next error rejected => cases called; exact program_error _ _ _ rejected
  next accepted =>
    apply bound ResultAllowed _ _ _ _ _ (called := called)
    intro resource state pending called
    unfold Token.MetadataPointer.afterMetas at called
    split at called
    next error rejected =>
      exact cleanup ResultAllowed _ _ (.returned (.error error) state) pending
        (pointer_fields args error rejected) called
    next encoded valid =>
      apply protect_property ResultAllowed _ _ _ _ _ _ (called := called)
      intro pending mappedCall
      apply mapped ResultAllowed _ _ _ _ _ (called := mappedCall)
      intro value
      trivial

theorem size (types : Builder) (before : types.instruction.State)
    (program mint : Solanalib.Runtime.Pubkey) (extensions : List ExtensionType)
    (final : Outcome types.instruction.State
      (Except Token.Error (Token.InstructionAllocated.Value types.instruction))
      types.instruction.Unwind types.instruction.Terminal)
    (called : sizeRun types program mint extensions before () final) :
    Returned ResultAllowed final := by
  unfold sizeRun at called
  split at called
  next error rejected => cases called; exact program_error _ _ _ rejected
  next accepted =>
    apply bound ResultAllowed _ _ _ _ _ (called := called)
    intro metas state pending protectedCall
    apply protect_property ResultAllowed _ _ _ _ _ _ (called := protectedCall)
    intro pending called
    apply bound ResultAllowed _ _ _ _ _ (called := called)
    intro copied state pending called
    obtain ⟨current, _, called⟩ := called
    apply scope_property ResultAllowed _ _ _ _ _ _ (called := called)
    intro pending mappedCall
    apply mapped ResultAllowed _ _ _ _ _ (called := mappedCall)
    intro value
    trivial

/-- Every actual returned constructor error has its exact ProgramError
counterpart. Allocation, mutation and cleanup providers remain arbitrary. -/
theorem build_error (types : Builder) (before after : types.instruction.State)
    (input : Construction) (error : Token.Error)
    (called : build types before input (.returned (.error error) after)) :
    error = .IncorrectProgramId ∨ error = .InvalidArgument := by
  cases input with
  | ordinary plan => exact ordinary types.instruction before plan _ called
  | pointer tag args => exact pointer tag types.instruction before args _ called
  | size program mint extensions => exact size types before program mint extensions _ called

end Solanalib.Specs.Core.AnchorSplTokenOperations.BuilderErrors
