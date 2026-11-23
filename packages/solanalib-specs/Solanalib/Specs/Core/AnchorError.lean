/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorError

universe u v

/-- Source locations retained by Anchor errors. The line is a Rust `u32`. -/
structure Source where
  filename : String
  line : UInt32
  deriving DecidableEq, Repr

inductive Origin where
  | source (location : Source)
  | accountName (name : String)
  deriving DecidableEq, Repr

inductive ComparedValues where
  | values (left right : String)
  | pubkeys (left right : _root_.Solanalib.Runtime.Pubkey)
  deriving DecidableEq, Repr

/-- The full mathematical payload of `anchor_lang::error::AnchorError`.
Equality here observes all fields; it is not the code-only `PartialEq` of Rust. -/
structure AnchorValue where
  name : String
  code : UInt32
  message : String
  origin : Option Origin
  compared : Option ComparedValues
  deriving DecidableEq, Repr

/-- Anchor adds diagnostic fields without interpreting the SDK error payload. -/
structure ProgramValue (ProgramError : Type u) where
  error : ProgramError
  origin : Option Origin
  compared : Option ComparedValues
  deriving DecidableEq, Repr

/-- Boxing and allocator behavior are separate from this value model. -/
inductive Value (ProgramError : Type u) where
  | anchor (error : AnchorValue)
  | program (error : ProgramValue ProgramError)
  deriving DecidableEq, Repr

def Value.origin {ProgramError : Type u} : Value ProgramError → Option Origin
  | .anchor error => error.origin
  | .program error => error.origin

def Value.compared {ProgramError : Type u} : Value ProgramError → Option ComparedValues
  | .anchor error => error.compared
  | .program error => error.compared

/-- Replace the diagnostic comparison and preserve the complete remaining payload. -/
def Value.replaceCompared {ProgramError : Type u} (error : Value ProgramError)
    (compared : ComparedValues) : Value ProgramError :=
  match error with
  | .anchor payload => .anchor { payload with compared := some compared }
  | .program payload => .program { payload with compared := some compared }

@[simp] theorem Value.replaceCompared_origin {ProgramError : Type u}
    (error : Value ProgramError) (compared : ComparedValues) :
    (error.replaceCompared compared).origin = error.origin := by
  cases error <;> rfl

@[simp] theorem Value.replaceCompared_compared {ProgramError : Type u}
    (error : Value ProgramError) (compared : ComparedValues) :
    (error.replaceCompared compared).compared = some compared := by
  cases error <;> rfl

@[simp] theorem Value.replaceCompared_replaceCompared {ProgramError : Type u}
    (error : Value ProgramError) (first second : ComparedValues) :
    (error.replaceCompared first).replaceCompared second = error.replaceCompared second := by
  cases error <;> rfl

structure PubkeysArgs (ProgramError : Type u) where
  error : Value ProgramError
  left : _root_.Solanalib.Runtime.Pubkey
  right : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Mathematical value construction; an implementation must separately account
for `Box::new`, allocation failure and representation. -/
def fromAnchorContract (State : Type v) (ProgramError : Type u) :
    Solanalib.Contracts.Model State AnchorValue (Value ProgramError) :=
  .returning (fun _ _ => True)
    (fun before error result after => after = before ∧ result = .anchor error)

/-- `with_pubkeys` replaces an existing comparison in either error variant. -/
def withPubkeysContract (State : Type v) (ProgramError : Type u) :
    Solanalib.Contracts.Model State (PubkeysArgs ProgramError) (Value ProgramError) :=
  .returning (fun _ _ => True)
    (fun before args result after =>
      after = before ∧ result = args.error.replaceCompared (.pubkeys args.left args.right))

def fromAnchorReference {State : Type v} {ProgramError : Type u}
    (before : State) (error : AnchorValue) : Value ProgramError × State :=
  (.anchor error, before)

def withPubkeysReference {State : Type v} {ProgramError : Type u}
    (before : State) (args : PubkeysArgs ProgramError) : Value ProgramError × State :=
  (args.error.replaceCompared (.pubkeys args.left args.right), before)

theorem fromAnchorReference_realizes (State : Type v) (ProgramError : Type u) :
    (fromAnchorContract State ProgramError).RealizedBy fromAnchorReference := by
  intro before error _
  exact ⟨rfl, rfl⟩

theorem withPubkeysReference_realizes (State : Type v) (ProgramError : Type u) :
    (withPubkeysContract State ProgramError).RealizedBy withPubkeysReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

end Solanalib.Specs.Core.AnchorError
