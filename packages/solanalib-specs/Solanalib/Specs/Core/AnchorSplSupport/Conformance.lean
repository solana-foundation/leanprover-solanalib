/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Sample
import all Init.Data.Array.Basic
import all Init.Data.String.Defs

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-- Only scripts actually implemented by the complete signature mock. -/
inductive Script where
  | ok | custom | borsh | unwind
  deriving DecidableEq

def Script.reply : Script → Reference.Reply
  | .ok => .ok
  | .custom => .error (.custom 31)
  | .borsh => .error (.borshIoError 3)
  | .unwind => .unwind "opaque unwind"

/-- The two optional-custodian cases use the same actual wrapper arguments. -/
def nativeArgs : (operation : Operation) → Bool → Args Reference.resources operation
  | .withdraw, custodian => { Sample.args .withdraw with extra :=
      ⟨42, if custodian then some (Sample.info 6) else none⟩ }
  | .associated profile kind, _ => Sample.args (.associated profile kind)
  | .memo, _ => Sample.args .memo
  | .metadata, _ => Sample.args .metadata
  | .deactivate, _ => Sample.args .deactivate

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
/-- All recorded fixture inputs satisfy the real local-read admission, before
any invocation or final cleanup has been assumed. -/
theorem native_checked (operation : Operation) (reply : Script) (custodian : Bool) :
    Reference.checked operation (Sample.initial reply.reply) (nativeArgs operation custodian) =
      true := by
  cases operation with
  | associated profile kind => cases profile <;> cases kind <;> cases reply <;> rfl
  | memo | deactivate => cases reply <;> rfl
  | metadata =>
    change Reference.checked .metadata (Sample.initial reply.reply) (Sample.args .metadata) = true
    cases reply <;> rfl
  | withdraw => cases reply <;> cases custodian <;> rfl


end Solanalib.Specs.Core.AnchorSplSupport.Conformance
