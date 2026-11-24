/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Instruction

def systemCreateAccount (fromAddress toAddress : _root_.Solanalib.Runtime.Pubkey)
    (lamports space : Nat) (owner : _root_.Solanalib.Runtime.Pubkey) : Value :=
  make systemProgramId [accountMeta fromAddress true true, accountMeta toAddress true true]
    (_root_.Solanalib.Runtime.u32le 0 ++ _root_.Solanalib.Runtime.u64le lamports ++
      _root_.Solanalib.Runtime.u64le space ++ owner.bytes)


end Solanalib.Specs.Core.Instruction
