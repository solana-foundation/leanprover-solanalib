/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount

namespace accounts.account.Account

def deref_contract := projectionFamily Account (fun T => T) (fun _ => accountDeref)
def deref_run := projectionRun Account (fun T => T) (fun _ => accountDeref)
def deref_sample := projectionSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  projection_reference _ _ _
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  projection_execution _ _ _ ⟨7, AccountInfo.sampleInfo⟩
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end accounts.account.Account

namespace accounts.interface_account.InterfaceAccount

def deref_contract := projectionFamily InterfaceAccount (fun T => T) (fun _ =>
  interfaceAccountDeref)
def deref_run := projectionRun InterfaceAccount (fun T => T) (fun _ => interfaceAccountDeref)
def deref_sample := projectionSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  projection_reference _ _ _
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  projection_execution _ _ _ ⟨⟨8, AccountInfo.sampleInfo⟩, .zero⟩
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end accounts.interface_account.InterfaceAccount

namespace accounts.interface.Interface

def deref_contract :=
  projectionFamily Interface (fun _ => AccountInfo.Value) (fun _ => interfaceDeref)
def deref_run := projectionRun Interface (fun _ => AccountInfo.Value) (fun _ => interfaceDeref)
def deref_sample := projectionSample
theorem deref_reference : FamilyReference deref_contract deref_run :=
  projection_reference _ _ _
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  projection_execution _ _ _ ⟨⟨AccountInfo.sampleInfo⟩⟩
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end accounts.interface.Interface

namespace accounts.account_loader.AccountLoader

def key_contract := projectionFamily Loader (fun _ => _root_.Solanalib.Runtime.Pubkey) (fun _ =>
  loaderKey)
def key_run := projectionRun Loader (fun _ => _root_.Solanalib.Runtime.Pubkey) (fun _ => loaderKey)
def key_sample := projectionSample
theorem key_reference : FamilyReference key_contract key_run := projection_reference _ _ _
theorem key_has_execution : FamilyHasExecution key_contract key_run key_sample :=
  projection_execution _ _ _ ⟨AccountInfo.sampleInfo⟩
theorem key_satisfiable : FamilySatisfiable key_contract key_sample := key_has_execution.satisfiable

end accounts.account_loader.AccountLoader

namespace accounts.signer.Signer

def key_contract :=
  projectionFamily (fun _ => Signer) (fun _ => _root_.Solanalib.Runtime.Pubkey) (fun _ => signerKey)
def key_run := projectionRun (fun _ => Signer) (fun _ => _root_.Solanalib.Runtime.Pubkey) (fun _ =>
  signerKey)
def key_sample := projectionSample
theorem key_reference : FamilyReference key_contract key_run := projection_reference _ _ _
theorem key_has_execution : FamilyHasExecution key_contract key_run key_sample :=
  projection_execution _ _ _ ⟨AccountInfo.sampleInfo⟩
theorem key_satisfiable : FamilySatisfiable key_contract key_sample := key_has_execution.satisfiable

end accounts.signer.Signer

namespace AccountInfo

def key_contract := projectionFamily (fun _ => Solanalib.Specs.Core.AccountInfo.Value)
  (fun _ => _root_.Solanalib.Runtime.Pubkey) (fun _ => infoKey)
def key_run := projectionRun (fun _ => Solanalib.Specs.Core.AccountInfo.Value)
  (fun _ => _root_.Solanalib.Runtime.Pubkey) (fun _ => infoKey)
def key_sample := projectionSample
theorem key_reference : FamilyReference key_contract key_run := projection_reference _ _ _
theorem key_has_execution : FamilyHasExecution key_contract key_run key_sample :=
  projection_execution _ _ _ Solanalib.Specs.Core.AccountInfo.sampleInfo
theorem key_satisfiable : FamilySatisfiable key_contract key_sample := key_has_execution.satisfiable

end AccountInfo

end Solanalib.Specs.AnchorLang
