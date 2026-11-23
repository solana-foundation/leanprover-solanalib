/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Values
public import Solanalib.Specs.Core.AnchorSplSupport.Sample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

namespace token_interface.TokenAccount

def deref_contract := derefFamily .interfaceTokenAccount
def deref_run := derefRun .interfaceTokenAccount
def deref_sample := derefSample .interfaceTokenAccount
theorem deref_reference : FamilyReference deref_contract deref_run :=
  AnchorSplSupport.deref_reference .interfaceTokenAccount
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  deref_execution .interfaceTokenAccount
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end token_interface.TokenAccount

end Solanalib.Specs.AnchorSpl

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

namespace token.Token

def id_contract := idFamily .token
def id_run := idRun .token
def id_sample : id_contract.Index := Nat
theorem id_reference : FamilyReference id_contract id_run := id_family_reference .token
theorem id_has_execution : FamilyHasExecution id_contract id_run id_sample :=
  id_execution .token
theorem id_satisfiable : FamilySatisfiable id_contract id_sample :=
  id_has_execution.satisfiable

end token.Token

namespace token.TokenAccount

def deref_contract := derefFamily .tokenAccount
def deref_run := derefRun .tokenAccount
def deref_sample := derefSample .tokenAccount
theorem deref_reference : FamilyReference deref_contract deref_run :=
  AnchorSplSupport.deref_reference .tokenAccount
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  deref_execution .tokenAccount
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end token.TokenAccount

namespace associated_token

def create_contract := family (.associated .legacyBoxed .create)
def create_run := reference (.associated .legacyBoxed .create)
def create_sample := Reference.types
theorem create_reference : FamilyReference create_contract create_run := reference_holds
  (.associated .legacyBoxed .create)
theorem create_has_execution : FamilyHasExecution create_contract create_run create_sample :=
  Sample.execution (.associated .legacyBoxed .create)
theorem create_satisfiable : FamilySatisfiable create_contract create_sample :=
  create_has_execution.satisfiable

end associated_token

namespace metadata

def create_metadata_accounts_v3_contract := family (.metadata)
def create_metadata_accounts_v3_run := reference (.metadata)
def create_metadata_accounts_v3_sample := Reference.types
theorem create_metadata_accounts_v3_reference : FamilyReference
  create_metadata_accounts_v3_contract create_metadata_accounts_v3_run := reference_holds
  (.metadata)
theorem create_metadata_accounts_v3_has_execution : FamilyHasExecution
  create_metadata_accounts_v3_contract create_metadata_accounts_v3_run
  create_metadata_accounts_v3_sample :=
  Sample.execution (.metadata)
theorem create_metadata_accounts_v3_satisfiable : FamilySatisfiable
  create_metadata_accounts_v3_contract create_metadata_accounts_v3_sample :=
  create_metadata_accounts_v3_has_execution.satisfiable

end metadata

end Solanalib.Specs.AnchorSpl

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

namespace memo

def build_memo_contract := family (.memo)
def build_memo_run := reference (.memo)
def build_memo_sample := Reference.types
theorem build_memo_reference : FamilyReference build_memo_contract build_memo_run :=
  reference_holds (.memo)
theorem build_memo_has_execution : FamilyHasExecution build_memo_contract build_memo_run
  build_memo_sample :=
  Sample.execution (.memo)
theorem build_memo_satisfiable : FamilySatisfiable build_memo_contract build_memo_sample :=
  build_memo_has_execution.satisfiable

end memo

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

namespace token_interface.TokenAccount

end token_interface.TokenAccount

namespace associated_token

def create_program_id_contract := family (.associated .modern .create)
def create_program_id_run := reference (.associated .modern .create)
def create_program_id_sample := Reference.types
theorem create_program_id_reference : FamilyReference create_program_id_contract
  create_program_id_run := reference_holds (.associated .modern .create)
theorem create_program_id_has_execution : FamilyHasExecution create_program_id_contract
  create_program_id_run create_program_id_sample :=
  Sample.execution (.associated .modern .create)
theorem create_program_id_satisfiable : FamilySatisfiable create_program_id_contract
  create_program_id_sample :=
  create_program_id_has_execution.satisfiable

end associated_token

namespace associated_token

def create_idempotent_contract := family (.associated .modern .idempotent)
def create_idempotent_run := reference (.associated .modern .idempotent)
def create_idempotent_sample := Reference.types
theorem create_idempotent_reference : FamilyReference create_idempotent_contract
  create_idempotent_run := reference_holds (.associated .modern .idempotent)
theorem create_idempotent_has_execution : FamilyHasExecution create_idempotent_contract
  create_idempotent_run create_idempotent_sample :=
  Sample.execution (.associated .modern .idempotent)
theorem create_idempotent_satisfiable : FamilySatisfiable create_idempotent_contract
  create_idempotent_sample :=
  create_idempotent_has_execution.satisfiable

end associated_token

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

namespace token.Token

end token.Token

namespace token.TokenAccount

end token.TokenAccount

namespace token_2022.Token2022

def id_contract := idFamily .token2022
def id_run := idRun .token2022
def id_sample : id_contract.Index := Nat
theorem id_reference : FamilyReference id_contract id_run := id_family_reference .token2022
theorem id_has_execution : FamilyHasExecution id_contract id_run id_sample :=
  id_execution .token2022
theorem id_satisfiable : FamilySatisfiable id_contract id_sample :=
  id_has_execution.satisfiable

end token_2022.Token2022

namespace token_interface.TokenAccount

end token_interface.TokenAccount

namespace associated_token

end associated_token

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

namespace token_interface.TokenAccount

end token_interface.TokenAccount

namespace token_interface.TokenInterface

def ids_contract := idsFamily
def ids_run := idsRun
def ids_sample : ids_contract.Index := Nat
theorem ids_reference : FamilyReference ids_contract ids_run := ids_family_reference
theorem ids_has_execution : FamilyHasExecution ids_contract ids_run ids_sample :=
  ids_execution
theorem ids_satisfiable : FamilySatisfiable ids_contract ids_sample :=
  ids_has_execution.satisfiable

end token_interface.TokenInterface

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl.stake.StakeAccount

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

def deref_contract := derefFamily .stakeAccount
def deref_run := derefRun .stakeAccount
def deref_sample := derefSample .stakeAccount
theorem deref_reference : FamilyReference deref_contract deref_run :=
  AnchorSplSupport.deref_reference .stakeAccount
theorem deref_has_execution : FamilyHasExecution deref_contract deref_run deref_sample :=
  deref_execution .stakeAccount
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  deref_has_execution.satisfiable

end Solanalib.Specs.AnchorSpl.stake.StakeAccount

namespace Solanalib.Specs.AnchorSpl.stake

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

def deactivate_stake_contract := family (.deactivate)
def deactivate_stake_run := reference (.deactivate)
def deactivate_stake_sample := Reference.types
theorem deactivate_stake_reference : FamilyReference deactivate_stake_contract deactivate_stake_run
  := reference_holds (.deactivate)
theorem deactivate_stake_has_execution : FamilyHasExecution deactivate_stake_contract
  deactivate_stake_run deactivate_stake_sample :=
  Sample.execution (.deactivate)
theorem deactivate_stake_satisfiable : FamilySatisfiable deactivate_stake_contract
  deactivate_stake_sample :=
  deactivate_stake_has_execution.satisfiable

def withdraw_contract := family (.withdraw)
def withdraw_run := reference (.withdraw)
def withdraw_sample := Reference.types
theorem withdraw_reference : FamilyReference withdraw_contract withdraw_run := reference_holds
  (.withdraw)
theorem withdraw_has_execution : FamilyHasExecution withdraw_contract withdraw_run withdraw_sample
  :=
  Sample.execution (.withdraw)
theorem withdraw_satisfiable : FamilySatisfiable withdraw_contract withdraw_sample :=
  withdraw_has_execution.satisfiable

end Solanalib.Specs.AnchorSpl.stake

namespace Solanalib.Specs.AnchorSpl.token.TokenAccount

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplSupport

end Solanalib.Specs.AnchorSpl.token.TokenAccount
