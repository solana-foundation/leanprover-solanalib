/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SdkValue

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSdkIds

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace bpf_loader_upgradeable

/-- Return the canonical address of the exact SDK declaration. -/
abbrev id_contract := SdkValue.idContract Solanalib.Runtime.Ids.bpfLoaderUpgradeable

/-- Total constant-key reference. -/
abbrev id_model := SdkValue.idModel Solanalib.Runtime.Ids.bpfLoaderUpgradeable

theorem id_reference : id_contract.RealizedBy id_model :=
  SdkValue.idReference Solanalib.Runtime.Ids.bpfLoaderUpgradeable

theorem id_satisfiable : id_contract.Satisfiable :=
  SdkValue.idSatisfiable Solanalib.Runtime.Ids.bpfLoaderUpgradeable

end bpf_loader_upgradeable

namespace ed25519_program

/-- Return the canonical address of the exact SDK declaration. -/
abbrev id_contract := SdkValue.idContract Solanalib.Runtime.Ids.ed25519Program

/-- Total constant-key reference. -/
abbrev id_model := SdkValue.idModel Solanalib.Runtime.Ids.ed25519Program

theorem id_reference : id_contract.RealizedBy id_model :=
  SdkValue.idReference Solanalib.Runtime.Ids.ed25519Program

theorem id_satisfiable : id_contract.Satisfiable :=
  SdkValue.idSatisfiable Solanalib.Runtime.Ids.ed25519Program

end ed25519_program


end Solanalib.Specs.SolanaSdkIds

namespace Solanalib.Specs.SolanaSdkIds

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace sysvar.instructions

/-- Return the canonical address of the exact SDK declaration. -/
abbrev id_contract := SdkValue.idContract Solanalib.Runtime.Ids.sysvarInstructions

/-- Total constant-key reference. -/
abbrev id_model := SdkValue.idModel Solanalib.Runtime.Ids.sysvarInstructions

theorem id_reference : id_contract.RealizedBy id_model :=
  SdkValue.idReference Solanalib.Runtime.Ids.sysvarInstructions

theorem id_satisfiable : id_contract.Satisfiable :=
  SdkValue.idSatisfiable Solanalib.Runtime.Ids.sysvarInstructions

end sysvar.instructions

namespace vote

/-- Return the canonical address of the exact SDK declaration. -/
abbrev id_contract := SdkValue.idContract Solanalib.Runtime.Ids.voteProgram

/-- Total constant-key reference. -/
abbrev id_model := SdkValue.idModel Solanalib.Runtime.Ids.voteProgram

theorem id_reference : id_contract.RealizedBy id_model :=
  SdkValue.idReference Solanalib.Runtime.Ids.voteProgram

theorem id_satisfiable : id_contract.Satisfiable :=
  SdkValue.idSatisfiable Solanalib.Runtime.Ids.voteProgram

end vote


end Solanalib.Specs.SolanaSdkIds
