/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaNullable.Capabilities
public import Solanalib.Specs.SolanaProgramError.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.ErrorNullableProfiles

open Solanalib.Contracts.Model.Versioning

def registry : Source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def nullableBuild : Build where
  package := "solana-nullable"
  version := "1.3.0"
  source := registry
  dependencies := [⟨"solana-address", "2.6.1", registry⟩]

/-- This selects the concrete Address alternative, rather than the separately interpreted callback
profile of the generic family. -/
def addressAdmitted (build : Build) : Bool :=
  (Solanalib.Specs.SolanaNullable.Capabilities.catalog.applicability .maybe_null_MaybeNull_get).any
    (fun profile => profile.id == "address-2-6-1" && profile.matches build)

theorem reviewed_address_admitted : addressAdmitted nullableBuild = true := by decide +kernel

/-- Compatible defining providers need no Pinocchio facade in the build of the caller. -/
theorem compatible_address_admitted : addressAdmitted
    { nullableBuild with
      version := "1.3.1"
      dependencies := [⟨"solana-address", "2.9.0", registry⟩] } = true := by
  decide +kernel

theorem below_reference_address_rejected : addressAdmitted
    { nullableBuild with dependencies :=
      [⟨"solana-address", "2.6.0", registry⟩] } = false := by
  decide +kernel

theorem unknown_provider_rejected : addressAdmitted
    { nullableBuild with dependencies := [] } = false := by decide +kernel

theorem ambiguous_provider_rejected : addressAdmitted
    { nullableBuild with dependencies := nullableBuild.dependencies ++
      [⟨"solana-address", "2.6.0", registry⟩] } = false := by decide +kernel

/-- Neither a new major line nor a prerelease inherits the reference contract. -/
theorem outside_nullable_range_rejected :
    ["2.0.0", "1.3.1-rc.1"].all (fun version =>
      !addressAdmitted { nullableBuild with version := version }) = true := by
  decide +kernel

def errorBuild : Build := ⟨"solana-program-error", "3.0.1", registry, [], none, none, []⟩

def errorAdmitted (build : Build) : Bool :=
  (Solanalib.Specs.SolanaProgramError.Capabilities.catalog.applicability .ProgramError_from_u64).any
    (fun profile => profile.matches build) &&
  (Solanalib.Specs.SolanaProgramError.Capabilities.catalog.applicability .ProgramError_into_u64).any
    (fun profile => profile.matches build)

theorem reviewed_error_admitted : errorAdmitted errorBuild = true := by decide +kernel

/-- Both conversion directions select compatible releases under the same declared assumption. -/
theorem compatible_errors_admitted :
    ["3.0.2", "3.9.0"].all (fun version =>
      errorAdmitted { errorBuild with version := version }) = true := by
  decide +kernel

theorem legacy_error_rejected :
    errorAdmitted { errorBuild with version := "2.2.2" } = false := by decide +kernel

theorem outside_error_range_rejected :
    ["4.0.0", "3.0.2-rc.1"].all (fun version =>
      !errorAdmitted { errorBuild with version := version }) = true := by
  decide +kernel

end SolanalibTest.Specs.Core.ErrorNullableProfiles
