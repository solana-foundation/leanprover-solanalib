/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Versioning

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Contracts.Model.Versioning

/-- A registry identity cannot be replaced by a git fork of the same version. -/
def cratesIo : Source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- A profile with a reviewed release hole and behavior-changing build facts. -/
def reviewed : Profile where
  id := "example-read"
  package := "example-sdk"
  source := cratesIo
  releases := ["1.0.0", "1.2.0"]
  item := "example_sdk::read"
  implementation := "example_sdk::read"
  target := [⟨"os", ["solana"], [], "Select the runtime implementation."⟩]
  features := { all := ["checked"], none := ["legacy"], reason := "Select the checked \
    behavior." }
  dependencies := [{
    package := "codec"
    source := some cratesIo
    releases := ["2.0.0"]
    reason := "Preserve returned error kinds." }]
  conditions := ["The selected operation retains its original ownership and callback \
    conditions."]
  argument := "Reviewed source alternatives for this synthetic matcher control."
  evidence := ["synthetic test"]

/-- Concrete compilation facts satisfying the reviewed profile. -/
def selected : Build where
  package := "example-sdk"
  version := "1.2.0"
  source := cratesIo
  target := [⟨"os", "solana"⟩]
  features := some ["checked", "unrelated"]
  dependencies := [⟨"codec", "2.0.0", cratesIo⟩]

example : reviewed.matches selected = true := by decide +kernel

-- The numeric interval between two reviewed releases supplies no permission.
example : reviewed.matches { selected with version := "1.1.0" } = false := by decide +kernel
example : reviewed.matches { selected with version := "1.2.1" } = false := by decide +kernel
example : reviewed.matches { selected with version := "1.2.0-rc.1" } = false := by decide +kernel

/-- Compatibility extends a selected source mapping, not its list of reviewed
references. The same source, feature and dependency constraints still apply. -/
def compatible : Profile := { reviewed with
  compatibleRanges := [⟨"1.2.0", "2.0.0"⟩]
  dependencies := [{
    package := "codec"
    source := some cratesIo
    releases := ["2.0.0"]
    compatibleRanges := [⟨"2.0.0", "3.0.0"⟩]
    reason := "Assume the reference error contract is preserved." }] }

example : compatible.matches { selected with
    version := "1.10.0+build.7"
    dependencies := [⟨"codec", "2.3.1", cratesIo⟩] } = true := by decide +kernel
example : compatible.matches { selected with version := "2.0.0" } = false := by decide +kernel
example : compatible.matches { selected with version := "1.3.0-rc.1" } = false := by decide +kernel
example : compatible.matches { selected with dependencies := [] } = false := by decide +kernel
example : compatible.matches { selected with dependencies :=
    [⟨"codec", "3.0.0", cratesIo⟩] } = false := by decide +kernel
example : compatible.matches { selected with source :=
    ⟨"git", "https://example.org/fork", "0123456789012345678901234567890123456789"⟩ } = false :=
  by decide +kernel

example : ({ lower := "0.10.0", upper := "0.11.0" } : ReleaseRange).matches "0.10.99" = true := by
  decide +kernel
example : ({ lower := "0.10.0", upper := "0.11.0" } : ReleaseRange).matches "0.11.0" = false := by
  decide +kernel
example : ({ lower := "0.0.3", upper := "0.0.4" } : ReleaseRange).matches "0.0.3+build.7" = true :=
  by decide +kernel
example : ({ lower := "0.0.3", upper := "0.0.4" } : ReleaseRange).matches "0.0.4" = false := by
  decide +kernel
-- Invalid, cross-line or prerelease bounds cannot select an unreviewed version.
example : ({ lower := "0.10.0", upper := "0.12.0" } : ReleaseRange).matches "0.11.0" = false := by
  decide +kernel
example : ({ lower := "0.0.3", upper := "0.0.5" } : ReleaseRange).matches "0.0.4" = false := by
  decide +kernel
example : ({ lower := "1.2.0", upper := "3.0.0" } : ReleaseRange).matches "2.1.0" = false := by
  decide +kernel
example : ({ lower := "1.2.0-rc.1", upper := "2.0.0" } : ReleaseRange).matches "1.3.0" = false :=
  by decide +kernel
example : ({ lower := "1.2.0", upper := "2.0.0" } : ReleaseRange).matches "01.3.0" = false := by
  decide +kernel
example : ({ lower := "1.2.0", upper := "2.0.0" } : ReleaseRange).matches "1.3.0+" = false := by
  decide +kernel

-- Unknown facts are distinct from known disabled features or a different target.
example : reviewed.matches { selected with target := [] } = false := by decide +kernel
example : reviewed.matches { selected with target := [⟨"os", "linux"⟩] } = false := by
  decide +kernel
example : reviewed.matches { selected with features := none } = false := by decide +kernel
example : reviewed.matches { selected with features := some [] } = false := by decide +kernel
example : reviewed.matches { selected with features := some ["checked", "legacy"] } = false :=
  by decide +kernel

-- A different source or an ambiguous dependency selection is not admitted.
example : reviewed.matches { selected with source :=
    ⟨"git", "https://example.org/fork", "0123456789012345678901234567890123456789"⟩ } = false :=
  by decide +kernel
example : reviewed.matches { selected with dependencies := [] } = false := by decide +kernel
example : reviewed.matches { selected with dependencies :=
    [⟨"codec", "2.0.0", cratesIo⟩, ⟨"codec", "3.0.0", cratesIo⟩] } = false := by decide +kernel
example : reviewed.matches { selected with target :=
    [⟨"os", "linux"⟩, ⟨"os", "solana"⟩] } = false := by decide +kernel

/-- An unconstrained pure function needs no irrelevant feature or target facts. -/
def pureProfile : Profile :=
  { reviewed with target := [], features := {}, dependencies := [] }

example : pureProfile.matches
    {
      package := "example-sdk", version := "1.2.0", source := cratesIo } = true := by decide +kernel

/-- A mathematical identity operation for checking that selection preserves
the complete contract, rather than reconstructing a weaker value-only model. -/
def identityFamily : Family where
  Index := ULift.{1} Nat
  State := fun _ => Nat
  Args := fun _ => Nat
  Value := fun _ => Nat
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun index => .returning
    (fun before arg => before = index.down ∧ arg = index.down)
    (fun before arg result after => result = arg ∧ after = before)

/-- One source function with its original generic family and provenance. -/
def catalog : Capabilities.Catalog where
  Key := Unit
  family := fun _ => identityFamily
  modelId := fun _ => "example::read"
  kind := fun _ => .full
  identities := fun _ => [⟨"example-sdk", "1.0.0", reviewed.item, reviewed.implementation⟩]
  applicability := fun _ => [reviewed]

example : (catalog.forBuild selected).identities () =
    [⟨"example-sdk", "1.2.0", "example_sdk::read", "example_sdk::read"⟩] := by decide +kernel

example : (catalog.forBuild { selected with version := "1.1.0" }).identities () = [] :=
  by decide +kernel

-- Selecting an unsupported build does not erase the original registration.
example : ((catalog.forBuild { selected with version := "1.1.0" }).forBuild selected).identities ()
  =
    (catalog.forBuild selected).identities () := by decide +kernel

example (index : ULift.{1} Nat) : ((catalog.forBuild selected).family ()).contract index =
    (catalog.family ()).contract index := rfl

/-- A facade profile binds the actual defining crate, not the version of the facade. -/
def reexport : Capabilities.Catalog :=
  { catalog with applicability := fun _ =>
      [{ reviewed with
          identityDependency := some "codec"
          item := "codec::read"
          implementation := "codec::read" }] }

example : (reexport.forBuild selected).identities () =
    [⟨"codec", "2.0.0", "codec::read", "codec::read"⟩] := by decide +kernel
example : (reexport.forBuild { selected with dependencies := [] }).identities () = [] :=
  by decide +kernel

/-- Ranged facades still use the actual defining version, not a reference pin. -/
def compatibleReexport : Capabilities.Catalog :=
  { catalog with applicability := fun _ =>
      [{ compatible with
          identityDependency := some "codec"
          item := "codec::read"
          implementation := "codec::read" }] }

example : (compatibleReexport.forBuild { selected with
    version := "1.10.0", dependencies := [⟨"codec", "2.3.1", cratesIo⟩] }).identities () =
    [⟨"codec", "2.3.1", "codec::read", "codec::read"⟩] := by decide +kernel

/-- A source-less supporting model never acquires the Rust identity of its consumer. -/
def supporting : Capabilities.Catalog where
  Key := Unit
  family := fun _ => identityFamily
  modelId := fun _ => "example::supporting"
  kind := fun _ => .supporting
  identities := fun _ => []
  applicabilityConsumers := fun _ => ["example::read"]

example : (supporting.forBuild selected).identities () = [] := by decide +kernel
example : ((catalog.sum supporting).forBuild selected).identities (.inr ()) = [] :=
  by decide +kernel

/-- A versioned observation can have reviewed profiles without a source-call
registration. Those profiles never manufacture a callable Rust identity. -/
def observation : Capabilities.Catalog where
  Key := Unit
  family := fun _ => identityFamily
  modelId := fun _ => "example::observation"
  kind := fun _ => .observation
  identities := fun _ => []
  applicability := fun _ => [reviewed]

example : (observation.forBuild selected).identities () = [] := by decide +kernel
example : ((catalog.sum observation).forBuild selected).identities (.inr ()) = [] :=
  by decide +kernel

end SolanalibTest.Specs.Core.Versioning
