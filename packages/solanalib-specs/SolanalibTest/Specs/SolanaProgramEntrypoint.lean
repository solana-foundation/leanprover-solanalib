/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgramEntrypoint
public import SolanalibTest.Specs.Core.EntryDeserialize
public import Solanalib.Specs.SolanaProgramEntrypoint.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SolanaProgramEntrypoint.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def deserializeBuild : Versioning.Build where
  package := "solana-program-entrypoint"
  version := "2.2.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-account-info", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def deserializeCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-2.2.1; eligible
  (deserializeBuild, true),
  -- inspected-reference-2.3.0; eligible
  ({ deserializeBuild with version := "2.3.0" }, true),
  -- lower; eligible
  (deserializeBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ deserializeBuild with version := "2.2.98" }, true),
  -- exclusive-upper; unsupported
  ({ deserializeBuild with version := "3.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ deserializeBuild with version := "2.2.1-rc.1" }, false),
  -- wrong-package; unsupported
  ({ deserializeBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ deserializeBuild with source := ⟨"git", "https://example.invalid/review-fork", "bbbbbb\
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- dependency-reference-solana-account-info-2.2.1; eligible
  (deserializeBuild, true),
  -- dependency-reference-solana-account-info-2.3.0; eligible
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.3.0" } else
    dependency)) }, true),
  -- dependency-solana-account-info-lower; eligible
  (deserializeBuild, true),
  -- dependency-solana-account-info-hypothetical-declaration-probe; eligible
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-account-info-exclusive-upper; unsupported
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-account-info-unlisted-prerelease; unsupported
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.2.1-rc\
      .1" }
    else dependency)) }, false),
  -- missing-dependency-solana-account-info; unresolved
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-account-info")) }, false),
  -- wrong-dependency-origin-solana-account-info; unsupported
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-account-info" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-account-info; ValueError containing Ambiguous dependency
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies ++ [⟨"solana-acco\
    unt-info", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-2.2.0; unsupported
  ({ deserializeBuild with version := "2.2.0" }, false),
  -- dependency-solana-account-info-below-lower-bound-fixture-2.2.0; unsupported
  ({ deserializeBuild with dependencies := (deserializeBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-account-info" then { dependency with version := "2.2.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem deserialize_profile_controls :
    deserializeCases.all (fun test =>
      (((Solanalib.Specs.SolanaProgramEntrypoint.Capabilities.catalog.applicability
        .deserialize).any
        (fun profile => ["entry-deserialize-2-3-0"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem deserialize_callable_identities :
    ["2.2.1", "2.3.0", "2.2.98"].all (fun version =>
      (((Solanalib.Specs.SolanaProgramEntrypoint.Capabilities.catalog.forBuild
        { deserializeBuild with version := version }).identities .deserialize).eraseDups ==
        [⟨"solana-program-entrypoint", version, "solana_program_entrypoint::deserialize",
          "solana_program_entrypoint::deserialize"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaProgramEntrypoint.Pr575Compatibility
