/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Contracts.Model.Versioning

/-- The Cargo source distinguishes a registry release from a git fork carrying
the same package name and version. Registry revisions are empty; git revisions
are the exact recorded commit. The registry generator validates these fields. -/
structure Source where
  /-- Either `registry` or `git`, as in the installed applicability manifest. -/
  kind : String
  /-- The canonical registry index or git repository URL. -/
  url : String
  /-- An exact git commit, or the empty string for a registry source. -/
  revision : String := ""
  deriving BEq, DecidableEq, Repr

/-- One recorded target fact, such as `os = linux` or `pointer_width = 64`.
Omitting a fact means unknown, not the setting of the host machine. -/
structure TargetFact where
  /-- The target-property name used by the applicability manifest. -/
  field : String
  /-- Its value in the compilation being interpreted. -/
  value : String
  deriving BEq, DecidableEq, Repr

/-- One dependency selected in the actual source closure of this function.
A list of alternative versions found somewhere in Cargo.lock is insufficient. -/
structure Dependency where
  /-- The selected Cargo package name. -/
  package : String
  /-- Its exact resolved version. -/
  version : String
  /-- Its resolved registry or git origin. -/
  source : Source
  deriving BEq, DecidableEq, Repr

/-- Compilation facts supplied for one library package. Their agreement with
the assessed compilation remains a source-binding obligation; this data does
not reconstruct Cargo resolution or prove Rust implementation correctness. -/
structure Build where
  /-- The Cargo package being matched to a model. -/
  package : String
  /-- Its exact resolved version. -/
  version : String
  /-- Its actual source, including a git revision when applicable. -/
  source : Source
  /-- Known target facts; omitted facts remain unknown. -/
  target : List TargetFact := []
  /-- Resolved features of this package; `none` means unknown. -/
  features : Option (List String) := none
  /-- Enabled compiler target features; `none` means unknown. -/
  targetFeatures : Option (List String) := none
  /-- The selected dependency packages needed by a reviewed profile. -/
  dependencies : List Dependency := []
  deriving BEq, DecidableEq, Repr

/-- A target condition is required only where reviewed source behavior differs. -/
structure TargetRequirement where
  /-- The target fact this condition concerns. -/
  field : String
  /-- Allowed values; an empty list places no inclusion restriction. -/
  «include» : List String := []
  /-- Disallowed values. -/
  «exclude» : List String := []
  /-- The source-level reason for the restriction. -/
  reason : String := ""
  deriving BEq, DecidableEq, Repr

/-- Feature conditions for one behavior profile, not a complete feature lock. -/
structure FeatureRequirement where
  /-- Features which must all be enabled. -/
  all : List String := []
  /-- At least one must be enabled when this list is nonempty. -/
  any : List String := []
  /-- Features which must all be disabled. -/
  none : List String := []
  /-- The observed behavior controlled by these features. -/
  reason : String := ""
  deriving BEq, DecidableEq, Repr

/-- A half-open interval of stable releases under an explicit behavioral
compatibility assumption. Bounds stay within one Cargo compatibility line:
1.x, 0.2.x and 0.0.3 have ceilings 2.0.0, 0.3.0 and 0.0.4 respectively. -/
structure ReleaseRange where
  /-- The inclusive stable lower bound. -/
  lower : String
  /-- The exclusive stable upper bound. -/
  upper : String
  deriving BEq, DecidableEq, Repr

/-- Parse a stable SemVer core, ignoring valid build metadata. -/
def stableVersion (version : String) : Option (Nat × Nat × Nat) := do
  -- List.splitOn is not exposed through the module interface of Lean. This small
  -- split keeps concrete profile selection reducible in downstream proofs.
  let split (separator : Char) (chars : List Char) : List (List Char) :=
    chars.foldr (fun c parts =>
      if c == separator then [] :: parts
      else match parts with
        | [] => [[c]]
        | first :: rest => (c :: first) :: rest) [[]]
  let core ← match split '+' version.toList with
    | [core] => some core
    | [core, metadata] =>
      if (split '.' metadata).all (fun part => !part.isEmpty &&
          part.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '-'))) then
        some core
      else none
    | _ => none
  let component (part : List Char) : Option Nat :=
    if part.isEmpty || !part.all Char.isDigit ||
        (part.length > 1 && part.head? == some '0') then none
    else some (part.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  match split '.' core with
  | [major, minor, patch] => return (← component major, ← component minor, ← component patch)
  | _ => none

/-- the exclusive compatibility ceiling of Cargo for a complete stable version. -/
def compatibilityCeiling (version : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (major, minor, patch) := version
  if major > 0 then (major + 1, 0, 0)
  else if minor > 0 then (0, minor + 1, 0)
  else (0, 0, patch + 1)

/-- Lexicographic ordering of the three numeric SemVer components. -/
def versionLt (left right : Nat × Nat × Nat) : Bool :=
  left.1 < right.1 || (left.1 == right.1 &&
    (left.2.1 < right.2.1 || (left.2.1 == right.2.1 && left.2.2 < right.2.2)))

/-- Stable release membership; build metadata is irrelevant to Cargo version
ordering. Prereleases require an exact reviewed entry. Invalid bounds cannot
broaden selection, even for a profile constructed directly in Lean. -/
def ReleaseRange.matches (range : ReleaseRange) (version : String) : Bool :=
  match stableVersion range.lower, stableVersion range.upper, stableVersion version with
  | some lower, some upper, some actual =>
    !range.lower.toList.contains '+' && !range.upper.toList.contains '+' &&
      versionLt lower upper && !versionLt (compatibilityCeiling lower) upper &&
      !versionLt actual lower && versionLt actual upper
  | _, _, _ => false

/-- Exact references remain eligible; only registry sources may use declared
compatible intervals. Git revisions never acquire range-based eligibility. -/
def releaseMatches (releases : List String) (ranges : List ReleaseRange)
    (source : Option Source) (version : String) : Bool :=
  releases.contains version ||
    (source.any (fun origin => origin.kind == "registry") &&
      ranges.any (fun range => range.matches version))

/-- A constraint on a selected dependency when it changes the observable behavior of the modeled
API. These are build facts, not additional callee contracts. -/
structure DependencyRequirement where
  /-- The dependency whose actual selected version matters. -/
  package : String
  /-- A required origin, when the source review distinguishes it. -/
  source : Option Source := none
  /-- Exactly the dependency releases covered by the review. -/
  releases : List String
  /-- The public behavioral distinction requiring this condition. -/
  reason : String := ""
  /-- Supported compatible intervals, separate from the reviewed references.
  Their use assumes preservation of the modeled behavior of the operation. -/
  compatibleRanges : List ReleaseRange := []
  deriving BEq, DecidableEq, Repr

/-- One source operation and its relevant build conditions. Exact reviewed
releases and explicitly assumed compatibility ranges are distinct evidence.
Neither source review nor SemVer supplies a Rust correctness theorem. -/
structure Profile where
  /-- The stable identifier of this reviewed alternative. -/
  id : String
  /-- The package containing this operation. -/
  package : String
  /-- The reviewed registry or exact git origin. -/
  source : Source
  /-- Exact reviewed releases, with holes and prereleases preserved. -/
  releases : List String
  /-- The source item through which this operation is called. -/
  item : String
  /-- The implementation path used in the reviewed releases. -/
  implementation : String
  /-- The defining package of a reexport, selected from the actual dependencies.
  `none` means that the matched package itself defines the operation. -/
  identityDependency : Option String := none
  /-- Behavior-changing target conditions; all must hold. -/
  target : List TargetRequirement := []
  /-- Behavior-changing Cargo feature conditions. -/
  features : FeatureRequirement := {}
  /-- Behavior-changing compiler target-feature conditions. -/
  targetFeatures : FeatureRequirement := {}
  /-- Constraints on actual selected dependencies. -/
  dependencies : List DependencyRequirement := []
  /-- Existing generic-index, ownership, provider and interpretation obligations.
These remain obligations; the Boolean matcher does not discharge them. -/
  conditions : List String := []
  /-- The source correspondence argument for this profile. -/
  argument : String := ""
  /-- Immutable source or review references supporting that argument. -/
  evidence : List String := []
  /-- Supported compatible intervals for this exact source-item mapping.
  Empty means that only the explicit reviewed releases are admitted. -/
  compatibleRanges : List ReleaseRange := []
  deriving BEq, DecidableEq, Repr

/-- Retrieve a unique target fact. Conflicting or duplicate facts cannot select
an arbitrary value and accidentally satisfy a profile. -/
def Build.targetValue (build : Build) (field : String) : Option String :=
  match build.target.filter (fun fact => fact.field == field) with
  | [fact] => some fact.value
  | _ => none

/-- Retrieve the unique actual dependency rather than an arbitrary lockfile
candidate sharing its package name. -/
def Build.dependency (build : Build) (package : String) : Option Dependency :=
  match build.dependencies.filter (fun dependency => dependency.package == package) with
  | [dependency] => some dependency
  | _ => none

/-- The defining package of this source identity. Reexports keep the version of the actual
provider, rather than the facade version through which it was used. -/
def Profile.identityPackage (profile : Profile) (build : Build) : Option Dependency :=
  match profile.identityDependency with
  | .none => some ⟨build.package, build.version, build.source⟩
  | .some package => build.dependency package

/-- A constrained target property must be known and satisfy both restrictions. -/
def TargetRequirement.matches (requirement : TargetRequirement) (build : Build) : Bool :=
  if requirement.include.isEmpty && requirement.exclude.isEmpty then true
  else match build.targetValue requirement.field with
    | .none => false
    | .some value =>
      (requirement.include.isEmpty || requirement.include.contains value) &&
        !requirement.exclude.contains value

/-- Unrestricted features need no supplied feature list. Any actual restriction
requires the resolved feature set of the selected package. -/
def FeatureRequirement.matches (requirement : FeatureRequirement)
    (actual : Option (List String)) : Bool :=
  if requirement.all.isEmpty && requirement.any.isEmpty && requirement.none.isEmpty then true
  else match actual with
    | .none => false
    | .some features =>
      requirement.all.all features.contains &&
        (requirement.any.isEmpty || requirement.any.any features.contains) &&
        requirement.none.all (fun feature => !features.contains feature)

/-- Match the unique selected dependency. Multiple versions with the same name
are ambiguous here, even if one of them would satisfy the release constraint. -/
def DependencyRequirement.matches (requirement : DependencyRequirement)
    (build : Build) : Bool :=
  match build.dependency requirement.package with
  | .some dependency =>
    releaseMatches requirement.releases requirement.compatibleRanges requirement.source
      dependency.version &&
      (match requirement.source with
       | .none => true
       | .some source => dependency.source == source)
  | .none => false

/-- Select a declared source/version/build alternative. Unknown required facts
fail this check; model and compatibility assumptions remain explicit. -/
def Profile.matches (profile : Profile) (build : Build) : Bool :=
  build.package == profile.package && build.source == profile.source &&
    releaseMatches profile.releases profile.compatibleRanges (some profile.source) build.version &&
    profile.target.all (fun requirement => requirement.matches build) &&
    profile.features.matches build.features &&
    profile.targetFeatures.matches build.targetFeatures &&
    profile.dependencies.all (fun requirement => requirement.matches build)

end Solanalib.Contracts.Model.Versioning
