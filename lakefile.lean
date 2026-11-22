import Lake
open Lake DSL

/-!
## Solanalib

A library of formal models and verified results for Solana programs.

Dependencies:
* Mathlib — algebraic infrastructure, tactics, numeric types.
* doc-gen4 — gated behind `-Kenv=dev` so casual builds don't pay its cost.
-/

package solanalib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Mathlib's style linters, enabled as warnings (CI fails on any warning).
    ⟨`weak.linter.style.longLine, true⟩,
    ⟨`weak.linter.style.lambdaSyntax, true⟩,
    ⟨`weak.linter.style.dollarSyntax, true⟩,
    ⟨`weak.linter.style.cdotPattern, true⟩,
    ⟨`weak.linter.style.commandStart, true⟩
  ]
  testDriver := "SolanalibTest"

require "leanprover-community" / "mathlib" @ git "v4.34.0"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "a6521b2d0c93dcdf2d640089f95548df5dd8bf46"

@[default_target]
lean_lib Solanalib where
  roots := #[]
  globs := #[
    .one `Solanalib,
    .one `Solanalib.Init,
    .submodules `Solanalib.Account,
    .submodules `Solanalib.Finance,
    .submodules `Solanalib.Instruction,
    .submodules `Solanalib.Numeric,
    .submodules `Solanalib.Primitives,
    .submodules `Solanalib.SBPF
  ]

lean_lib SolanalibTest where
  roots := #[]
  globs := #[
    .one `SolanalibTest,
    .one `SolanalibTest.LayerATests,
    .submodules `SolanalibTest.Account,
    .submodules `SolanalibTest.Finance,
    .submodules `SolanalibTest.Numeric,
    .submodules `SolanalibTest.SBPF
  ]

-- These libraries share one package output directory because Lean resolves modules
-- by their top-level root. Source directories remain separate for navigation.
lean_lib Solanalib.Runtime where
  srcDir := "packages/solanalib-runtime"
  roots := #[`Solanalib.Runtime]
  globs := #[.one `Solanalib.Runtime, .submodules `Solanalib.Runtime]

lean_lib SolanalibTest.Runtime where
  srcDir := "packages/solanalib-runtime"
  roots := #[`SolanalibTest.Runtime]
  globs := #[.one `SolanalibTest.Runtime, .submodules `SolanalibTest.Runtime]

lean_lib SolanalibTest.Conformance.Runtime where
  srcDir := "tools/runtime-conformance"
  roots := #[`SolanalibTest.Conformance.Runtime]

/-- Executable front end to the Lean sBPF semantics, used by the differential
testing harness (`spinoza validate`). -/
lean_exe «sbpf-oracle» where
  root := `Oracle

/-- Check real module ownership; invoked with the source inventory by the Python wrapper. -/
script checkModuleOwners (args) do
  let ws ← getWorkspace
  let mut invalid := args.isEmpty
  for arg in args do
    let name := arg.toName
    -- Workspace.findModules reports only the last matching library per package.
    -- Count all library claims and executable roots so same-package overlaps fail too.
    let owners := ws.packages.flatMap fun pkg =>
      pkg.leanLibs.filterMap (·.findModule? name) ++ pkg.leanExes.filterMap (·.isRoot? name)
    if owners.size != 1 || owners.any (fun m => m.pkg.baseName != `solanalib) then
      let descriptions := owners.map (fun m => (m.pkg.baseName, m.lib.name))
      IO.eprintln s!"{name}: expected one root-package owner, got {descriptions}"
      invalid := true
  unless invalid do
    IO.println s!"Unique Lake ownership: {args.length} modules"
  return if invalid then 1 else 0

/-- Export the actual library configuration and module inventory for audit tools. -/
script libraryInventory (args) do
  let ws ← getWorkspace
  let mut rows := #[]
  let some pkg := ws.findPackageByName? `solanalib
    | IO.eprintln "The solanalib package is not loaded"; return 1
  for lib in pkg.leanLibs do
    if args.isEmpty || args.contains lib.name.toString then
      let modules ← lib.getModuleArray
      rows := rows.push <| Lean.Json.mkObj [
        ("name", Lean.toJson lib.name.toString),
        ("package", Lean.toJson lib.pkg.baseName.toString),
        ("srcDir", Lean.toJson lib.srcDir.toString),
        ("buildDir", Lean.toJson lib.pkg.leanLibDir.toString),
        ("roots", Lean.toJson <| lib.roots.map toString),
        ("globs", Lean.toJson <| lib.config.globs.map toString),
        ("modules", Lean.toJson <| modules.map fun m => m.name.toString),
        ("files", Lean.toJson <| modules.map fun m => m.leanFile.toString)]
  IO.println (Lean.Json.compress <| Lean.toJson rows)
  return 0
