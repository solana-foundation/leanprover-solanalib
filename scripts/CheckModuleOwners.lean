/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Lake.Load.Workspace

/-! Check actual Lake ownership in an independent TOML workspace. -/

open Lake

def main (args : List String) : IO UInt32 := do
  let directory :: modules := args
    | throw <| IO.userError "Expected a workspace and its module inventory"
  let (elan, lean, lake) ← findInstall?
  let some lean := lean | throw <| IO.userError "Lean installation not found"
  let some lake := lake | throw <| IO.userError "Lake installation not found"
  let lakeEnv ← (Env.compute lake lean elan).toIO IO.userError
  let some ws ← (loadWorkspace { lakeEnv, wsDir := directory }).toBaseIO
    | throw <| IO.userError s!"Cannot load workspace {directory}"
  let mut invalid := modules.isEmpty
  for moduleName in modules do
    let name := moduleName.toName
    let owners := ws.packages.flatMap fun pkg =>
      pkg.leanLibs.filterMap (·.findModule? name) ++ pkg.leanExes.filterMap (·.isRoot? name)
    if owners.size != 1 then
      let descriptions := owners.map (fun m => (m.pkg.baseName, m.lib.name))
      IO.eprintln s!"{name}: expected one owner, got {descriptions}"
      invalid := true
  unless invalid do
    IO.println s!"Unique Lake ownership: {modules.length} modules"
  return if invalid then 1 else 0
