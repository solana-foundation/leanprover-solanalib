#!/usr/bin/env python3
"""Check ordinary Lean lookup for every solanalib library in a Lake workspace."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    environment = os.environ.copy()
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
        environment.pop(key, None)
    inventory = subprocess.run(['lake', '--quiet', 'run', 'solanalib/libraryInventory'],
                               cwd=workspace, env=environment, check=True, capture_output=True, text=True)
    libraries = json.loads(inventory.stdout)
    if not libraries or {row['package'] for row in libraries} != {'solanalib'}:
        raise SystemExit('Expected libraries owned by the solanalib package')
    build_dirs = {str(Path(row['buildDir']).resolve()) for row in libraries}
    if len(build_dirs) != 1:
        raise SystemExit('Solanalib libraries do not share one artifact directory')
    search = subprocess.check_output(
        ['lake', 'env', sys.executable, '-c', 'import os; print(os.environ.get("LEAN_PATH", ""))'],
        cwd=workspace, env=environment, text=True).strip().split(os.pathsep)
    for root in ('Solanalib', 'SolanalibTest'):
        providers = {str(Path(entry).resolve()) for entry in search
                     if (Path(entry) / root).is_dir() or (Path(entry) / (root + '.olean')).is_file()}
        if providers != build_dirs:
            raise SystemExit(f'{root} artifacts have unexpected providers: {sorted(providers)}')
    modules = []
    for library in libraries:
        available = sorted(set(library['modules']))
        if not available:
            raise SystemExit('Library has no modules: ' + library['name'])
        modules.append(library['name'] if library['name'] in available else available[0])
    with tempfile.TemporaryDirectory(prefix='solanalib-plain-lean-') as temporary:
        probe = Path(temporary) / 'Imports.lean'
        probe.write_text(''.join('import ' + name + '\n' for name in modules))
        subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=workspace, env=environment, check=True)
        dynamic = Path(temporary) / 'Dynamic.lean'
        imports = ', '.join('{ module := `' + name + ' }' for name in modules)
        dynamic.write_text('import Lean\nopen Lean\ndef main : IO Unit := do\n'
                           '  initSearchPath (← findSysroot)\n'
                           '  let env ← importModules #[' + imports + '] {}\n'
                           '  unless env.contains `Solanalib.Runtime.Account do\n'
                           '    throw <| IO.userError "Runtime declaration missing"\n')
        subprocess.run(['lake', 'env', 'lean', '--run', str(dynamic)],
                       cwd=workspace, env=environment, check=True)
    result = {'status': 'passed', 'libraries': len(libraries), 'modules': modules,
              'one_package': 'solanalib', 'one_build_directory': True,
              'plain_lean': True, 'lean_run_import_modules': True}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f'Plain Lean loading: {len(libraries)} libraries; static and dynamic imports pass')


if __name__ == '__main__':
    main()
