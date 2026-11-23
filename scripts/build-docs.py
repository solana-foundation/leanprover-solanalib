#!/usr/bin/env python3
"""Render one site for every owned production module and its import closure.

All public libraries share the artifact directory of the root package. The pinned
loader uses ordinary LEAN_PATH resolution, without an artifact overlay.
"""
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / '.lake/build'
sys.path.insert(0, str(ROOT / 'tools/model-audit'))
from import_tiers import header_imports

CORE = {'Init', 'Std', 'Lean', 'Lake'}


def public_sources():
    modules = {}
    for package in [ROOT, *sorted((ROOT / 'packages').glob('*'))]:
        paths = sorted((package / 'Solanalib').rglob('*.lean'))
        if (package / 'Solanalib.lean').is_file():
            paths.append(package / 'Solanalib.lean')
        for path in paths:
            name = '.'.join(path.relative_to(package).with_suffix('').parts)
            if name in modules:
                raise ValueError('Duplicate production source: ' + name)
            modules[name] = path
    return dict(sorted(modules.items()))


def public_modules():
    return list(public_sources())


def render_roots(modules):
    # fromDb follows transitive imports. Passing only graph roots also avoids
    # the compound-SELECT limit of SQLite when the package has over 500 modules.
    imported = {'.'.join(parts) for source in modules.values()
                for _, parts in header_imports(source.read_text())}
    return sorted(set(modules) - imported)


def lake_environment():
    # Read only the build-related variables; never serialize credentials.
    command = ['lake', '-Kenv=dev', 'env', sys.executable, '-c',
               'import json, os; print(json.dumps({k: os.environ.get(k) for k in '
               '["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH", "PATH"]}))']
    variables = json.loads(subprocess.check_output(command, cwd=ROOT, text=True))
    environment = os.environ.copy()
    environment.update({key: value for key, value in variables.items() if value is not None})
    return environment


def import_closure(modules, environment):
    directories = list(dict.fromkeys(Path(p).resolve() for p in environment['LEAN_SRC_PATH'].split(os.pathsep) if p))
    sources = dict(modules)
    pending = list(modules)
    visited = set()
    while pending:
        name = pending.pop()
        if name in visited or name.split('.')[0] in CORE:
            continue
        visited.add(name)
        if name not in sources:
            relative = Path(*name.split('.')).with_suffix('.lean')
            found = {directory / relative for directory in directories if (directory / relative).is_file()}
            if len(found) != 1:
                raise ValueError(f'Expected one source for imported module {name}: {sorted(map(str, found))}')
            sources[name] = found.pop()
        pending += ['.'.join(parts) for _, parts in header_imports(sources[name].read_text())]
    return {name: sources[name] for name in sorted(visited)}


@lru_cache(maxsize=None)
def repository_info(directory):
    directory = Path(directory)
    if not (directory / '.git').exists():
        if directory.parent == directory:
            raise ValueError('Documentation source has no Git provenance')
        return repository_info(str(directory.parent))
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
    remote = subprocess.check_output(['git', 'config', '--get', 'remote.origin.url'], cwd=directory, text=True).strip()
    if remote.startswith('git@github.com:'):
        remote = 'https://github.com/' + remote.split(':', 1)[1]
    parsed = urlsplit(remote)
    if parsed.hostname != 'github.com':
        raise ValueError('Documentation source requires a GitHub origin: ' + str(directory))
    # Exclude any URL credentials, query or fragment from published source links.
    url = 'https://github.com' + parsed.path.removesuffix('.git')
    return directory, revision, url


def source_uri(source):
    directory, revision, url = repository_info(str(source.parent))
    return f'{url}/blob/{revision}/{source.relative_to(directory).as_posix()}'


def documentation_warnings(modules, logs):
    # The pinned generator has a hard-coded per-declaration heartbeat budget.
    # Keep its two known presentation gaps visible; do not hide new failures.
    known = {
        'Solanalib.Specs.Core.AnchorSplSupport.Admission':
            'Failed to obtain information for: Solanalib.Specs.Core.AnchorSplSupport.Ready:',
        'Solanalib.Specs.AnchorLang.Capabilities':
            'Failed to calculate equational lemmata for Solanalib.Specs.AnchorLang.Capabilities.reference:',
    }
    warnings = []
    for name in modules:
        output = (logs / (name + '.log')).read_text()
        for line in output.splitlines():
            if not line.startswith('WARNING:'):
                continue
            if (name not in known or not line.startswith('WARNING: ' + known[name])
                    or 'maximum number of heartbeats (5000)' not in output):
                raise SystemExit(f'Unexpected documentation warning in {name}: {line}')
            warnings.append({'module': name, 'message': line,
                             'source': str(modules[name].relative_to(ROOT))})
            print('Documentation presentation limitation: ' + line.removeprefix('WARNING: '))
    return warnings


def main():
    modules = public_sources()
    subprocess.run(['lake', '-R', '-Kenv=dev', 'build', 'doc-gen4/coreDocs',
                    'doc-gen4/bibPrepass', *('+' + name for name in modules)], cwd=ROOT, check=True)
    environment = lake_environment()
    sources = import_closure(modules, environment)
    executable = ROOT / '.lake/packages/doc-gen4/.lake/build/bin/doc-gen4'
    if os.name == 'nt':
        executable = executable.with_suffix('.exe')
    records = {name: {'source': str(source.relative_to(ROOT)), 'uri': source_uri(source)}
               for name, source in sources.items()}
    (BUILD / 'doc-source-manifest.json').write_text(json.dumps(records, indent=2) + '\n')
    logs = BUILD / 'doc-logs'
    logs.mkdir(exist_ok=True)

    def generate(name):
        with (logs / (name + '.log')).open('w') as log:
            result = subprocess.run([str(executable), 'single', '--build', str(BUILD),
                                     name, 'api-docs.db', records[name]['uri']],
                                    cwd=ROOT, env=environment, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            return f'{name}: {logs / (name + ".log")}'
        return None

    # Bound concurrency explicitly: these processes import full Lean environments.
    with ThreadPoolExecutor(max_workers=4) as pool:
        failures = [failure for failure in pool.map(generate, sources) if failure]
    if failures:
        raise SystemExit('Documentation extraction failed:\n' + '\n'.join(failures))
    warnings = documentation_warnings(modules, logs)
    # Stale pages cannot satisfy the coverage check.
    shutil.rmtree(BUILD / 'doc/Solanalib', ignore_errors=True)
    (BUILD / 'doc/Solanalib.html').unlink(missing_ok=True)
    manifest = BUILD / 'doc-manifest.json'
    subprocess.run([str(executable), 'fromDb', '--build', str(BUILD), '--manifest', str(manifest),
                    str(BUILD / 'api-docs.db'), *render_roots(modules), *sorted(CORE)],
                   cwd=ROOT, env=environment, check=True)
    generated = set(json.loads(manifest.read_text()))
    expected = {'doc/' + name.replace('.', '/') + '.html' for name in modules}
    missing = sorted(name for name in expected if name not in generated or not (BUILD / name).is_file())
    if missing:
        raise SystemExit('Missing generated module documentation: ' + ', '.join(missing))
    (BUILD / 'doc/solanalib-warnings.json').write_text(json.dumps(warnings, indent=2) + '\n')
    subprocess.run([sys.executable, 'scripts/postprocess-docs.py'], cwd=ROOT, check=True)
    print(f'Documentation coverage: {len(expected)} production modules; '
          f'{len(sources)} modules in the non-core import closure; one rendered site')


if __name__ == '__main__':
    main()
