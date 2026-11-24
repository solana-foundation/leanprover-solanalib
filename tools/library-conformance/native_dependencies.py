# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Resolve exact model providers afresh and authenticate the packages actually compiled."""

from functools import lru_cache
import json
import os
from pathlib import Path
import re
import tomllib
from urllib.parse import urlsplit
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parent
CRATES_IO = 'registry+https://github.com/rust-lang/crates.io-index'
VERSION = re.compile(r'\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?\Z')
PROFILES = {'dev', 'abort', 'wrapping', 'optimized'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_cargo(directory):
    return tomllib.loads((Path(directory) / 'Cargo.toml').read_text())


def workspace(directory):
    directory = Path(directory).resolve()
    name = read_cargo(directory)['package'].get('workspace')
    require(isinstance(name, str), f'{directory.name}: driver requires an explicit workspace')
    result = directory / name
    require(not result.is_symlink() and result.resolve().parent == directory.parent / 'workspaces',
            f'{directory.name}: workspace must be under rust/workspaces')
    result = result.resolve()
    members = read_cargo(result).get('workspace', {}).get('members', [])
    require(directory in {(result / member).resolve() for member in members},
            f'{directory.name}: workspace does not list the driver')
    return result


def profile(directory, selected):
    require(selected in PROFILES, f'Unknown recording profile: {selected}')
    profiles = read_cargo(workspace(directory)).get('profile', {})
    result = {'panic': 'unwind', 'opt-level': 0, 'debug-assertions': True, 'overflow-checks': True}
    active = set()

    def inherit(name):
        require(name in profiles and name not in active, f'Missing or cyclic Cargo profile: {name}')
        active.add(name)
        values = profiles[name]
        if name != 'dev':
            inherit(values.get('inherits'))
        result.update({key: value for key, value in values.items() if key != 'inherits'})
        active.remove(name)

    inherit(selected)
    return {'profile': selected, 'panic': result['panic'], 'opt_level': str(result['opt-level']),
            'debug_assertions': result['debug-assertions'], 'overflow_checks': result['overflow-checks']}


def pins(directory):
    """Exact external dependency constraints; optional pin aliases enable no additional features."""
    result = {}
    for alias, value in read_cargo(directory).get('dependencies', {}).items():
        spec = {'version': value} if isinstance(value, str) else value
        require(isinstance(spec, dict), f'Invalid dependency: {alias}')
        if 'path' in spec:
            continue
        name = spec.get('package', alias)
        version = spec.get('version')
        if version is not None:
            require(isinstance(version, str) and version.startswith('=') and VERSION.fullmatch(version[1:]),
                    f'{Path(directory).name}: {alias} needs an exact =version pin')
            version = version[1:]
        if 'git' in spec:
            url, revision = spec['git'], spec.get('rev')
            parsed = urlsplit(url)
            require(parsed.scheme == 'https' and parsed.netloc == 'github.com' and not parsed.query
                    and not parsed.fragment and not parsed.username and not parsed.password
                    and isinstance(revision, str) and re.fullmatch(r'[a-f0-9]{40}', revision),
                    f'{alias}: Git dependencies require a public HTTPS origin and exact revision')
            source = 'git+' + url + '?rev=' + revision + '#' + revision
        else:
            require(version is not None and 'registry' not in spec, f'{alias}: missing crates.io version')
            source = CRATES_IO
        optional = spec.get('optional', False)
        require(type(optional) is bool, f'{alias}: invalid optional flag')
        if alias.startswith('pin-'):
            require(optional and spec.get('default-features') is False and not spec.get('features'),
                    f'{alias}: a transitive constraint must be optional and enable no features')
        result[alias] = {'name': name, 'version': version, 'source': source, 'optional': optional}
    return result


@lru_cache(maxsize=None)
def registry(root=ROOT):
    from solana_source_map import load_source_map
    return load_source_map(Path(root).parents[1] / 'packages/solanalib-specs')


@lru_cache(maxsize=None)
def reviewed_checksums(root=ROOT):
    return {(row['package'], version): release['sha256']
            for row in registry(root)['applicability_sources'].values() if row['source']['kind'] == 'registry'
            for version, release in row['releases'].items()}


@lru_cache(maxsize=None)
def modeled_crates(root=ROOT):
    document = registry(root)
    names = {row['crate'].rpartition('-')[0] for row in document['interfaces']}
    names.update(row['package'] for row in document['applicability_sources'].values())

    def providers(value):
        if isinstance(value, dict):
            for key, child in value.items():
                if key == 'dependencies' and isinstance(child, list):
                    names.update(row['package'] for row in child)
                providers(child)
        elif isinstance(value, list):
            for child in value:
                providers(child)

    providers(document['applicability'])
    extra = tomllib.loads((Path(root) / 'native-pins.toml').read_text())
    for group in extra.values():
        require(isinstance(group.get('reason'), str) and group['reason'], 'Missing provider scope')
        require(isinstance(group.get('packages'), list) and all(isinstance(x, str) and x for x in group['packages']),
                'Invalid provider package list')
        names.update(group['packages'])
    return frozenset(names)


def _matches(pin, name, entry):
    return (pin['name'] == name and (pin['version'] is None or pin['version'] == entry['version'])
            and pin['source'] == entry['source'])


def validate_resolution(directory, receipt, checksums=None):
    """Check selected versions/origins against every exact constraint without running Cargo."""
    constraints = pins(directory)
    require(isinstance(receipt, dict) and set(receipt) == {'modeled', 'unused_pins'}, 'Invalid resolution receipt')
    records = receipt['modeled']
    require(isinstance(records, dict), 'Invalid modeled-package records')
    used = set()
    for name, entries in records.items():
        require(isinstance(name, str) and isinstance(entries, list) and entries, 'Invalid modeled package')
        seen = set()
        for entry in entries:
            require(isinstance(entry, dict) and set(entry) in ({'version', 'source'}, {'version', 'source', 'checksum'}),
                    f'{name}: invalid resolved package fields')
            require(isinstance(entry['version'], str) and VERSION.fullmatch(entry['version']), f'{name}: invalid version')
            require(isinstance(entry['source'], str), f'{name}: invalid source')
            if entry['source'] == CRATES_IO:
                require(isinstance(entry.get('checksum'), str) and re.fullmatch(r'[a-f0-9]{64}', entry['checksum']),
                        f'{name}: missing published archive checksum')
                expected = (checksums or {}).get((name, entry['version']))
                require(expected is None or entry['checksum'] == expected, f'{name}: reviewed archive checksum differs')
            else:
                require('checksum' not in entry, f'{name}: Git source cannot have a registry checksum')
            identity = entry['version'], entry['source']
            require(identity not in seen, f'{name}: repeated resolved package')
            seen.add(identity)
            matches = {alias for alias, pin in constraints.items() if _matches(pin, name, entry)}
            require(matches, f'{name}@{entry["version"]}: modeled dependency has no matching exact version/origin pin')
            used.update(matches)
    unused = sorted(set(constraints) - used)
    require(receipt['unused_pins'] == unused, 'Resolved package inventory or unused pins differ')
    require(all(constraints[alias]['optional'] for alias in unused), 'A required direct dependency was not compiled')
    return records


def selected_version(directory, receipt, crate):
    records = validate_resolution(directory, receipt)
    entries = records.get(crate, [])
    # Prefer an actual direct dependency over optional transitive constraints.
    direct = [entry for entry in entries for alias, pin in pins(directory).items()
              if not alias.startswith('pin-') and not pin['optional'] and _matches(pin, crate, entry)]
    identities = {(entry['version'], entry['source']) for entry in direct or entries}
    return next(iter(identities))[0] if len(identities) == 1 else None


def compiled_resolution(directory, metadata, units, modeled):
    """Intersect Cargo metadata with the selected compiler unit graph, excluding other members."""
    directory = Path(directory)
    packages = {package['id']: package for package in metadata['packages']}
    roots = [units['units'][index] for index in units['roots']]
    require(roots and all(Path(packages[unit['pkg_id']]['manifest_path']).resolve() == (directory / 'Cargo.toml').resolve()
                          for unit in roots), 'Compiler unit graph selected a different driver')
    selected = {unit['pkg_id'] for unit in units['units']}
    require(selected <= packages.keys(), 'Compiler units and Cargo metadata disagree')
    constraints = pins(directory)
    names = set(modeled) | {pin['name'] for pin in constraints.values()}
    lock = tomllib.loads((workspace(directory) / 'Cargo.lock').read_text())['package']
    checksums = {(p['name'], p['version'], p.get('source')): p.get('checksum') for p in lock}
    records = {}
    for key in sorted(selected):
        package = packages[key]
        name, version, source = package['name'], package['version'], package['source']
        if name not in names:
            continue
        require(source is not None, f'{name}: a local package cannot replace a modeled upstream provider')
        entry = {'version': version, 'source': source}
        if source == CRATES_IO:
            entry['checksum'] = checksums.get((name, version, source))
        records.setdefault(name, []).append(entry)
    records = {name: sorted(entries, key=lambda entry: (entry['version'], entry['source'])) for name, entries in sorted(records.items())}
    unused = sorted(alias for alias, pin in constraints.items()
                    if not any(_matches(pin, name, entry) for name, entries in records.items() for entry in entries))
    receipt = {'modeled': records, 'unused_pins': unused}
    validate_resolution(directory, receipt)
    observed = []
    for root in roots:
        value = root['profile']
        observed.append({'profile': value['name'], 'panic': value['panic'], 'opt_level': value['opt_level'],
                         'debug_assertions': value['debug_assertions'], 'overflow_checks': value['overflow_checks']})
    require(all(value == observed[0] for value in observed), 'Driver roots use different compilation profiles')
    return receipt, observed[0]


def index_path(name):
    require(isinstance(name, str) and re.fullmatch(r'[a-z0-9_-]+', name), 'Invalid crates.io package name')
    return ('1/' + name if len(name) == 1 else '2/' + name if len(name) == 2 else
            '3/' + name[0] + '/' + name if len(name) == 3 else name[:2] + '/' + name[2:4] + '/' + name)


def yanked_entry(name, version, offline=False):
    """Authenticate an exact yanked release against the public sparse registry entry."""
    path = index_path(name)
    if offline:
        cargo = Path(os.environ.get('CARGO_HOME', Path.home() / '.cargo'))
        caches = list((cargo / 'registry/index').glob('index.crates.io-*/.cache/' + path))
        require(len(caches) == 1, f'No unambiguous cached public index entry for {name}; resolve online')
        rows = [json.loads(part) for part in caches[0].read_bytes().split(b'\0') if part.startswith(b'{')]
    else:
        with urlopen('https://index.crates.io/' + path, timeout=60) as response:
            rows = [json.loads(line) for line in response.read().decode().splitlines()]
    selected = [row for row in rows if row.get('name') == name and row.get('vers') == version]
    require(len(selected) == 1 and selected[0].get('yanked') is True
            and isinstance(selected[0].get('cksum'), str) and re.fullmatch(r'[a-f0-9]{64}', selected[0]['cksum']),
            f'{name}@{version}: expected one yanked public release with a checksum')
    return {'name': name, 'version': version, 'source': CRATES_IO, 'checksum': selected[0]['cksum']}


def seed_contents(entries):
    """Only exact yanked package identities: no dependency graph or incidental version pins."""
    return 'version = 4\n' + ''.join('\n[[package]]\n' + ''.join(
        key + ' = ' + json.dumps(entry[key]) + '\n' for key in ('name', 'version', 'source', 'checksum'))
        for entry in entries)


def constrain_modeled(directory, runner, metadata, modeled, offline=False):
    """Use explicit model pins when an upstream broad range selects another compatibility line."""
    members = read_cargo(directory)['workspace']['members']
    constraints = [pin for member in members for pin in pins(directory / member).values()]
    names = set(modeled) | {pin['name'] for pin in constraints}
    seen = set()
    while True:
        unexpected = [row for row in metadata['packages'] if row['name'] in names and row['source'] is not None
                      and not any(_matches(pin, row['name'], row) for pin in constraints)]
        if not unexpected:
            return metadata
        row = unexpected[0]
        identity = row['name'], row['version'], row['source']
        choices = {pin['version'] for pin in constraints if pin['name'] == row['name']
                   and pin['source'] == row['source'] and pin['version'] is not None}
        require(row['source'] == CRATES_IO and len(choices) == 1 and identity not in seen,
                f'{row["name"]}@{row["version"]}: no unique exact modeled dependency selection; review the driver pins')
        seen.add(identity)
        selected = next(iter(choices))
        flags = ['--offline'] if offline else []
        name = f'constrain-{directory.name}-{len(seen)}'
        runner.run(name, ['cargo', 'update', '-p', row['id'], '--precise', selected, *flags], directory)
        _, output = runner.run(name + '-metadata', ['cargo', 'metadata', '--format-version', '1', '--locked', *flags],
                               directory, stdout_only=True)
        metadata = json.loads(output)


def fresh_resolution(directory, runner, offline=False, modeled=None):
    """Discard previous resolutions, retaining yanked exact releases through temporary entries."""
    directory = Path(directory)
    lock = directory / 'Cargo.lock'
    require(not lock.is_symlink(), 'A temporary resolution file cannot be a symlink')
    lock.unlink(missing_ok=True)
    entries = []
    seen = set()
    while True:
        if entries:
            lock.write_text(seed_contents(entries))
        name = f'resolve-{directory.name}-{len(entries)}'
        # Keep all target alternatives here: driver Rust flags select the Solana cfg.
        # The compiler unit graph later identifies the packages of the actual target.
        command = ['cargo', 'metadata', '--format-version', '1']
        if offline:
            command.append('--offline')
        code, output = runner.run(name, command, directory, check=False, stdout_only=True)
        if code == 0:
            data = json.loads(output)
            (runner.evidence / f'{directory.name}-yanked-releases.json').write_text(json.dumps(entries, indent=2) + '\n')
            return constrain_modeled(directory, runner, data, modeled, offline) if modeled is not None else data
        error = (runner.evidence / f'run-{name}.log').read_text()
        match = re.search(r'failed to select a version for the requirement `([a-z0-9_-]+) = "=([^"`]+)"`\s*'
                          r'version \2 is yanked', error)
        require(match is not None, f'{name} failed; see {runner.evidence / ("run-" + name + ".log")}')
        identity = match.group(1), match.group(2)
        require(identity not in seen and VERSION.fullmatch(identity[1]), f'Cannot resolve exact yanked release: {identity}')
        seen.add(identity)
        entries.append(yanked_entry(*identity, offline=offline))
