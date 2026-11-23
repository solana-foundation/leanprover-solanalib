#!/usr/bin/env python3
"""Index existing model/test gaps without creating a second coverage registry."""
import argparse
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import tomllib

from solana_source_map import load_source_map, source_map_files

ROOT = Path(__file__).resolve().parents[2]
SDK = Path('packages/solanalib-specs')
RUNTIME = Path('packages/solanalib-runtime/source-map/sources.json')
CONFORMANCE = Path('tools/library-conformance')
CENSUS = Path('docs/release-census.json')
REVIEW = Path('docs/gap-review.json')
OUTPUT = Path('docs/model-gaps.md')
EXTRA_INPUTS = [RUNTIME, CONFORMANCE / 'not-tested.toml', CONFORMANCE / 'requires-open.toml',
                CONFORMANCE / 'checker_selection.py', SDK / 'BINDINGS.md',
                Path('Solanalib/SBPF/Interpreter.lean'),
                Path('packages/solanalib-runtime/Solanalib/Runtime/Exec.lean'),
                Path('Solanalib/Transfer.lean'), CENSUS]
STATUS = {'runtime': 'recorded model scope',
          'sdk-model': 'recorded scope or remaining requirement', 'sdk-binding': 'open',
          'release-review': 'applicability review pending',
          'native-test': 'documented mathematical-only exception', 'precondition-test': 'open',
          'checker-omission': 'explicit finite coverage omission', 'cross-layer': 'open'}


def input_hashes(root):
    paths = [*source_map_files(root / SDK), *(root / path for path in EXTRA_INPUTS)]
    return {path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def records(root=ROOT):
    review = json.loads((root / REVIEW).read_text())
    if (review['schema_version'] != 1 or set(review['policies']) != set(STATUS)
            or any(set(policy) != {'affected_claims', 'resolution'}
                   for policy in review['policies'].values())):
        raise ValueError('Review policies describe claims and resolution criteria, not editable coverage status')
    if review['inputs'] != input_hashes(root):
        raise ValueError('Gap review inputs changed; review the affected records and refresh gap-review.json')
    # Validate the date without assigning a new review date during generation.
    from datetime import date
    date.fromisoformat(review['reviewed_on'])
    sdk = load_source_map(root / SDK)
    models = {row['id']: row for row in sdk['models']}
    interfaces = {row['id']: row for row in sdk['interfaces']}
    runtime = json.loads((root / RUNTIME).read_text())
    runtime_sources = {row['id']: row for row in runtime['entries']}
    rows = []

    def add(identifier, category, origin, declarations, behavior, **details):
        policy = review['policies'][category]
        rows.append({'id': identifier, 'category': category, 'origin': origin,
                     'declarations': declarations, 'recorded_behavior': behavior,
                     'status': STATUS[category], 'affected_claims': policy['affected_claims'],
                     'resolution': policy['resolution'], 'last_review': review['reviewed_on'],
                     'review_scope': review['scope'], **details})

    for row in runtime['correspondence']:
        if not row['limitations']:
            continue
        add('runtime:' + row['id'], 'runtime', RUNTIME.as_posix(), row['declarations'],
            row['limitations'], assumptions=row['assumptions'], modules=row['modules'],
            sources=[runtime_sources[name] for name in row['source_ids']],
            build_conditions={'reference_runtime': runtime['reference_runtime'],
                              'correspondence_id': row['id']},
            tests=['tools/runtime-conformance/README.md',
                   'packages/solanalib-runtime/SolanalibTest/Runtime.lean'])

    for model in sdk['models']:
        if not (model['model_gaps'] or model['remaining_requirements']):
            continue
        api = [row for row in sdk['api'] if model['id'] in row['models']]
        add('sdk-model:' + model['id'], 'sdk-model', (SDK / 'source-map.json').as_posix(),
            [model['contract']], model['model_gaps'] + model['remaining_requirements'],
            model_id=model['id'], model_kind=model['kind'], assumptions=model['assumptions'],
            sources=[interfaces[name] for name in sorted({row['source_id'] for row in api})],
            source_functions=[{'api': row['id'], 'source_id': row['source_id'],
                               'rust_names': row.get('rust_names', []), 'scope': row['scope']}
                              for row in api],
            build_conditions=sdk['applicability'][model['id']],
            tests=sorted({name for row in api for name in row.get('clients', [])}),
            witnesses=model['witnesses'] + model['satisfiability_witnesses'] +
                      model.get('execution_witnesses', []))

    source_models = sorted({name for row in sdk['api'] for name in row['models']})
    if any(models[name]['rust_proof_status'] != 'open' for name in source_models):
        raise ValueError('Source-proof status changed; update the implementation-gap presentation')
    add('sdk:rust-implementation-bindings', 'sdk-binding', (SDK / 'source-map.json').as_posix(),
        [models[name]['contract'] for name in source_models],
        ['The registered mathematical witnesses do not prove the selected Rust implementations.'],
        model_ids=source_models, api_ids=[row['id'] for row in sdk['api']],
        build_conditions={'registry': str(SDK / 'source-map/applicability.json')},
        sources=sdk['interfaces'], tests=['tools/library-conformance/README.md'],
        obligations=str(SDK / 'BINDINGS.md'))

    census = json.loads((root / CENSUS).read_text())['live_source_census']
    date.fromisoformat(census['checked_on'])
    for finding in census['findings']:
        source = sdk['applicability_sources'].get(finding['source'])
        # The public census retains the original diagnostic of verify_source_census.
        # Derive its releases rather than maintaining another editable pending-release list.
        match = re.fullmatch(r'Source census needs review: ([^;]+); '
                             r'unrecorded (\[[^\n]*\]), missing (\[[^\n]*\])', finding['error'])
        if (source is None or source['source']['kind'] != 'registry'
                or finding['status'] != 'needs review' or match is None
                or finding['package'] != source['package'] or match[1] != source['package']):
            raise ValueError('Unrecognized source census finding; review its gap presentation')
        unrecorded, missing = (ast.literal_eval(match[index]) for index in (2, 3))
        if (not isinstance(unrecorded, list) or not unrecorded or missing != []
                or any(not isinstance(version, str) or not re.fullmatch(r'[0-9]+\.[0-9]+\.[0-9]+', version)
                       for version in unrecorded)):
            raise ValueError('Unrecognized source census releases; review their gap presentation')
        affected = {name: [profile['id'] for profile in applicability.get('profiles', [])
                           if profile['source'] == finding['source']]
                    for name, applicability in sdk['applicability'].items()}
        affected = {name: profiles for name, profiles in affected.items() if profiles}
        for version in unrecorded:
            if version in source['releases']:
                raise ValueError('Release census finding is already recorded; review its gap presentation')
            add('release-review:' + source['package'] + '@' + version, 'release-review',
                CENSUS.as_posix(), [models[name]['contract'] for name in sorted(affected)],
                [f"The {census['checked_on']} census found {source['package']} {version} unrecorded; "
                 'source/build applicability review for this release remains pending.'],
                package=source['package'], version=version, source_id=finding['source'],
                census_checked_on=census['checked_on'], source=source['source'],
                last_source_review=source['reviewed_on'], model_ids=sorted(affected),
                build_conditions={'registry': str(SDK / 'source-map/applicability.json'),
                                  'profile_ids': sorted({name for profiles in affected.values() for name in profiles})},
                tests=['tools/model-audit/solana_applicability.py',
                       'tools/library-conformance/REFERENCE.md'],
                test_scope='This census finding adds no release-specific source-review or test credit.')

    for filename, category in [('not-tested.toml', 'native-test'),
                               ('requires-open.toml', 'precondition-test')]:
        source = CONFORMANCE / filename
        for row in tomllib.loads((root / source).read_text()).get('model', []):
            if row['id'] not in models:
                raise ValueError('Conformance exception names an unknown model: ' + row['id'])
            add(category + ':' + row['id'], category, source.as_posix(),
                [models[row['id']]['contract']], [row['reason']],
                model_id=row['id'], detail=row['detail'],
                build_conditions=sdk['applicability'][row['id']],
                tests=['tools/library-conformance/REFERENCE.md'])

    selection_path = root / CONFORMANCE / 'checker_selection.py'
    spec = importlib.util.spec_from_file_location('gap_checker_selection', selection_path)
    selection = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(selection)
    omissions = {corpus: [list(key) for key in sorted(keys)]
                 for corpus, keys in sorted(selection.KNOWN_OMISSIONS.items())}
    add('library-tests:registered-checker-omissions', 'checker-omission',
        (CONFORMANCE / 'checker_selection.py').as_posix(), [],
        ['The registered-checker policy permits exact native observations without a selected checker; '
         'an omitted observation or its skipped control earns no conformance credit.'],
        allowed_identities=omissions,
        build_conditions={'corpora': sorted(omissions), 'selection': '--registered-checkers'},
        tests=['tools/library-conformance/test_checker_selection.py'])

    for row in review['cross_layer']:
        for path in row['sources']:
            if not (root / path).is_file():
                raise ValueError('Missing cross-layer source: ' + path)
        add(row['id'], 'cross-layer', REVIEW.as_posix(), row['declarations'], row['behavior'],
            sources=row['sources'], build_conditions=row['build_conditions'], tests=row['tests'],
            test_scope=row['test_scope'])

    identifiers = [row['id'] for row in rows]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError('Duplicate gap identity')
    return review, rows


def text_cell(value):
    return value.replace('|', '\\|').replace('\n', ' ')


def render(review, rows):
    lines = ['# Recorded model and test boundaries', '',
             'Generated from the existing source registries, recorded release census and conformance policies by '
             '`python3.12 tools/model-audit/generate_gap_index.py`. Edit the underlying record, '
             'review changed inputs in [gap-review.json](gap-review.json), then regenerate. '
             'This index adds no model, source proof or native-test credit.', '',
             'Last index review: **' + review['reviewed_on'] + '**. ' + review['scope'], '',
             'The [authoring standard](model-standard.md) distinguishes intentional model scope, '
             'implementation bindings and missing test evidence. Assumptions are not classified as '
             'defects merely because a theorem uses them. The machine-readable `--json` output '
             'retains exact declarations, immutable source records, build-profile references, '
             'tests, status and resolution criteria; this page is their readable index.', '']
    titles = {'runtime': 'Runtime correspondence', 'sdk-model': 'SDK model scope and remaining work',
              'sdk-binding': 'Rust implementation bindings', 'release-review': 'Pending release applicability reviews',
              'native-test': 'Native test exceptions',
              'precondition-test': 'Open checker preconditions', 'checker-omission': 'Checker selection',
              'cross-layer': 'Execution connections'}
    for category, title in titles.items():
        selected = [row for row in rows if row['category'] == category]
        policy = review['policies'][category]
        lines += ['## ' + title, '', policy['affected_claims'], '',
                  '**Status:** ' + STATUS[category] + '. **Resolution criterion:** ' + policy['resolution'], '',
                  '| Stable ID | Affected declarations or selection | Canonical record |',
                  '| --- | --- | --- |']
        for row in selected:
            names = row['declarations']
            if category == 'sdk-binding':
                subject = f"{len(row['model_ids'])} source-facing models; {len(row['api_ids'])} API records"
            elif category == 'release-review':
                subject = f"`{row['package']} {row['version']}`; detected {row['census_checked_on']}"
            elif category == 'checker-omission':
                subject = str(sum(map(len, row['allowed_identities'].values()))) + ' allowed observation identities'
            else:
                subject = ', '.join('`' + name + '`' for name in names)
            link = '[' + ('review record' if category == 'cross-layer' else 'source record') + '](../' + row['origin'] + ')'
            lines.append('| `' + row['id'] + '` | ' + text_cell(subject) + ' | ' + link + ' |')
        lines.append('')
    lines += ['The SDK registry is the authority for per-model assumptions, selected observables and '
              'exact source/build applicability. Follow its [registry guide](../packages/solanalib-specs/source-map/README.md) '
              'and [binding obligations](../packages/solanalib-specs/BINDINGS.md). Runtime rows refer to '
              'the matching `correspondence` IDs in its [source registry](../packages/solanalib-runtime/source-map/sources.json) '
              'and [trust boundary](../packages/solanalib-runtime/TRUST.md).', '',
              'Allowed omission identities are policy, not a claim about a newly executed replay. '
              'Each replay must authenticate its complete corpora and record the actual selected, '
              'omitted and rejected-control identities. Use the [conformance guide](../tools/library-conformance/REFERENCE.md) '
              'for the mathematical-only exception and the precise open Token-2022 precondition.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--json', type=Path, help='Write the derived full records to an untracked artifact')
    args = parser.parse_args()
    review, rows = records()
    expected = render(review, rows)
    if args.check:
        if not (ROOT / OUTPUT).is_file() or (ROOT / OUTPUT).read_text() != expected:
            raise SystemExit('Stale gap index: run tools/model-audit/generate_gap_index.py')
    else:
        (ROOT / OUTPUT).write_text(expected)
    if args.json:
        args.json.write_text(json.dumps({'review': review, 'gaps': rows}, indent=2) + '\n')
    print(f'Gap index: {len(rows)} records from reviewed canonical inputs')


if __name__ == '__main__':
    main()
