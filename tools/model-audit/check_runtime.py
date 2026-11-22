#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Check runtime source correspondence, module coverage and complete proof dependencies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from proof_diagnostics import has_proof_placeholder
from runtime_inventory import check_audit_modules, model_files, model_modules, render_export
from runtime_source_map import verify_correspondence, verify_source_map

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / 'packages/solanalib-runtime'
DATA = MODEL / 'source-map'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def validate_declarations(rows, summary):
    """Reject incomplete or contradictory output from the Lean dependency audit."""
    if summary.get('kind') != 'audit_summary' or not rows:
        raise ValueError('Missing complete runtime axiom audit')
    names = [row['name'] for row in rows]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate runtime declaration')
    for row in rows:
        if not set(row['axioms']) <= ALLOWED_AXIOMS:
            raise ValueError('Unexpected axiom: ' + row['name'])
        if {'⋯', '…'}.intersection(row['type']):
            raise ValueError('Truncated declaration type: ' + row['name'])
    if (summary['audited_constants'] < len(rows)
            or summary['audited_theorems'] < sum(row['kind'] == 'theorem' for row in rows)):
        raise ValueError('Incomplete runtime declaration counts')


def validate_modules(records, modules):
    """Require one description for every production module beneath the aggregate."""
    listed = [row['module'] for row in records]
    expected = set(modules) - {'Solanalib.Runtime'}
    if len(listed) != len(set(listed)) or set(listed) != expected:
        raise ValueError('Runtime module descriptions do not match the Lake inventory')
    if any(not row['description'].strip() for row in records):
        raise ValueError('Empty runtime module description')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry', type=Path, help='Cargo registry source directory.')
    parser.add_argument('--agave-source', type=Path, help='The pinned Agave source checkout.')
    parser.add_argument('--require-source-checks', action='store_true',
                        help='Require byte and line-anchor checks for every upstream source.')
    parser.add_argument('--output', type=Path, help='Write the JSON audit result here.')
    args = parser.parse_args()
    sources = {str(p.relative_to(MODEL)): p.read_text() for p in model_files(MODEL)}
    validate_modules(json.loads((DATA / 'modules.json').read_text()), model_modules(MODEL))
    document = json.loads((DATA / 'sources.json').read_text())
    analyses = document['analyses']
    if (not analyses or len(analyses) != len(set(analyses))
            or any(Path(name).name != name or not name.endswith('.md')
                   or not (MODEL / 'source-notes' / name).is_file() for name in analyses)):
        raise ValueError('Missing or invalid runtime source analysis')
    environment = os.environ.copy()
    for name in ('LEAN_PATH', 'LEAN_SRC_PATH'):
        environment.pop(name, None)
    subprocess.run(['lake', '--wfail', 'build', 'Solanalib.Runtime'],
                   cwd=ROOT, env=environment, check=True)
    with tempfile.TemporaryDirectory(prefix='solanalib-runtime-audit-') as temporary:
        script = Path(temporary) / 'Audit.lean'
        script.write_text(render_export(MODEL, Path(__file__).with_name('AuditRuntime.lean.in').read_text()))
        result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(script)],
                                cwd=ROOT, env=environment, text=True, capture_output=True)
        if result.returncode or has_proof_placeholder(result.stdout + result.stderr):
            raise RuntimeError('Runtime dependency audit failed:\n' + result.stdout + result.stderr)
        output = [json.loads(line) for line in result.stdout.splitlines()]
        if not output:
            raise ValueError('Empty runtime dependency audit')
        rows, summary = output[:-1], output[-1]
        validate_declarations(rows, summary)
        check_audit_modules(MODEL, summary)
    correspondence = verify_correspondence(DATA / 'sources.json', sources, rows)
    anchors = verify_source_map(DATA / 'sources.json', registry=args.registry,
                                agave_source=args.agave_source, require_sources=args.require_source_checks)
    receipt = {
        'status': 'passed', 'axioms': summary, 'allowed_axioms': sorted(ALLOWED_AXIOMS),
        'correspondence': correspondence, 'sources': anchors,
        'model_sha256': {name: hashlib.sha256(body.encode()).hexdigest() for name, body in sources.items()},
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(f"Runtime audit: {summary['audited_constants']} declarations, "
          f"{correspondence['modules']} source-correspondence modules, "
          f"{anchors['checked_source_anchors']}/{anchors['anchors']} source anchors checked")


if __name__ == '__main__':
    main()
