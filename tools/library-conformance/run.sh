#!/usr/bin/env bash
# Record the pinned Rust libraries and check the Lean models against the recording.
#
#   tools/library-conformance/run.sh            record (needs Rust), then check
#   tools/library-conformance/run.sh --check    check the committed corpus only (Lean)
#
# Evidence goes to $EVIDENCE_DIR (default: a new temporary directory); Cargo builds into
# $CARGO_TARGET_CACHE (default: ~/.cache/solana-library-conformance/target). Extra arguments
# after --record-args are passed to `run.py --record` (for example --offline).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
python="${PYTHON:-python3}"
evidence="${EVIDENCE_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/solana-library-conformance.XXXXXX")}"
target="${CARGO_TARGET_CACHE:-$HOME/.cache/solana-library-conformance/target}"

check_only=0
record_args=()
while [ $# -gt 0 ]; do
    case "$1" in
        --check) check_only=1 ;;
        --record-args) shift; record_args=("$@"); break ;;
        *) echo "usage: run.sh [--check] [--record-args ARG...]" >&2; exit 2 ;;
    esac
    shift
done

if [ "$check_only" -eq 0 ]; then
    "$python" -B "$here/run.py" --record --twice --evidence-dir "$evidence/record" --target-dir "$target" \
        ${record_args[@]+"${record_args[@]}"}
fi
"$python" -B -m unittest discover -s "$here" -p 'test_*.py'
"$python" -B "$here/run.py" --model-only --evidence-dir "$evidence/model"
