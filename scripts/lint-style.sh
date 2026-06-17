#!/usr/bin/env bash
# Textual style checks for Lean source files.
#
# Catches conventions Lean's own linters can't see across files:
#   - copyright header presence with the expected Authors line
#   - lines exceeding 100 characters
#   - forbidden tokens (`λ`, `$`-as-application)
#   - module docstring `/-! ... -/` placed AFTER any `import` lines
#
# Compatible with macOS bash 3.2 (no mapfile / readarray). Exits 0 if clean,
# 1 if any rule trips.

set -u
set -o pipefail

cd "$(dirname "$0")/.."

EXIT=0
RED=$'\033[31m'
RESET=$'\033[0m'

fail() {
  printf '%s%s%s\n' "$RED" "$1" "$RESET" >&2
  EXIT=1
}

check_file() {
  local f=$1
  local header
  header=$(head -n 6 "$f")

  # ---- Copyright header ----
  if ! grep -q '^Copyright (c) [0-9]\{4\} .* All rights reserved\.$' <<<"$header"; then
    fail "$f: missing 'Copyright (c) YYYY <Owner>. All rights reserved.' line"
  fi
  if ! grep -q '^Authors: .* Contributors$' <<<"$header"; then
    fail "$f: header must end with 'Authors: <Project> Contributors' (no personal names)"
  fi
  if ! grep -q '^Released under Apache 2.0 license' <<<"$header"; then
    fail "$f: header missing Apache 2.0 license line"
  fi

  # ---- Line length: 100 char limit ----
  # Lines containing a URL are exempt — long link refs are an editorial
  # decision, not a style violation.
  awk -v file="$f" '
    length > 100 && !/https?:\/\// {
      print file":"NR": line exceeds 100 chars ("length")"
    }
  ' "$f" | while IFS= read -r line; do fail "$line"; done

  # ---- Forbidden tokens ----
  if grep -nE 'λ' "$f" >/dev/null; then
    grep -nE 'λ' "$f" | while IFS= read -r line; do
      fail "$f:$line: bare 'λ' — use 'fun ... ↦ ...'"
    done
  fi
  # `$` used as application combinator. Exclude doc/comment contexts and the
  # legitimate `--`-prefixed comment markers.
  if grep -nE '[[:space:]]\$[[:space:]]' "$f" | grep -vE '^[0-9]+:[[:space:]]*(--|/-)' >/dev/null; then
    grep -nE '[[:space:]]\$[[:space:]]' "$f" | grep -vE '^[0-9]+:[[:space:]]*(--|/-)' | while IFS= read -r line; do
      fail "$f:$line: '\$' forbidden — use '<|' or '|>'"
    done
  fi

  # ---- Module docstring must appear after imports ----
  # The capital-letter anchor distinguishes real `import Foo.Bar` lines from
  # docstring prose that happens to start with the word "import".
  local first_doc last_import
  first_doc=$(grep -n '^/-!' "$f" | head -n1 | cut -d: -f1)
  last_import=$(grep -nE '^import [A-Z]' "$f" | tail -n1 | cut -d: -f1)
  if [ -n "$first_doc" ] && [ -n "$last_import" ] && [ "$first_doc" -lt "$last_import" ]; then
    fail "$f: module docstring at line $first_doc must appear AFTER last import (line $last_import)"
  fi
}

COUNT=0
while IFS= read -r f; do
  check_file "$f"
  COUNT=$((COUNT + 1))
done < <(
  find Solanalib SolanalibTest -name '*.lean' 2>/dev/null
  [ -f Solanalib.lean ] && echo Solanalib.lean
  [ -f SolanalibTest.lean ] && echo SolanalibTest.lean
)

if [ $EXIT -eq 0 ]; then
  echo "lint-style: $COUNT files OK"
fi
exit $EXIT
