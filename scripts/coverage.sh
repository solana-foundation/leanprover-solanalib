#!/usr/bin/env bash
# Cheap "spec coverage" report: for every Lean source file in the library,
# count definitions vs. theorems and show the ratio. Higher = more of the
# defs have a proven property attached. Crude but useful as a CI signal.

set -u
set -o pipefail

cd "$(dirname "$0")/.."

count_kind() {
  local file=$1
  local keyword=$2
  # Match lines where the keyword starts the declaration, optionally
  # preceded by an attribute like @[simp] or @[ext].
  grep -cE "^[[:space:]]*(@\[[^]]+\][[:space:]]+)?(${keyword})[[:space:]]" "$file" || true
}

printf "%-50s %5s %5s %8s\n" "FILE" "DEFS" "THMS" "RATIO"
printf "%s\n" "$(printf -- '-%.0s' {1..72})"

total_defs=0
total_thms=0

# All .lean files in the library and tests.
files=$(find Solanalib SolanalibTest -name '*.lean' 2>/dev/null; \
        [ -f Solanalib.lean ]     && echo Solanalib.lean; \
        [ -f SolanalibTest.lean ] && echo SolanalibTest.lean)

for f in $files; do
  defs=$(count_kind "$f" "def|structure|inductive|class|abbrev|notation")
  thms=$(count_kind "$f" "theorem|lemma|example")
  total_defs=$((total_defs + defs))
  total_thms=$((total_thms + thms))
  if [ "$defs" -gt 0 ]; then
    ratio=$(awk "BEGIN { printf \"%.2f\", $thms / $defs }")
  else
    ratio="—"
  fi
  printf "%-50s %5d %5d %8s\n" "$f" "$defs" "$thms" "$ratio"
done

printf "%s\n" "$(printf -- '-%.0s' {1..72})"
if [ "$total_defs" -gt 0 ]; then
  overall=$(awk "BEGIN { printf \"%.2f\", $total_thms / $total_defs }")
else
  overall="—"
fi
printf "%-50s %5d %5d %8s\n" "TOTAL" "$total_defs" "$total_thms" "$overall"
