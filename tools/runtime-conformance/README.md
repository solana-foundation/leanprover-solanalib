# Solana runtime model tests

This suite compares the [Solana runtime model](../../packages/solanalib-runtime/README.md)
with unmodified Agave 4.3.2 at revision
`a203300045b405f86c9c84308b2eae76af69ac3b`.
It checks account operations, serialization/read-back and nonempty CPI calls.
The [reference guide](REFERENCE.md) describes the fixtures, compared fields and
selected runtime configuration.

## Run the tests

From the repository root, using Python 3.12 and the recorded Lean toolchain:

```sh
python3.12 -B -m unittest discover -s tools/runtime-conformance -p 'test_*.py'
python3.12 -B tools/runtime-conformance/run.py --model-only \
  --evidence-dir /tmp/solana-runtime-check
```

The runner authenticates the committed native recording, evaluates the current
model and compares all cases. `run-status.json` records the result;
`comparison.json` identifies the fields compared, and `native.tsv` and `model.tsv`
retain the complete observations. Commands, source identities and the axiom check of the local theorem remain in the same evidence directory.

Build the separate mathematical scenario tests of the model with:

```sh
lake build Solanalib.Runtime SolanalibTest.Runtime
```

## Reproduce native results

Use Rust 1.97.1, target `x86_64-unknown-linux-gnu`, and the system dependencies
required by the `solana-program-runtime` of Agave. Download the pinned source archive:

```sh
curl --fail --location \
  https://codeload.github.com/anza-xyz/agave/tar.gz/a203300045b405f86c9c84308b2eae76af69ac3b \
  --output /tmp/agave-a203300.tar.gz
python3.12 -B tools/runtime-conformance/run.py \
  --source-archive /tmp/agave-a203300.tar.gz \
  --evidence-dir /tmp/solana-runtime-native
```

The runner verifies the archive hash, builds and executes the native driver,
then checks the fresh results against the model. Build outputs and observations
stay in the evidence directory. It uses four Cargo jobs by default and preserves
the lockfile and configuration of the source.

## Maintain the tests

Use the existing fixtures, native driver and `SolanalibTest/Conformance/Runtime.lean`. Include meaningful
success, error and boundary cases; compare every represented state effect.
Negative controls should reject changed values, state, errors or missing cases.
After changing fixtures or native inputs, reproduce the native results and update
their recorded provenance. Model-only changes use a fresh model replay.

[REFERENCE.md](REFERENCE.md) gives the exact source seal, native build settings,
field coverage and observations outside the model. The separate
library suite tests SDK and framework
function models.
