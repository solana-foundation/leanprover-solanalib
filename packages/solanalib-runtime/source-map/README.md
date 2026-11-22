# Runtime source correspondence

[sources.json](sources.json) records immutable upstream paths, Git revisions or published archive checksums, line anchors and file hashes. Its `correspondence` rows associate every runtime module with a source argument, assumptions, limitations and exact Lean bytes. [modules.json](modules.json) describes the modules in the runtime library. The [source notes](../source-notes/README.md) explain the model and its boundaries.

Run the correspondence and proof-dependency audit from the repository root with Python 3.12:

```sh
uv run --no-project --python 3.12 python tools/model-audit/check_runtime.py
```

The audit obtains the complete runtime module inventory from Lake, checks the descriptions and source arguments, elaborates every runtime module, and checks all declarations, including private proofs, for dependencies outside `propext`, `Classical.choice` and `Quot.sound`. Source references and model hashes must agree with the registry. The checks do not prove semantic equivalence with the Rust implementations.

To check all upstream file bytes and line anchors as well, supply the pinned Agave checkout and the directory of unpacked Cargo sources:

```sh
uv run --no-project --python 3.12 python tools/model-audit/check_runtime.py \
  --registry /path/to/cargo/registry/src/index.crates.io-... \
  --agave-source /path/to/agave \
  --require-source-checks --output /tmp/runtime-audit.json
```

The audit checks the content hash of each selected file and its exact line anchor. Git-pinned Cargo entries also check the revision and repository-relative path in `.cargo_vcs_info.json`. Archive-pinned entries record the exact crates.io URL and checksum; authenticate that archive before supplying its unpacked sources. Without the local upstream copies, the result records zero checked source anchors. `--require-source-checks` rejects missing or partial source copies.
