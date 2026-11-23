# Shared contract vocabulary

`Solanalib.Contracts.Model` is the library-neutral vocabulary for mathematical API models. `Solanalib.Contracts` is a selectable library in the root `solanalib` Lake package, which includes Mathlib. Its Lean sources use only Lean core and Std; the [SDK models](../solanalib-specs/README.md) instantiate this vocabulary.

Import `Solanalib.Contracts` for the model record. The separate `Solanalib.Contracts.Outcome`, `.Family`, `.Callback`, `.Capabilities` and `.Versioning` modules provide the remaining vocabulary. The model declarations use the `Solanalib.Contracts.Model` namespace.

A model specifies a precondition on state and arguments and a relation on returned values, unwinds and terminal outcomes. `Family` retains type arguments, callbacks and other interpretation parameters. `Callback` describes stateful dependency operations; `Capabilities` and `Versioning` describe selected families and registered source/build applicability.

`Holds` states that an interpretation satisfies the model. `Satisfiable` witnesses an admissible input, and `HasExecution` a finite reference execution. These are mathematical results, separate from Rust implementation and memory-representation proofs. Concrete bindings belong outside this package; their obligations are described in [BINDINGS.md](../solanalib-specs/BINDINGS.md).

From the repository root, using the recorded Lean toolchain:

```sh
lake --wfail build Solanalib.Contracts
lake --wfail build SolanalibTest.Specs.Core
```

The shared [scenario tests](../solanalib-specs/SolanalibTest/Specs/Core.lean) exercise callbacks, resource effects and capability composition. Git clients require the root `solanalib` package at an immutable commit and import `Solanalib.Contracts`. Every library under `Solanalib` and `SolanalibTest` shares its artifact directory, including when loaded with plain `lake env lean`.
