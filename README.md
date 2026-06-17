<div align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-dark.png">
    <source media="(prefers-color-scheme: light)" srcset="https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-light.png">
    <img alt="Solanalib" width="100%" src="https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-light.png">
  </picture>
</div>

<p align="center">
  <a href="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/ci.yml"><img alt="CI" src="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/ci.yml/badge.svg"></a>
  <a href="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/docs.yml"><img alt="Docs" src="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/docs.yml/badge.svg"></a>
  <a href="LICENSE"><img alt="License: Apache-2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue"></a>
</p>

**A [Lean 4](https://lean-lang.org/) library of formal models and verified theorems for Solana programs.** 

Status: **purely experimental — exploring framework shape.**

The ambition is to be for Solana what [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) is for mathematics — a shared, well-documented foundation that downstream verification work can build on without redefining the same primitives every time. Programs written in [Anchor](https://www.anchor-lang.com/), [Pinocchio](https://github.com/anza-xyz/pinocchio), or hand-rolled, are intended to be modelled against `Solanalib`'s formal primitives and proven correct.

📚 **Generated docs:** <https://solana-foundation.github.io/leanprover-solanalib/>

---

## Why

Solana programs run with real assets at stake. Bugs in lending invariants, vesting curves, AMM math, PDA derivation, or token-supply accounting cost users — and code review is fundamentally limited as a defence: it scans for known patterns and misses what reviewers don't think to look for.

Formal verification flips the model. Instead of *reading* code looking for bugs, you *prove* the code matches a specification — a precise mathematical statement of intended behaviour. If the proof type-checks, the property holds *for every possible input*, not just the cases the reviewer happened to consider.

The bottleneck has historically been the cost of specs: writing them takes deep expertise, and every protocol has to reinvent the same primitives. `Solanalib` aims to lower that cost by providing the primitives — accounts, instructions, PDAs, common financial shapes — as reusable Lean definitions with theorems already proven about them.

The role this library plays in the stack:

```
┌──────────────────────────────────────────────────────────────┐
│  ON-CHAIN: Rust/Anchor/Pinocchio → compiled sBPF bytecode     │
└───────────────┬──────────────────────────────┬───────────────┘
                │ source-level                  │ artifact-level
┌───────────────▼──────────────────────────────▼───────────────┐
│  SPEC: Solanalib formal models in Lean 4                      │
│    · high-level layer  — accounts, instructions, finance …    │
│    · Solanalib.SBPF    — the sBPF ISA semantics: the machine  │
│                          the deployed bytecode actually runs  │
└──────────────────────────────────────────────────────────────┘
```

Solanalib lives entirely at the spec layer — it doesn't run on-chain. But it now models *both* ends of the refinement: the high-level shapes a protocol's logic is proven against, **and** the sBPF instruction-set semantics those programs compile down to. That lower anchor (`Solanalib.SBPF`) is a Lean port of the [OOPSLA 2025 Isabelle/HOL formalisation](https://dl.acm.org/doi/10.1145/3720414), validated against a reference VM (see [`spinoza`](https://github.com/lgalabru/spinoza), the companion harness). The eventual goal is an end-to-end chain from deployed bytecode up to protocol invariants.

---

## Architecture

Six peer top-level folders, each a distinct layer:

```
Solanalib/
├── Init.lean              ← Mathlib linter activation (imports-only)
├── Primitives/            ← atomic on-chain types
│   ├── Pubkey.lean             ByteArray wrapper, DecidableEq
│   ├── Lamports.lean           UInt64 (= Lamports) + Nat (= LamportsUnchecked)
│   └── Time.lean               UInt64 (= Timestamp) + Nat (= TimestampUnchecked)
├── Numeric/               ← fixed-point + arithmetic infrastructure
│   └── Fraction.lean           Q68.60 (Nat-backed spec; Fraction128 future)
├── Account/               ← Solana account model
│   ├── Basic.lean              5-field on-chain Account + credit/debit
│   └── Transfer.lean           Lamport transfer + conservation theorem
├── Instruction/           ← Solana instruction model
│   └── Basic.lean              Instruction + AccountMeta + signers/writables
├── Finance/               ← domain abstractions for DeFi shapes
│   ├── Decay.lean                  WindowedDecay bundled structure
│   ├── Growth.lean                 GrowthCurve (windowed dual of WindowedDecay)
│   ├── LinearDecay.lean            first concrete decay shape
│   ├── MonotoneSequence.lean       unbounded monotone-up shape
│   ├── CompoundInterest.lean       discrete compounding as a MonotoneSequence
│   └── WithdrawalCap.lean          stateful sliding-window rate limiter
└── SBPF/                  ← the sBPF instruction-set semantics (machine layer)
    ├── CommType.lean               BitVec machine words (U4 … U128) + byte (de)ser
    ├── Syntax.lean                 BpfInstruction (22 forms) + registers/ops/version
    ├── Value.lean                  CompCert-style memory value
    ├── Memory.lean                 byte-addressable memory + loadv / storev
    ├── Decoder.lean                bytecode → BpfInstruction (full opcode table)
    ├── State.lean                  registers, call stack, BpfState result
    ├── Interpreter.lean            step + fuel-bounded bpfInterp
    └── Verifier.lean               verifyInstr + step-safety theorem (Lemma 6.4)
```

The boundaries are deliberate:

- **`Primitives/`** are atomic types (no operations beyond the obvious). When we add `Slot`, `Epoch`, `Hash`, they live here.
- **`Numeric/`** is the numeric backbone — every fixed-point or refined-int type belongs here, separate from domain code so it stays reusable.
- **`Account/`**, **`Instruction/`** model the Solana runtime data shapes 1:1 with the real Rust crates (`solana-pubkey 4.2`, `solana-account 4.3`, `solana-instruction 3.4`).
- **`Finance/`** is the first domain layer — financial shapes that recur across DeFi: decay curves, growth curves, and (future) AMM math, lending invariants, oracle aggregation.
- **`SBPF/`** is the machine layer — a faithful Lean port of the [OOPSLA 2025](https://dl.acm.org/doi/10.1145/3720414) Isabelle/HOL sBPF semantics (all 22 instruction forms, the decoder, the small-step interpreter, and the verifier). Unlike the `Nat`-backed spec layers above, it models bit-precise machine words with `BitVec` (signed division, sign-extension, shifts), because the bytecode it describes is bit-precise. It is the concrete machine the high-level shapes ultimately refine down to.

The high-level layers depend only on the ones above them plus `Init.lean`; `SBPF/` is self-contained (it models the machine, not the protocol). The result: replacing or refining a lower layer doesn't ripple — e.g. promoting `Fraction` to a bounded `Fraction128` won't force `Finance/Decay.lean` to change.

---

## Design patterns

These are the patterns the codebase has converged on. They're documented in detail in [`skills/lean-best-practices/SKILL.md`](skills/lean-best-practices/SKILL.md).

### 1. **Bundled structures, not type-classes**, for domain shapes

When a concept has several properties that must hold together (e.g. "a function that decays from peak to zero, monotonically, in a window"), we use a **bundled structure** with the function and proofs embedded:

```lean
structure WindowedDecay where
  tBegin tEnd peak : Nat
  apply : Nat → Nat
  bounded : ∀ t, apply t ≤ peak
  at_begin : tBegin < tEnd → apply tBegin = peak
  at_end : apply tEnd = 0
  antitone_in_window : …
```

Concrete shapes provide a `toX` constructor that constructs the bundle by proving each obligation:

```lean
def LinearDecay.toWindowedDecay (tBegin tEnd peak : Nat) : WindowedDecay := { … }
```

Generic theorems are methods on the structure (`d.complementary`, `d.complementary_le_peak`). No type-class elaboration surprises; matches Mathlib's `OrderHom`, `MulHom`, `LinearMap`.

### 2. **Bounded types live alongside unbounded spec aliases**

Solana fields are `u64` on-chain; mathematical reasoning wants unbounded `Nat`. We expose both:

```lean
notation "Lamports"          => UInt64   -- strict on-chain shape
notation "LamportsUnchecked" => Nat      -- spec layer; omega-friendly
```

Operations on `Lamports` carry overflow / underflow preconditions in their type signatures:

```lean
def Account.credit (a : Account) (amount : Lamports)
    (h : a.lamports.toNat + amount.toNat < UInt64.size) : Account := …
```

Theorems are typically stated at the `.toNat` level (so `omega` does the arithmetic) with bridge lemmas like `Account.credit_lamports_toNat` connecting the two.

### 3. **`@[ext]` on every structure, `@[simp]` on every projection**

Lets `ext; simp` close most structural-equality proofs uniformly. Skim any test file for examples.

### 4. **Layered model: spec layer in `Nat`, bounded refinement separate**

`Fraction = Q68.60` is currently `Nat`-backed at the spec layer for arithmetic clarity. The bounded `Fraction128` refinement (matching the on-chain `u128` shape) lives in a separate type with `.toNat` bridge lemmas — same architectural pattern as `Lamports` / `LamportsUnchecked`. This follows the [seL4](https://sel4.systems/) / [CompCert](https://compcert.org/) discipline: prove on the abstract model, refine to the bounded representation as a separate step.

---

## Quick-start

You'll need:

- [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager (rustup-equivalent). Install once:
  ```sh
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
  ```
- [`just`](https://github.com/casey/just) as the command runner: `brew install just`.

Then, in this directory:

```sh
just setup        # ~5 min: fetches Mathlib + downloads cached oleans
just build        # ~10 s warm: type-checks the library + all theorems
just test         # runs regression tests in SolanalibTest/
just docs-open    # builds the docs site + opens .lake/build/doc/index.html
```

CI runs the same `just build` + `just test` + `scripts/lint-style.sh` flow on every push. Warning gate fails any build that emits a `warning: Solanalib*/` line.

---

## What's in it today

Inventory of the verified surface as of this commit:

| Module | Definitions | Theorems |
|---|---|---|
| `Primitives.Lamports` | `Lamports`, `LamportsUnchecked`, `Lamports.perSol` | — |
| `Primitives.Pubkey` | `Pubkey` | — |
| `Numeric.Fraction` | `Fraction`, `scale`, `zero`, `one`, `fromNat`, `toFloor`, `add`, `sub`, `mul`, `div`, `ofLamports`, `toLamports?`, order instances | 14 (monoid, ordering, round-trip, sub/add cancel, div_one) |
| `Account.Basic` | `Account`, `credit`, `debit` | 12 (10 `@[simp]` projection + 2 `.toNat` bridge) |
| `Account.Transfer` | `TransferResult`, `transfer` | 1 (`transfer_preserves_total` — lamport conservation) |
| `Instruction.Basic` | `Instruction`, `AccountMeta`, `Instruction.signers`, `.writables` | — |
| `Finance.Decay` | `WindowedDecay`, `WindowedDecay.complementary` | 4 (inherited via composition) |
| `Primitives.Time` | `Timestamp`, `TimestampUnchecked` | — |
| `Finance.LinearDecay` | `LinearDecay.value`, `LinearDecay.toWindowedDecay` | 4 (P1–P3b: bounded, antitone, value-at-begin, value-at-end) |
| `Finance.MonotoneSequence` | `MonotoneSequence` | 2 (`apply_zero_le`, `apply_le_of_le`) |
| `Finance.CompoundInterest` | `balance`, `toMonotoneSequence` | 5 (boundary, unit-multiplier identity, one-step monotonicity, multi-step monotonicity, balance ≥ principal) |
| `Finance.WithdrawalCap` | `WithdrawalCap`, `Invariant`, `IsElapsed`, `remaining`, `TryAdd`, `tryAdd` | 5 (`remaining_le_capacity`, `tryAdd_preserves_invariant`, `tryAdd_rejects_over_cap_midwindow` + `_at_reset`, `interval_reset_idempotent`) |
| `Finance.Growth` | `GrowthCurve`, `WindowedDecay.toComplementaryGrowthCurve` | 4 (embedded; inherited at constructor time) |
| `SBPF.{CommType,Syntax,Value,Memory}` | `BitVec` words, `BpfInstruction` (22 forms), `Val`, `loadv`/`storev` | data layer |
| `SBPF.Decoder` | `decode`, `findInstr` (full opcode table) | round-trip tests |
| `SBPF.Interpreter` | `step`, `bpfInterp` + per-class evaluators | differential testing (below) |
| `SBPF.Verifier` | `verifyInstr`, `step_ne_err` (Lemma 6.4) | 9 |

Run `scripts/coverage.sh` for the live def/theorem tally.

The two layers are validated differently, on purpose. The **high-level / finance** shapes carry per-definition theorems — a high theorem-to-def ratio there is the signal that we're proving properties faster than we add surface. The **`SBPF/` machine layer** is mostly executable definitions (the interpreter is a faithful model, not a thing to prove theorems *about* per se); its correctness is established two ways instead: (1) the `step_ne_err` **safety theorem** — a verifier-accepted instruction never faults to the `err` state ([Lemma 6.4 of the paper](https://dl.acm.org/doi/10.1145/3720414)) — and (2) **differential testing** against a reference sBPF VM via [`spinoza`](https://github.com/lgalabru/spinoza), which has run tens of thousands of randomized programs through both this Lean interpreter and the VM with zero divergences.

---

## Roadmap

Listed roughly in order of how foundational they are; not all need to be done before the library is useful, but all are flagged as known gaps.

### Numeric foundation

- [ ] **`Fraction.mul_assoc` error bound.** Truncating `bits / scale` after each multiplication introduces ≤ 1 ULP of error; left-associative and right-associative multiplications can differ by `(a + c) / scale` in the worst case. The theorem statement is straightforward; the proof needs careful `Nat` lemmas about double-truncation.
- [ ] **`Fraction128` bounded refinement.** Mirror of the `Lamports` / `LamportsUnchecked` story: a `UInt128`-backed `Fraction128` plus `.toNat` bridge. Lean 4 doesn't have native `UInt128`; modelled as `Fin (2^128)` or a `(lo, hi)` `UInt64` pair.
- [ ] **`Fraction.divCeil`** — round-up variant for slippage / collateralisation calculations.
- [ ] **Pow / `Real.exp` correspondence** — for compound interest, we'll want a theorem bounding `pow_fraction r n` against the mathematical `e^(r·n)`. Requires importing more of Mathlib.

### Domain primitives

- [x] **`Finance.CompoundInterest`** — landed: discrete-compounding `balance` consuming a `Fraction` multiplier, bundled into a `MonotoneSequence`. Open follow-up: truncated-Taylor approximation matching Kamino's `approximate_compounded_interest`, plus an error-bound theorem connecting the approximation to the exact compounding modelled here.
- [x] **`Finance.WithdrawalCap`** — landed: stateful sliding-window rate limiter; four theorems pin the bug classes auditors check for (saturation, invariant escape, off-by-one on the boundary, missed accumulator reset on interval rollover).
- [ ] **`Finance.AMM`** — constant-product (`x · y = k`), then weighted pools, then concentrated liquidity. `IsAMM` becomes a `class` (this is one of the places where typeclass dispatch genuinely earns its keep — multiple instance types share an interface).
- [ ] **`Finance.Lending`** — collateralisation-ratio invariants, liquidation conditions, interest accrual.
- [ ] **`Primitives.Slot`, `Primitives.Epoch`** — `UInt64`-backed clock primitives.
- [ ] **`Primitives.Hash`** — 32-byte cryptographic hash with collision-resistance as an axiom (for unsigned theorems) and refinement to specific hash functions (SHA-256, Keccak) later.

### Solana semantics

- [ ] **`Pda`** — `find_program_address` + the determinism theorem. Hit by every Solana program.
- [ ] **`Sysvar.Clock`, `Sysvar.Rent`** — read-only on-chain state most programs depend on.
- [ ] **`ProgramResult`** — `Ok` / `Err` with the standard Solana error codes.
- [ ] **`Transaction`** — list of instructions + signers + recent blockhash.
- [ ] **`CPI`** — cross-program-invocation semantics; invariants spanning a CPI call.

### Bridges and verification

- [x] **sBPF semantics in Lean (`Solanalib.SBPF`).** Landed: a Lean port of the [OOPSLA 2025 Isabelle/HOL formalisation](https://dl.acm.org/doi/10.1145/3720414) — all 22 instruction forms, the decoder, the small-step interpreter, and the verifier with the `step_ne_err` safety theorem (Lemma 6.4). Validated against a reference VM through the [`spinoza`](https://github.com/lgalabru/spinoza) harness (`spinoza validate`), which differentially tests the Lean interpreter against an executable sBPF VM; `spinoza lift` emits a deployed program's `.text` as an importable `BpfBin` term.
- [ ] **Refinement from `SBPF/` up to the spec layers.** The pieces exist at both ends; the open work is the connecting theorem — e.g. a lifted program's `bpfInterp` result preserves a `Finance.WithdrawalCap` invariant. Also outstanding from the port: the x86-64 JIT correspondence, and reconciling the PQR high-multiply edge case against a second oracle (agave `solana-sbpf`).
- [ ] **Aeneas integration (source-level path).** The complement to the artifact-level sBPF route above: pick one pure-math Rust function (e.g. `kfarms::get_withdrawal_penalty_bps`), run `cargo charon --preset=aeneas`, run `aeneas -backend lean`, import the generated Lean, prove `theorem rust_impl_refines_spec`. If this works end-to-end on one realistic module, we have a defensible refinement story for the algorithmic core of Solana programs.

### Library hygiene

- [ ] **`@[simps]` integration.** Currently we hand-write projection lemmas — Mathlib's `@[simps]` macro auto-generates them. Saves boilerplate as the codebase grows.
- [ ] **`shake` integration.** Mathlib's unused-imports detector. Deferred because the current `notation`-heavy style doesn't play well with shake's import-usage analysis; revisit when we have ≥ 10 leaf modules.
- [ ] **Mathlib version-bump automation.** `update.yml` workflow currently runs `lake update` monthly; add a follow-on step that bumps `lean-toolchain` to whatever Mathlib pins.

---

## Contributing

The skill at [`skills/lean-best-practices/SKILL.md`](skills/lean-best-practices/SKILL.md) is the canonical guide — file template, naming conventions, the `abbrev` / `notation` / `UInt64` trade-offs, common errors, the bundled-structure pattern, and the numeric-bridge discipline. Read it before adding a new primitive.

In short, the workflow for adding a new domain primitive looks like:

1. Decide the file path under `Solanalib/<Concept>/`. New top-level concept ↔ new top-level folder.
2. Write the file using the template in the skill (copyright header, then imports, then `/-! … -/` module docstring, then namespace).
3. Add the file to `Solanalib.lean`.
4. Run `just build` locally. **Always verify locally before pushing** — CI cycles are ~2 minutes vs ~10 seconds locally.
5. For load-bearing API, add a regression test under `SolanalibTest/<Concept>/<Aspect>Test.lean` and import it from `SolanalibTest.lean`.
6. Run `just test` and `scripts/lint-style.sh`.

Conventions worth knowing before writing the first proof:

- Use `notation` over `abbrev` for type synonyms over `Nat` / `Int` (`omega` doesn't unfold `abbrev`).
- Tag every `structure` with `@[ext]`, every projection lemma with `@[simp]`.
- For bounded `UInt64` / `UInt128` reasoning, bridge to `Nat` via `.toNat` — `omega` doesn't reason about `UInt64` directly.
- Bundled structures > type-classes for domain shapes with concrete parameters.
- The first commit should follow the existing pattern (no AI-attribution trailer, copyright `(c) <YEAR> Solana Foundation`, `Authors: Solanalib Contributors`).

---

## License

Apache-2.0. See [`LICENSE`](LICENSE).
