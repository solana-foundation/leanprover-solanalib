---
name: lean-best-practices
description: Mathlib4-derived best practices for writing and structuring Lean 4 libraries. Use when user asks to "add a Lean theorem", "create a Lean module", "review Lean code", "structure a Lean library like Mathlib", "fix a Lean build error", or works on `.lean` / `lakefile.lean` / `lean-toolchain` files. Codifies file template, naming, proof style, attribute usage, the `abbrev`/`omega` trap, and the common errors that bite first-time contributors.
metadata:
  source-project: solana-foundation/leanprover-solanalib
  version: 0.1.0
---

# Lean 4 best practices

Conventions for writing Lean 4 libraries in the Mathlib4 style. Distilled from the official Mathlib contributor docs plus painful lessons learned bootstrapping the [Solanalib](https://github.com/solana-foundation/leanprover-solanalib) library — examples below use Solanalib's code, but the rules are general.

## When this skill applies

- Adding or modifying any `.lean` file in a library that aims to follow Mathlib conventions.
- Editing `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, or `.github/workflows/` for a Lean project.
- Reviewing a Lean PR for style or structure.
- Bootstrapping a new Lean 4 library that should match the Mathlib ecosystem's conventions.

## Default decisions

Make these without asking:

- **Verify locally before pushing.** `elan` installs the right toolchain from the `lean-toolchain` file; `lake build` (and `lake test`) before any push. CI cycles cost minutes; local builds cost seconds. Never push a Lean change without a local build pass.
- **Track Mathlib's `lean-toolchain` pin.** When bumping Lean, fetch `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain`, set `lean-toolchain` to match, and update the Mathlib `require` rev in `lakefile.lean` to the same tag. `doc-gen4`'s `main` branch tracks this — drift breaks docs.
- **Copyright authorship line is `<Project> Contributors`.** Never personal names, never the parent org. The `Copyright (c) YEAR <Owner>` line is the legal-owner statement and is separate.
- **No AI-attribution trailers** (`Co-Authored-By: Claude …`) in commits.
- **Commit `lake-manifest.json`** but not `.lake/`. Reproducible builds depend on the manifest; `.lake/` is per-machine cache.

## Operating procedure

### Adding a new module

1. Decide the file path. Organise by **domain concept**, not by **consumer or framework** (Mathlib organises by mathematical concept, not by who uses it; sibling libraries should organise the same way within their domain).
2. Write the file using the template in `## File template` below.
3. Add `import <Library>.<Concept>.<Aspect>` to the library root file (alphabetical within its block).
4. Run `lake build` locally. Fix any errors. Run `lake test`.
5. If the module introduces a load-bearing API surface, add a regression test under the test library mirror (`<Library>Test/<Concept>/<Aspect>Test.lean`) and import it from the test root.

### Adding a new theorem

1. Place it in the file whose subject it concerns, not in a global `Theorems.lean`.
2. Name it `<conclusion>_of_<hypothesis>` (Mathlib pattern: `add_pos_of_pos_of_nonneg`) or `<descriptive_name>` if self-explanatory (`Nat.sub_add_cancel`).
3. Write the statement with all binders explicit (`autoImplicit := false` is on globally in the lakefile — keep it that way).
4. Prefer term-mode proofs (`:= rfl`, `:= by simp`) over multi-line `by` blocks when feasible. Otherwise use the tactic style in `## Proof style` below.
5. Tag with `@[simp]` only if the lemma rewrites *toward* a normal form. Don't tag the headline result.

### Adding a new type

**Default to `notation` over `abbrev` when the type is a synonym for `Nat`/`Int`.** See `## Type aliases: notation, not abbrev` below — this is the most-likely-to-bite gotcha.

For real structures, use `structure`/`inductive` with `@[ext]`:

```lean
@[ext]
structure Slot where
  /-- The slot number on the cluster. -/
  value : Nat
  deriving Repr, DecidableEq
```

## File template

Every `.lean` file starts with this exact shape:

```lean
/-
Copyright (c) <YEAR> <Legal Owner>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <Project> Contributors
-/
import <Library>.<dep1>
import <Library>.<dep2>          -- alphabetical within their block

/-!
# <Module title — short, capitalised>

<One-paragraph summary explaining what this module is for and why it exists.
End at the level of "what does this file give to the rest of the library".>

## Main definitions

* `<Library>.Foo` — <one-line gloss>
* `<Library>.Foo.bar` — <one-line gloss>

## Main statements

* `foo_property_baz` — <what it proves and why it matters>
-/

namespace <Library>

-- declarations

end <Library>
```

**Critical ordering:** copyright `/- ... -/` comment first, then imports, then `/-! ... -/` module docstring. The module docstring is a *declaration*, not a comment, so it cannot precede `import`. Mistaking this produces `invalid 'import' command, it must be used in the beginning of the file`.

**Subsection headers** (`## Main definitions`, `## Main statements`, `## Implementation notes`, `## References`) follow Mathlib's convention and are rendered as anchored sections in the doc-gen4 output.

## Naming conventions

Inherited from Mathlib:

| Kind | Convention | Example |
|---|---|---|
| Types, structures, classes, inductives | `UpperCamelCase` | `Account`, `TransferResult` |
| Defs, functions, fields | `lowerCamelCase` | `credit`, `lamportsPerSol`, `source` |
| Theorems, lemmas, propositions | `snake_case` | `transfer_preserves_total`, `credit_lamports` |
| Files | `UpperCamelCase.lean` | `Transfer.lean` |
| Folders | `UpperCamelCase` | `Account/`, `Primitives/` |

Theorem-name pattern: `<conclusion>_of_<hypothesis>`. For projection-shape `@[simp]` lemmas, the form `<def>_<field>` is conventional (`credit_lamports`, `Account.mk_lamports`).

## Bounded types: bridging UInt64 to Nat for omega

**`omega` in Lean 4.31.0-rc1 has very limited `UInt64` support.** Tests like `(a b : UInt64) (h : a ≤ b) : b - a + a = b := by omega` fail with `No usable constraints found`. The fix is to keep two parallel type-aliases and bridge between them with `.toNat`:

```lean
notation "Lamports"          => UInt64   -- strict on-chain shape
notation "LamportsUnchecked" => Nat      -- for omega-style reasoning
```

The pattern in practice:

```lean
-- Define operations on UInt64 with explicit bounds proofs in the signature:
def credit (a : Account) (amount : Lamports)
    (h : a.lamports.toNat + amount.toNat < UInt64.size) : Account :=
  { a with lamports := a.lamports + amount }

-- Provide a `_toNat` bridge lemma that drops the result into Nat:
theorem credit_lamports_toNat (a : Account) (n : Lamports)
    (h : a.lamports.toNat + n.toNat < UInt64.size) :
    (credit a n h).lamports.toNat = a.lamports.toNat + n.toNat := by
  rw [credit_lamports, UInt64.toNat_add, Nat.mod_eq_of_lt h]
```

Then conservation-style proofs become:

```lean
theorem transfer_preserves_total ... :
    (transfer ...).source.lamports.toNat + (transfer ...).destination.lamports.toNat
      = src.lamports.toNat + dst.lamports.toNat := by
  have h_under_nat := UInt64.le_iff_toNat_le.mp h_under   -- bridge UInt64 ≤ → Nat ≤
  simp only [transfer]
  rw [debit_lamports_toNat, credit_lamports_toNat]
  omega                                                   -- now in Nat-land
```

Key core lemmas to know (all in `Init.Data.UInt.Lemmas`):

| Lemma | What it gives |
|---|---|
| `UInt64.le_iff_toNat_le` | `a ≤ b ↔ a.toNat ≤ b.toNat` (proved by `rfl`) |
| `UInt64.toNat_add` (`@[simp]`) | `(a + b).toNat = (a.toNat + b.toNat) % UInt64.size` |
| `UInt64.toNat_sub_of_le` (`@[simp]`) | `b ≤ a → (a - b).toNat = a.toNat - b.toNat` |
| `UInt64.toNat_lt` (`@[simp]`) | `n.toNat < 2 ^ 64` |
| `Nat.mod_eq_of_lt` | `n < m → n % m = n` (used with `toNat_add` to drop the `%`) |

## Why not `abbrev`?

The historical reason for using `notation` (over `abbrev`) was that **`omega` does not unfold `abbrev T : Type := Nat`.** Its preprocessor classifies hypotheses by their surface type and silently drops constraints over the alias, producing `omega could not prove the goal: No usable constraints found.`

Wrong:

```lean
abbrev Lamports : Type := Nat   -- omega will refuse to see (a : Lamports) ≤ b
```

Right:

```lean
namespace Solanalib.Lamports
-- declarations using Nat directly (the namespace header is parsed BEFORE the
-- notation is declared, so `Lamports` here is still an identifier).
end Solanalib.Lamports

/-- A lamport count: the smallest unit of native Solana value. -/
notation "Lamports" => Nat
```

`notation` is a parse-time substitution, so `(amount : Lamports)` is elaborated as `(amount : Nat)` from the start. omega and `simp`-set lemmas about `Nat` work without ceremony. The notation must be declared *after* any `namespace <SameName>` blocks in the same file, because the parser substitutes the token everywhere once the notation is in scope.

**Escape hatch:** if/when strict typing is needed (e.g. to enforce `≤ 2^64 - 1` on a `u64`-like quantity), promote to a single-field `structure` with explicit conversion. Plan to migrate the call sites mechanically; the migration is breaking but tractable.

## Attribute usage

- **`@[ext]`** on every `structure`. Generates the extensionality lemma `Foo.ext : a.f₁ = b.f₁ → … → a = b`. Costs nothing now, saves writing it later.
- **`@[simp]`** on lemmas that rewrite *toward* a normal form. The classic case: projection lemmas that expose a field after a constructor or update.

  ```lean
  @[simp]
  theorem credit_lamports (a : Account) (n : Lamports) :
      (credit a n).lamports = a.lamports + n := rfl
  ```

  Don't tag the headline theorem (`transfer_preserves_total`) with `@[simp]` — it's not a rewrite rule, it's a result.

- **`@[reducible]`** — almost never needed at small library scale. `notation` is the right answer for type synonyms.

## Proof style

- `by` at the end of the preceding line, never alone on its own line.
- Tactic block indented 2 spaces.
- Subgoals marked with `·` (centered dot), not `case`.
- `omega` for `Nat`/`Int` linear arithmetic. `linarith` for ordered field arithmetic. `decide` for closed decidable goals.
- **`simp` vs `simp only`:** prefer `simp [foo, bar]` for *terminal* calls — Mathlib explicitly discourages squeezing terminal `simp` to `simp only` because it makes proofs brittle to lemma renames. For *non-terminal* `simp`, squeezing to `simp only [...]` is fine for performance.
- **`simp` not closing → `omega` "no usable constraints":** check whether one of your types is an `abbrev` over `Nat`. See `## Type aliases` above.
- **`λ` is forbidden** — use `fun x ↦ y` (mapsto, not `=>`). Mathlib's linter rejects `λ`.
- **`$` is forbidden** — use `<|` for left-pipe or `|>` for right-pipe.

Canonical proof shape:

```lean
theorem transfer_preserves_total
    (src dst : Account) (amount : Lamports) (h : amount ≤ src.lamports) :
    (transfer src dst amount h).source.lamports
      + (transfer src dst amount h).destination.lamports
      = src.lamports + dst.lamports := by
  simp [transfer]
  omega
```

`simp [transfer]` unfolds the definition; `@[simp]` projection lemmas (e.g. `credit_lamports`, `debit_lamports`) then expose the field accesses; `omega` closes the resulting `Nat` arithmetic given `h`.

## Composition

Theorems compose via `have`-binding inside larger proofs:

```lean
example (src dst extra : Account) (amount : Lamports) (h : amount ≤ src.lamports) :
    let r := Account.transfer src dst amount h
    r.source.lamports + r.destination.lamports + extra.lamports
      = src.lamports + dst.lamports + extra.lamports := by
  have := Account.transfer_preserves_total src dst amount h
  omega
```

This is the pattern whenever a downstream proof needs an earlier result. `omega` will chain the `have` hypothesis with goal arithmetic.

## Project structure

```
<Library>.lean                  -- root: imports the library's modules
<Library>/<Concept>/*.lean      -- domain code, organised by concept
<Library>Test.lean              -- root for the regression-test library
<Library>Test/<Concept>/*Test.lean
scripts/lint-style.sh           -- textual style enforcement
```

- Don't put tests inside the main library directory — they'd ship in the published library.
- The library root re-exports everything; downstream users `import <Library>` for everything or import individual files.
- When a `<Concept>/Basic.lean` grows beyond ~5 lemmas, split into `<Concept>/Defs.lean` (the bare definitions) and `<Concept>/Basic.lean` (core API + simp lemmas). Mathlib's `Defs.lean`/`Basic.lean`/`Lemmas.lean` split keeps recompile times sane.

## CI workflows

- **`ci.yml`** — runs `lake build` + `lake test` on every push and PR, plus the textual lint script. Use explicit `elan install` + `lake update` + `lake exe cache get` rather than `leanprover/lean-action@v1` — lean-action requires a pre-existing `lake-manifest.json` and you want CI to work even after a manifest-bumping PR.
- **`docs.yml`** — runs `lake -Kenv=dev build <Library>:docs` and deploys `.lake/build/doc/` to GitHub Pages. Pages is configured with "Source: GitHub Actions" once via `gh api -X POST /repos/<owner>/<repo>/pages -f build_type=workflow`.
- **`update.yml`** — monthly cron + `workflow_dispatch` that runs `lake -Kenv=dev update` and opens a PR with the manifest diff. Scaled down from Mathlib's hourly version.
- **`dependabot.yml`** — monthly grouped updates for GitHub Actions versions.

## Common errors and fixes

### `invalid 'import' command, it must be used in the beginning of the file`

**Cause:** A `/-! ... -/` module docstring or any declaration sits above the `import` lines.

**Fix:** Order must be `/- copyright -/` block-comment, then `import` lines, then `/-! ... -/` module docstring. See `## File template`.

### `omega could not prove the goal: No usable constraints found.`

**Cause #1 (most common):** A type in the hypothesis is an `abbrev` over `Nat` (e.g. `abbrev Lamports : Type := Nat`). omega doesn't unfold it.

**Fix:** Change the `abbrev` to a `notation` declared after the namespace block. See `## Type aliases`.

**Cause #2:** Bare `simp` consumed the hypothesis by applying a rewrite like `Nat.sub_add_cancel`.

**Fix:** Use `simp only [...]` to restrict the simp set, then `omega`. (For terminal `simp` Mathlib still prefers bare `simp`; only restrict when omega follows.)

### `lean-action@v1`: `No lake-manifest.json found. Run lake update to generate manifest`

**Cause:** CI is calling `leanprover/lean-action@v1` but no `lake-manifest.json` is committed.

**Fix:** Commit `lake-manifest.json`. Generate it with `lake -Kenv=dev update` locally, then `git add lake-manifest.json`.

### `unexpected token 'Foo'; expected identifier` inside a `namespace Foo` declaration

**Cause:** `notation "Foo" => Bar` is declared *before* `namespace Foo`. The parser substitutes `Foo` and fails.

**Fix:** Move the `notation` declaration to after all `namespace Foo` blocks close in the file. Importing files are unaffected because dotted namespace names (`A.B.C`) are parsed as identifiers, not subject to token-level substitution.

### Docs build is 404 on the Pages URL

**Cause:** The Docs workflow hasn't run successfully yet, or Pages isn't enabled with "GitHub Actions" as source.

**Fix:** Check `.github/workflows/docs.yml` runs are green; if not, fix the underlying error. If runs are green but Pages is still 404, enable Pages: `gh api -X POST /repos/<owner>/<repo>/pages -f build_type=workflow`.

## Forbidden patterns (Mathlib lint)

- `λ` (use `fun … ↦ …`)
- `$` (use `<|` / `|>`)
- Empty lines inside a single declaration
- Indenting `namespace`/`section` bodies (flush left)
- Lines exceeding 100 characters
- Unicode outside the Mathlib allow-list (BiDi controls, invisibles)
- Bucket imports (`import Lean`, `import Mathlib`) without justification — always import the specific module
- Undisclosed LLM-generated content in PRs

## References for deeper rules

- [Mathlib4 style guide](https://leanprover-community.github.io/contribute/style.html)
- [Mathlib4 naming conventions](https://leanprover-community.github.io/contribute/naming.html)
- [Mathlib4 doc string conventions](https://leanprover-community.github.io/contribute/doc.html)
- The Mathlib4 source itself: representative files like `Mathlib/Algebra/Group/Basic.lean` and `Mathlib/Init.lean` show the conventions in action.
