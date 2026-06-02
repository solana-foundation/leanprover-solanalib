---
name: sf-solanalib-skill
description: Conventions and workflows for the Solanalib Lean 4 library — Mathlib4-derived style adapted for Solana formal verification. Use when user asks to "add a theorem to Solanalib", "create a Solanalib module", "fix a Lean build error in Solanalib", "review Solanalib code", "add a Solana primitive type", "structure a Lean library like Mathlib", or when editing `.lean`/`lakefile.lean` files in this repo.
metadata:
  author: Solanalib Contributors
  version: 0.1.0
---

# Solanalib

Solanalib is the Lean 4 "Mathlib for Solana": reusable formal models of Solana primitives (lamports, accounts, instructions, PDAs, …) plus theorems about them. Downstream verification of Anchor/Pinocchio programs depends on these.

This skill encodes the Mathlib4-derived conventions Solanalib has adopted, plus a few Solana-specific defaults and the one painful gotcha (`abbrev`/`omega`) we learned the hard way.

## When this skill applies

- Adding or modifying any `.lean` file under this repo.
- Editing `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, or `.github/workflows/`.
- Reviewing a Solanalib PR or designing a new module.
- Bootstrapping a sibling Lean 4 library that should follow these conventions.

## Default decisions

Make these without asking:

- **Verify locally before pushing.** `elan` is installed at `~/.elan/`. Use `PATH="$HOME/.elan/bin:$PATH" lake build` (and `lake test`) before any push. CI iterations are 2 min; local builds are seconds. Never push a Lean change without a local build pass.
- **Track Mathlib's `lean-toolchain` pin.** When bumping Lean, fetch `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain`, set `lean-toolchain` to match, and update the Mathlib `require` rev in `lakefile.lean` to the same tag. `doc-gen4`'s `main` branch tracks this — drift breaks docs.
- **Copyright authorship line is `Solanalib Contributors`.** Never personal names, never "Solana Foundation Contributors". The `Copyright (c) YEAR Solana Foundation` line is the legal-owner statement and is separate.
- **No AI-attribution trailers** (`Co-Authored-By: Claude …`) in commits.
- **Commit `lake-manifest.json`** but not `.lake/`. Reproducible builds depend on the manifest; `.lake/` is per-machine cache.

## Operating procedure

### Adding a new module

1. Decide the file path: `Solanalib/<Concept>/<Aspect>.lean`. Organise by **Solana concept** (Account, Token, Pda, Instruction), not by **framework** (Anchor, Pinocchio). Framework-specific results layer on top under `Solanalib/Anchor/`, `Solanalib/Pinocchio/`.
2. Write the file using the template in `## File template` below.
3. Add `import Solanalib.<Concept>.<Aspect>` to `Solanalib.lean` (alphabetical within its block).
4. Run `lake build` locally. Fix any errors. Run `lake test`.
5. If the module introduces a load-bearing API surface, add a regression test under `SolanalibTest/<Concept>/<Aspect>Test.lean` and import it from `SolanalibTest.lean`.

### Adding a new theorem

1. Place it in the file whose subject it concerns (`Account/Transfer.lean` for transfer properties, not in a global `Theorems.lean`).
2. Name it `<conclusion>_of_<hypothesis>` or `<conclusion>` if descriptive on its own. Examples in Mathlib: `add_pos_of_pos_of_nonneg`, `Nat.sub_add_cancel`.
3. Write the statement with all binders explicit (no `autoImplicit` — it's globally off in `lakefile.lean`).
4. Prefer term-mode proofs (`:= rfl`, `:= by simp`) over multi-line `by` blocks when feasible. Otherwise use the tactic style in `## Proof style` below.
5. Tag with `@[simp]` only if the lemma rewrites toward a normal form. Don't tag the headline theorem.

### Adding a new type

**Default to `notation` over `abbrev` when the type is a synonym for `Nat`/`Int`.** See `## Type aliases: notation, not abbrev` below — this is the most-likely-to-bite gotcha in the project.

For real structures, use `structure`/`inductive` with `@[ext]`:

```lean
@[ext]
structure Slot where
  /-- The slot number on the cluster. -/
  value : Nat
  deriving Repr, DecidableEq
```

## File template

Every `.lean` file in the library starts with this exact shape:

```lean
/-
Copyright (c) <YEAR> Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.<dep1>
import Solanalib.<dep2>          -- alphabetical within their block

/-!
# <Module title — short, capitalised>

<One-paragraph summary explaining what this module is for and why it exists.
End at the level of "what does this file give to the rest of the library".>

## Main definitions

* `Solanalib.Foo` — <one-line gloss>
* `Solanalib.Foo.bar` — <one-line gloss>

## Main statements

* `foo_property_baz` — <what it proves and why it matters>
-/

namespace Solanalib

-- declarations

end Solanalib
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

## Type aliases: notation, not abbrev

**`omega` in Lean 4.31.0-rc1 does not unfold `abbrev T : Type := Nat`** — its preprocessor classifies hypotheses by their surface type and silently drops `Lamports`-typed constraints. This burned four CI cycles before we caught it.

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

`notation` is a parse-time substitution, so `(amount : Lamports)` is elaborated as `(amount : Nat)` from the start. omega and `simp`-set lemmas about `Nat` work without ceremony. The notation must be declared *after* any `namespace Lamports` blocks in the same file, because the parser substitutes the token everywhere once the notation is in scope.

The same trap applies to future numeric synonyms (`Slot`, `Epoch`, `Pubkey` if defined as `ByteArray`-alias, etc.). Default to `notation` for these.

**Escape hatch:** if/when we need strict typing (e.g. to enforce `≤ 2^64 - 1` on lamports), promote to a single-field `structure` with explicit conversion. Plan to migrate the call sites mechanically; the migration is breaking but tractable.

## Attribute usage

- **`@[ext]`** on every structure. Generates the extensionality lemma `Foo.ext : a.f₁ = b.f₁ → … → a = b`. Costs nothing now, saves writing it later.
- **`@[simp]`** on lemmas that rewrite *toward* a normal form. The classic case: projection lemmas that expose a field after a constructor or update, e.g.

  ```lean
  @[simp]
  theorem credit_lamports (a : Account) (n : Lamports) :
      (credit a n).lamports = a.lamports + n := rfl
  ```

  Don't tag the headline theorem (`transfer_preserves_total`) with `@[simp]` — it's not a rewrite rule, it's a result.

- **`@[reducible]`** — almost never needed at our scale. `notation` is the right answer for type synonyms.

## Proof style

- `by` at end of the preceding line, never alone.
- Tactic block indented 2 spaces.
- Subgoals marked with `·` (centered dot), not `case`.
- `omega` for `Nat`/`Int` linear arithmetic. `linarith` for ordered field arithmetic. `decide` for closed decidable goals.
- **`simp` vs `simp only`:** prefer `simp [foo, bar]` for terminal calls — Mathlib explicitly discourages squeezing terminal `simp` to `simp only` because it makes proofs brittle to lemma renames. For non-terminal `simp`, squeezing to `simp only [...]` is fine for performance.
- **`simp` not closing → `omega` "no usable constraints":** check whether one of your types is an `abbrev` over `Nat`. See `## Type aliases` above.
- **`λ` is forbidden** — use `fun x ↦ y` (mapsto, not `=>`). Mathlib's linter rejects `λ`.
- **`$` is forbidden** — use `<|` for left-pipe or `|>` for right-pipe.

Example of the canonical proof shape, taken from `Solanalib/Account/Transfer.lean`:

```lean
theorem transfer_preserves_total
    (src dst : Account) (amount : Lamports) (h : amount ≤ src.lamports) :
    (transfer src dst amount h).source.lamports
      + (transfer src dst amount h).destination.lamports
      = src.lamports + dst.lamports := by
  simp [transfer]
  omega
```

`simp [transfer]` unfolds the definition; the `@[simp]` lemmas `credit_lamports` and `debit_lamports` then expose the lamports projections; `omega` closes the resulting `Nat` arithmetic given `h`.

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

This is the pattern to reach for whenever a downstream proof needs an earlier result. `omega` will chain the `have` hypothesis with goal arithmetic.

## Project structure

```
Solanalib.lean                  -- root: imports the library's modules
Solanalib/<Concept>/*.lean       -- domain code, organised by Solana concept
SolanalibTest.lean              -- root for the regression-test library
SolanalibTest/<Concept>/*Test.lean
```

- Don't put tests inside `Solanalib/` — they'd ship in the published library.
- The library root re-exports everything; downstream users import individual files or `import Solanalib` for everything.
- When a `<Concept>/Basic.lean` grows beyond ~5 lemmas, split into `<Concept>/Defs.lean` (the bare definitions) and `<Concept>/Basic.lean` (core API + simp lemmas). Mathlib's `Defs.lean`/`Basic.lean`/`Lemmas.lean` split keeps recompile times sane.

## CI workflows

- **`ci.yml`** — runs `lake build` + `lake test` on every push and PR. Uses explicit `elan install` + `lake update` + `lake exe cache get` rather than `leanprover/lean-action@v1`, because lean-action requires a pre-existing `lake-manifest.json` and we want CI to work even after a manifest-bumping PR.
- **`docs.yml`** — runs `lake -Kenv=dev build Solanalib:docs` and deploys `.lake/build/doc/` to GitHub Pages. Pages is configured with "Source: GitHub Actions" (set once via `gh api -X POST /repos/<owner>/<repo>/pages -f build_type=workflow`).
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

**Cause:** CI is calling `leanprover/lean-action@v1` but no `lake-manifest.json` is committed (or the manifest hasn't been refreshed after a lakefile change).

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
