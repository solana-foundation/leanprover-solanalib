/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Account.Basic
import Solanalib.Account.Transfer
import Solanalib.Instruction.Basic
import Solanalib.Primitives.Lamports
import Solanalib.Primitives.Pubkey

/-!
# Solanalib

A library of formal models and verified results for Solana programs in Lean 4.

Solanalib provides reusable type-level models of Solana primitives — lamports,
accounts, instructions, programs — together with theorems about their behaviour.
The intent is that downstream verification work on Anchor or Pinocchio programs
can reuse these definitions rather than redefining them per project.

## Organisation

Modules are organised by Solana concept, not by framework. Framework-specific
results (Anchor account validation, Pinocchio entrypoint patterns, …) layer on
top of the core primitives and live in their own subdirectories.

* `Solanalib.Primitives` — units and identifiers (`Lamports`, eventually `Pubkey`, `Slot`).
* `Solanalib.Account`    — the account model and operations over it.
-/
