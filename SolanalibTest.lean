/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Account.TransferTest
import SolanalibTest.Finance.LinearDecayTest
import SolanalibTest.LayerATests

/-!
# SolanalibTest

Regression tests for Solanalib. Each test file lives under `SolanalibTest/`
and uses `example` declarations so the test passes iff the file
type-checks. Run with `lake test` (which builds the `SolanalibTest` library
via the package's `testDriver`).
-/
