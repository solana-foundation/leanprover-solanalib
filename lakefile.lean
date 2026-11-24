import Lake
open Lake DSL

/-!
## Solanalib

Lean models of the Solana runtime and of the Rust crates Solana programs are built on.
Every library below belongs to this one package; its sources live under `packages/`,
`tools/` and `examples/`.

Dependencies:
* Mathlib — pinned for the package; no library here imports it.
* doc-gen4 — gated behind `-Kenv=dev` so casual builds don't pay its cost.
-/

package solanalib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Mathlib's style linters, enabled as warnings (CI fails on any warning).
    ⟨`weak.linter.style.longLine, true⟩,
    ⟨`weak.linter.style.lambdaSyntax, true⟩,
    ⟨`weak.linter.style.dollarSyntax, true⟩,
    ⟨`weak.linter.style.cdotPattern, true⟩,
    ⟨`weak.linter.style.commandStart, true⟩
  ]
  testDriver := "SolanalibTest.Runtime"

require "leanprover-community" / "mathlib" @ git "v4.34.0"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "a6521b2d0c93dcdf2d640089f95548df5dd8bf46"

-- The getting-started example is checked like a scenario, not exported as a model.
lean_lib SolanalibTest.Examples where
  srcDir := "examples"
  roots := #[`SolanalibTest.Examples.CheckedTransfer]

-- These libraries share one package output directory because Lean resolves modules
-- by their top-level root. Source directories remain separate for navigation.
@[default_target]
lean_lib Solanalib.Runtime where
  srcDir := "packages/solanalib-runtime"
  roots := #[`Solanalib.Runtime]
  globs := #[.one `Solanalib.Runtime, .submodules `Solanalib.Runtime]

lean_lib SolanalibTest.Runtime where
  srcDir := "packages/solanalib-runtime"
  roots := #[`SolanalibTest.Runtime]
  globs := #[.one `SolanalibTest.Runtime, .submodules `SolanalibTest.Runtime]

lean_lib SolanalibTest.Conformance.Runtime where
  srcDir := "tools/runtime-conformance"
  roots := #[`SolanalibTest.Conformance.Runtime]

@[default_target]
lean_lib Solanalib.Contracts where
  srcDir := "packages/solanalib-contracts"
  roots := #[`Solanalib.Contracts]
  globs := #[.one `Solanalib.Contracts, .submodules `Solanalib.Contracts]

lean_lib Solanalib.Specs.Core where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.Core]
  globs := #[.andSubmodules `Solanalib.Specs.Core]

lean_lib SolanalibTest.Specs.Core where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.Core]
  globs := #[.andSubmodules `SolanalibTest.Specs.Core]

lean_lib Solanalib.Specs.AnchorLang where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.AnchorLang]
  globs := #[.andSubmodules `Solanalib.Specs.AnchorLang]

lean_lib SolanalibTest.Specs.AnchorLang where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.AnchorLang]
  globs := #[.andSubmodules `SolanalibTest.Specs.AnchorLang]

lean_lib Solanalib.Specs.AnchorSpl where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.AnchorSpl]
  globs := #[.andSubmodules `Solanalib.Specs.AnchorSpl]

lean_lib SolanalibTest.Specs.AnchorSpl where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.AnchorSpl]
  globs := #[.andSubmodules `SolanalibTest.Specs.AnchorSpl]

lean_lib Solanalib.Specs.Borsh where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.Borsh]
  globs := #[.andSubmodules `Solanalib.Specs.Borsh]

lean_lib SolanalibTest.Specs.Borsh where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.Borsh]
  globs := #[.andSubmodules `SolanalibTest.Specs.Borsh]

lean_lib Solanalib.Specs.Bytemuck where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.Bytemuck]
  globs := #[.andSubmodules `Solanalib.Specs.Bytemuck]

lean_lib SolanalibTest.Specs.Bytemuck where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.Bytemuck]
  globs := #[.andSubmodules `SolanalibTest.Specs.Bytemuck]

lean_lib Solanalib.Specs.Pinocchio where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.Pinocchio]
  globs := #[.andSubmodules `Solanalib.Specs.Pinocchio]

lean_lib SolanalibTest.Specs.Pinocchio where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.Pinocchio]
  globs := #[.andSubmodules `SolanalibTest.Specs.Pinocchio]

lean_lib Solanalib.Specs.PinocchioAssociatedTokenAccount where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PinocchioAssociatedTokenAccount]
  globs := #[.andSubmodules `Solanalib.Specs.PinocchioAssociatedTokenAccount]

lean_lib SolanalibTest.Specs.PinocchioAssociatedTokenAccount where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PinocchioAssociatedTokenAccount]
  globs := #[.andSubmodules `SolanalibTest.Specs.PinocchioAssociatedTokenAccount]

lean_lib Solanalib.Specs.PinocchioSystem where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PinocchioSystem]
  globs := #[.andSubmodules `Solanalib.Specs.PinocchioSystem]

lean_lib SolanalibTest.Specs.PinocchioSystem where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PinocchioSystem]
  globs := #[.andSubmodules `SolanalibTest.Specs.PinocchioSystem]

lean_lib Solanalib.Specs.PinocchioToken where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PinocchioToken]
  globs := #[.andSubmodules `Solanalib.Specs.PinocchioToken]

lean_lib SolanalibTest.Specs.PinocchioToken where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PinocchioToken]
  globs := #[.andSubmodules `SolanalibTest.Specs.PinocchioToken]

lean_lib Solanalib.Specs.PinocchioToken2022 where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PinocchioToken2022]
  globs := #[.andSubmodules `Solanalib.Specs.PinocchioToken2022]

lean_lib SolanalibTest.Specs.PinocchioToken2022 where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PinocchioToken2022]
  globs := #[.andSubmodules `SolanalibTest.Specs.PinocchioToken2022]

lean_lib Solanalib.Specs.PythSolanaReceiverSdk where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PythSolanaReceiverSdk]
  globs := #[.andSubmodules `Solanalib.Specs.PythSolanaReceiverSdk]

lean_lib SolanalibTest.Specs.PythSolanaReceiverSdk where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PythSolanaReceiverSdk]
  globs := #[.andSubmodules `SolanalibTest.Specs.PythSolanaReceiverSdk]

lean_lib Solanalib.Specs.PythnetSdk where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PythnetSdk]
  globs := #[.andSubmodules `Solanalib.Specs.PythnetSdk]

lean_lib SolanalibTest.Specs.PythnetSdk where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PythnetSdk]
  globs := #[.andSubmodules `SolanalibTest.Specs.PythnetSdk]

lean_lib Solanalib.Specs.SolanaAccountInfo where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaAccountInfo]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaAccountInfo]

lean_lib SolanalibTest.Specs.SolanaAccountInfo where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaAccountInfo]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaAccountInfo]

lean_lib Solanalib.Specs.SolanaAccountView where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaAccountView]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaAccountView]

lean_lib SolanalibTest.Specs.SolanaAccountView where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaAccountView]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaAccountView]

lean_lib Solanalib.Specs.SolanaAddress where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaAddress]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaAddress]

lean_lib SolanalibTest.Specs.SolanaAddress where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaAddress]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaAddress]

lean_lib Solanalib.Specs.SolanaAddressLookupTableInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaAddressLookupTableInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaAddressLookupTableInterface]

lean_lib SolanalibTest.Specs.SolanaAddressLookupTableInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaAddressLookupTableInterface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaAddressLookupTableInterface]

lean_lib Solanalib.Specs.SolanaBorsh where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaBorsh]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaBorsh]

lean_lib SolanalibTest.Specs.SolanaBorsh where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaBorsh]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaBorsh]

lean_lib Solanalib.Specs.SolanaCurve25519 where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaCurve25519]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaCurve25519]

lean_lib SolanalibTest.Specs.SolanaCurve25519 where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaCurve25519]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaCurve25519]

lean_lib Solanalib.Specs.SolanaDefineSyscall where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaDefineSyscall]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaDefineSyscall]

lean_lib SolanalibTest.Specs.SolanaDefineSyscall where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaDefineSyscall]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaDefineSyscall]

lean_lib Solanalib.Specs.SolanaEpochSchedule where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaEpochSchedule]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaEpochSchedule]

lean_lib SolanalibTest.Specs.SolanaEpochSchedule where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaEpochSchedule]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaEpochSchedule]

lean_lib Solanalib.Specs.SolanaCpi where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaCpi]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaCpi]

lean_lib SolanalibTest.Specs.SolanaCpi where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaCpi]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaCpi]

lean_lib Solanalib.Specs.SolanaHash where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaHash]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaHash]

lean_lib SolanalibTest.Specs.SolanaHash where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaHash]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaHash]

lean_lib Solanalib.Specs.SolanaInstruction where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaInstruction]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaInstruction]

lean_lib SolanalibTest.Specs.SolanaInstruction where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaInstruction]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaInstruction]

lean_lib Solanalib.Specs.SolanaInstructionView where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaInstructionView]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaInstructionView]

lean_lib SolanalibTest.Specs.SolanaInstructionView where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaInstructionView]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaInstructionView]

lean_lib Solanalib.Specs.SolanaInvoke where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaInvoke]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaInvoke]

lean_lib SolanalibTest.Specs.SolanaInvoke where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaInvoke]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaInvoke]

lean_lib Solanalib.Specs.SolanaMsg where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaMsg]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaMsg]

lean_lib SolanalibTest.Specs.SolanaMsg where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaMsg]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaMsg]

lean_lib Solanalib.Specs.SolanaNullable where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaNullable]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaNullable]

lean_lib SolanalibTest.Specs.SolanaNullable where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaNullable]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaNullable]

lean_lib Solanalib.Specs.SolanaProgram where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaProgram]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaProgram]

lean_lib SolanalibTest.Specs.SolanaProgram where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaProgram]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaProgram]

lean_lib Solanalib.Specs.SolanaProgramError where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaProgramError]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaProgramError]

lean_lib SolanalibTest.Specs.SolanaProgramError where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaProgramError]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaProgramError]

lean_lib Solanalib.Specs.SolanaProgramOption where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaProgramOption]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaProgramOption]

lean_lib SolanalibTest.Specs.SolanaProgramOption where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaProgramOption]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaProgramOption]

lean_lib Solanalib.Specs.SolanaPubkey where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaPubkey]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaPubkey]

lean_lib SolanalibTest.Specs.SolanaPubkey where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaPubkey]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaPubkey]

lean_lib Solanalib.Specs.SolanaRent where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaRent]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaRent]

lean_lib SolanalibTest.Specs.SolanaRent where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaRent]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaRent]

lean_lib Solanalib.Specs.SolanaSdkIds where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaSdkIds]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaSdkIds]

lean_lib SolanalibTest.Specs.SolanaSdkIds where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaSdkIds]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaSdkIds]

lean_lib Solanalib.Specs.SolanaSha256Hasher where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaSha256Hasher]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaSha256Hasher]

lean_lib SolanalibTest.Specs.SolanaSha256Hasher where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaSha256Hasher]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaSha256Hasher]

lean_lib Solanalib.Specs.SolanaStakeInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaStakeInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaStakeInterface]

lean_lib SolanalibTest.Specs.SolanaStakeInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaStakeInterface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaStakeInterface]

lean_lib Solanalib.Specs.SolanaSystemInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaSystemInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaSystemInterface]

lean_lib SolanalibTest.Specs.SolanaSystemInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaSystemInterface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaSystemInterface]

lean_lib Solanalib.Specs.SolanaSysvar where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaSysvar]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaSysvar]

lean_lib SolanalibTest.Specs.SolanaSysvar where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaSysvar]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaSysvar]

lean_lib Solanalib.Specs.SolanaZeroCopy where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaZeroCopy]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaZeroCopy]

lean_lib SolanalibTest.Specs.SolanaZeroCopy where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaZeroCopy]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaZeroCopy]

lean_lib Solanalib.Specs.SplToken2022 where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplToken2022]
  globs := #[.andSubmodules `Solanalib.Specs.SplToken2022]

lean_lib SolanalibTest.Specs.SplToken2022 where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplToken2022]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplToken2022]

lean_lib Solanalib.Specs.SplToken2022Interface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplToken2022Interface]
  globs := #[.andSubmodules `Solanalib.Specs.SplToken2022Interface]

lean_lib SolanalibTest.Specs.SplToken2022Interface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplToken2022Interface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplToken2022Interface]

lean_lib Solanalib.Specs.SplTokenInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplTokenInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SplTokenInterface]

lean_lib SolanalibTest.Specs.SplTokenInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplTokenInterface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplTokenInterface]

lean_lib Solanalib.Specs.SwitchboardOnDemand where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SwitchboardOnDemand]
  globs := #[.andSubmodules `Solanalib.Specs.SwitchboardOnDemand]

lean_lib SolanalibTest.Specs.SwitchboardOnDemand where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SwitchboardOnDemand]
  globs := #[.andSubmodules `SolanalibTest.Specs.SwitchboardOnDemand]

lean_lib Solanalib.Specs.SplAssociatedTokenAccountClient where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplAssociatedTokenAccountClient]
  globs := #[.andSubmodules `Solanalib.Specs.SplAssociatedTokenAccountClient]

lean_lib SolanalibTest.Specs.SplAssociatedTokenAccountClient where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplAssociatedTokenAccountClient]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplAssociatedTokenAccountClient]

lean_lib Solanalib.Specs.SplMemo where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplMemo]
  globs := #[.andSubmodules `Solanalib.Specs.SplMemo]

lean_lib SolanalibTest.Specs.SplMemo where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplMemo]
  globs := #[.one `SolanalibTest.Specs.SplMemo]

lean_lib Solanalib.Specs.SplTokenMetadataInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplTokenMetadataInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SplTokenMetadataInterface]

lean_lib SolanalibTest.Specs.SplTokenMetadataInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplTokenMetadataInterface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplTokenMetadataInterface]

lean_lib Solanalib.Specs.PinocchioLog where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.PinocchioLog]
  globs := #[.andSubmodules `Solanalib.Specs.PinocchioLog]

lean_lib SolanalibTest.Specs.PinocchioLog where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.PinocchioLog]
  globs := #[.andSubmodules `SolanalibTest.Specs.PinocchioLog]

lean_lib Solanalib.Specs.SolanaProgramEntrypoint where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaProgramEntrypoint]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaProgramEntrypoint]

lean_lib SolanalibTest.Specs.SolanaProgramEntrypoint where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaProgramEntrypoint]
  globs := #[.one `SolanalibTest.Specs.SolanaProgramEntrypoint]

lean_lib Solanalib.Specs.SplPod where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplPod]
  globs := #[.andSubmodules `Solanalib.Specs.SplPod]

lean_lib SolanalibTest.Specs.SplPod where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplPod]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplPod]

lean_lib Solanalib.Specs.SplToken where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplToken]
  globs := #[.andSubmodules `Solanalib.Specs.SplToken]

lean_lib SolanalibTest.Specs.SplToken where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplToken]
  globs := #[.one `SolanalibTest.Specs.SplToken]

lean_lib Solanalib.Specs.SplTransferHookInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplTransferHookInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SplTransferHookInterface]

lean_lib SolanalibTest.Specs.SplTransferHookInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplTransferHookInterface]
  globs := #[.one `SolanalibTest.Specs.SplTransferHookInterface]

lean_lib Solanalib.Specs.AnchorLangError where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.AnchorLangError]
  globs := #[.andSubmodules `Solanalib.Specs.AnchorLangError]

lean_lib SolanalibTest.Specs.AnchorLangError where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.AnchorLangError]
  globs := #[.one `SolanalibTest.Specs.AnchorLangError]

lean_lib Solanalib.Specs.SolanaInstructionsSysvar where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaInstructionsSysvar]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaInstructionsSysvar]

lean_lib SolanalibTest.Specs.SolanaInstructionsSysvar where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaInstructionsSysvar]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaInstructionsSysvar]

lean_lib Solanalib.Specs.SolanaLoaderV3Interface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SolanaLoaderV3Interface]
  globs := #[.andSubmodules `Solanalib.Specs.SolanaLoaderV3Interface]

lean_lib SolanalibTest.Specs.SolanaLoaderV3Interface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SolanaLoaderV3Interface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SolanaLoaderV3Interface]

lean_lib Solanalib.Specs.SplAssociatedTokenAccountInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`Solanalib.Specs.SplAssociatedTokenAccountInterface]
  globs := #[.andSubmodules `Solanalib.Specs.SplAssociatedTokenAccountInterface]

lean_lib SolanalibTest.Specs.SplAssociatedTokenAccountInterface where
  srcDir := "packages/solanalib-specs"
  roots := #[`SolanalibTest.Specs.SplAssociatedTokenAccountInterface]
  globs := #[.andSubmodules `SolanalibTest.Specs.SplAssociatedTokenAccountInterface]

lean_lib SolanalibTest.Conformance.Library where
  srcDir := "tools/library-conformance"
  roots := #[`SolanalibTest.Conformance.Library]
  globs := #[.andSubmodules `SolanalibTest.Conformance.Library]
  leanOptions := #[⟨`autoImplicit, true⟩]

lean_exe «solanalib-library-conformance» where
  srcDir := "tools/library-conformance"
  root := `SolanalibTest.Conformance.LibraryMain
  leanOptions := #[⟨`autoImplicit, true⟩]

lean_exe «solanalib-selection-control» where
  srcDir := "tools/library-conformance"
  root := `SolanalibTest.Conformance.SelectionMain
  leanOptions := #[⟨`autoImplicit, true⟩]

-- The sBPF machine model is an exploration, separate from the runtime and SDK models.
lean_lib Solanalib.SBPF where
  srcDir := "packages/solanalib-sbpf"
  roots := #[`Solanalib.SBPF]
  globs := #[.one `Solanalib.SBPF, .submodules `Solanalib.SBPF]

lean_lib SolanalibTest.SBPF where
  srcDir := "packages/solanalib-sbpf"
  roots := #[`SolanalibTest.SBPF]
  globs := #[.one `SolanalibTest.SBPF, .submodules `SolanalibTest.SBPF]

/-- Command-line front end to the sBPF interpreter, for differential testing. -/
lean_exe «sbpf-oracle» where
  srcDir := "packages/solanalib-sbpf"
  root := `SolanalibTest.SBPFOracle

/-- Check real module ownership; invoked with the source inventory by the Python wrapper. -/
script checkModuleOwners (args) do
  let ws ← getWorkspace
  let mut invalid := args.isEmpty
  for arg in args do
    let name := arg.toName
    -- Workspace.findModules reports only the last matching library per package.
    -- Count all library claims and executable roots so same-package overlaps fail too.
    let owners := ws.packages.flatMap fun pkg =>
      pkg.leanLibs.filterMap (·.findModule? name) ++ pkg.leanExes.filterMap (·.isRoot? name)
    if owners.size != 1 || owners.any (fun m => m.pkg.baseName != `solanalib) then
      let descriptions := owners.map (fun m => (m.pkg.baseName, m.lib.name))
      IO.eprintln s!"{name}: expected one root-package owner, got {descriptions}"
      invalid := true
  unless invalid do
    IO.println s!"Unique Lake ownership: {args.length} modules"
  return if invalid then 1 else 0

/-- Export the actual library configuration and module inventory for audit tools. -/
script libraryInventory (args) do
  let ws ← getWorkspace
  let mut rows := #[]
  let some pkg := ws.findPackageByName? `solanalib
    | IO.eprintln "The solanalib package is not loaded"; return 1
  for lib in pkg.leanLibs do
    if args.isEmpty || args.contains lib.name.toString then
      let modules ← lib.getModuleArray
      rows := rows.push <| Lean.Json.mkObj [
        ("name", Lean.toJson lib.name.toString),
        ("package", Lean.toJson lib.pkg.baseName.toString),
        ("srcDir", Lean.toJson lib.srcDir.toString),
        ("buildDir", Lean.toJson lib.pkg.leanLibDir.toString),
        ("roots", Lean.toJson <| lib.roots.map toString),
        ("globs", Lean.toJson <| lib.config.globs.map toString),
        ("modules", Lean.toJson <| modules.map fun m => m.name.toString),
        ("files", Lean.toJson <| modules.map fun m => m.leanFile.toString)]
  IO.println (Lean.Json.compress <| Lean.toJson rows)
  return 0
