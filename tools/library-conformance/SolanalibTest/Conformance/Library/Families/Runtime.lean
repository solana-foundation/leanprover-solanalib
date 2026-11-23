/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Rent
import SolanalibTest.Conformance.Library.Families.Runtime.Values
import SolanalibTest.Conformance.Library.Families.Runtime.Instructions
import SolanalibTest.Conformance.Library.Families.Runtime.Syscalls
import SolanalibTest.Conformance.Library.Families.Runtime.Accounts
import SolanalibTest.Conformance.Library.Families.Runtime.Host
import SolanalibTest.Conformance.Library.Families.Runtime.RawSyscalls

/-!
# Family `runtime`: sysvar getters, Rent arithmetic, the Instructions sysvar,
# logging, return data, hashing, curve validation, raw syscalls and small value helpers

Drivers `rust/runtime-pinocchio-0-10-2`,
`rust/runtime-rent-3-0-0` and `rust/runtime-pinocchio-0-11-1`, and
`rust/runtime-pinocchio-0-10-2-wrapping` and `rust/runtime-rent-3-0-0-wrapping`, which
record the Rent arithmetic without overflow checks (`*_wrapping` corpora), and
`rust/runtime-sysvar-3-1-1-host` and `rust/runtime-program-4-0-0-host`, built without the
Solana cfg, which record the host branches (`*_host` corpora). One
corpus file per library root, plus `pinocchio_0_11_1_accounts` for the calls over
loader-serialized accounts; function names repeat across the two pinocchio
versions, so the corpus file selects the version. `rust/runtime-pinocchio-0-11-1` also calls
the raw `sol_sha256`, `sol_log_`, `sol_panic_` and `abort` of solana-define-syscall
5.1.0, the version pinocchio 0.11.1 links, directly (`solana_define_syscall`,
decided at the shim index of `RawSyscalls`): the `hashv` and `sol_log` records reach
those syscalls through define-syscall 4.0.1 and 5.2.0. The 5.2.0 raw-syscall corpus
adds SHA-512 and multiscalar multiplication through the same `RawSyscalls` provider.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Runtime

def corpora : List (String × List Checker) := [
  ("solana_rent_3_0_0", [Rent.minimumBalance]),
  ("solana_rent_3_0_0_wrapping", [Rent.minimumBalance]),
  ("solana_sysvar_3_1_1", [Syscalls.sdkClockGet, Syscalls.sdkRentGet]),
  ("solana_sysvar_3_1_1_host", [Host.sdkClockGet, Host.sdkRentGet]),
  ("pinocchio_0_10_2", [Rent.tryMinimumBalance102, Syscalls.pinClockGet102,
    Syscalls.pinRentGet102]),
  ("pinocchio_0_10_2_wrapping", [Rent.tryMinimumBalance102]),
  ("pinocchio_0_11_1", [Rent.tryMinimumBalance111, Syscalls.pinClockGet111] ++
    Instructions.checkers),
  ("pinocchio_0_11_1_accounts", Accounts.checkers),
  ("solana_msg_3_1_0", [Syscalls.solLog]),
  ("solana_msg_3_1_0_host", [Host.solLog]),
  ("solana_program_4_0_0", [Syscalls.solLogData, Syscalls.setReturnData]),
  ("solana_program_4_0_0_host", [Host.solLogData, Host.setReturnData]),
  ("solana_sha256_hasher_3_1_0", [Syscalls.hashv]),
  ("solana_curve25519_3_1_12", [Syscalls.validateEdwards]),
  ("solana_hash_4_5_0", [Values.toBytes]),
  ("solana_sdk_ids_3_1_0", [Values.systemProgramId]),
  ("solana_zero_copy_1_2_0", [Values.intoU64]),
  ("solana_program_option_3_1_0", Values.isSomeCheckers),
  ("solana_define_syscall_5_1_0", RawSyscalls.checkers),
  ("solana_define_syscall_5_2_0", [RawSyscalls.solSha512, RawSyscalls.solCurveMultiscalarMul])
]

end SolanalibTest.Conformance.Library.Families.Runtime
