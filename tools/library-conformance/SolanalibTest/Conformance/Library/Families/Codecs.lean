/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Bytemuck
import SolanalibTest.Conformance.Library.Borsh161De
import SolanalibTest.Conformance.Library.Borsh161Ser
import SolanalibTest.Conformance.Library.Borsh161NostdIo
import SolanalibTest.Conformance.Library.Borsh0104
import SolanalibTest.Conformance.Library.StakeAddress
import SolanalibTest.Conformance.Library.Pyth

/-!
# Family `Codecs` (PR #474): borsh, bytemuck, Address, StakeStateV2, Pyth decoding

Drivers `rust/codecs-borsh-0-10-4-bytemuck-1-25-2`, `rust/codecs-borsh-1-6-1-stake-3-1-0`,
`rust/pyth` and
`rust/borsh-1-6-1-nostd` (borsh 1.6.1 without its `std` feature, whose
`write_all` is the no-std provided method). Each corpus file is checked by
exactly these checkers. Function names repeat across versions (borsh 0.10.4
and 1.6.1), so the corpus file selects the version. borsh
0.10.4 `Vec<T>` decoding is decided with its heap requests (`BorshVecHeap`),
and `hint::cautious` on the records the driver derives from those runs
(`Borsh0104`); `controls/Codecs.py` corrupts both.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Codecs

def corpora : List (String × List Checker) := [
  ("borsh_0_10_4", Borsh.V0104.checkers),
  ("borsh_1_6_1", Borsh.V161.checkers ++ Borsh.V161Ser.checkers),
  ("borsh_1_6_1_nostd_io", Borsh.V161NostdIo.checkers),
  ("bytemuck_1_25_2", Bytemuck.bytemuck_1_25_2),
  ("bytemuck_1_25_0", Bytemuck.bytemuck_1_25_0),
  ("solana_address_2_6_0", StakeAddress.addressCheckers),
  ("solana_stake_interface_3_1_0", StakeAddress.stakeCheckers),
  ("pythnet_sdk_3_0_0", Pyth.pythnetCheckers),
  ("pyth_solana_receiver_sdk_2_0_0", Pyth.receiverCheckers)
]

end SolanalibTest.Conformance.Library.Families.Codecs
