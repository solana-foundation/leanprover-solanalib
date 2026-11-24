/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic

@[expose] public section

/-!
# Well-known addresses

Each address is given by the big-endian value of its 32 bytes, with the base58
form of `solana-sdk-ids-3.1.0/src/lib.rs` in the docstring.
-/

namespace Solanalib.Runtime.Ids

/-- `11111111111111111111111111111111` -/
def systemProgram : Pubkey := Pubkey.ofNat 0x0
/-- `NativeLoader1111111111111111111111111111111` -/
def nativeLoader : Pubkey :=
  Pubkey.ofNat 0x058784bf148ba4282fb012574888a9f153a07dadf765c0455c9a970380000000
/-- `BPFLoader1111111111111111111111111111111111`, loader v1, deprecated -/
def bpfLoaderDeprecated : Pubkey :=
  Pubkey.ofNat 0x02a8f6914e88a16bbd2395855f6404d9b4f456b7821bb0145749428c00000000
/-- `BPFLoader2111111111111111111111111111111111`, loader v2 -/
def bpfLoader : Pubkey :=
  Pubkey.ofNat 0x02a8f6914e88a16e395ae128948ffa695693376818dd47435221f3c600000000
/-- `BPFLoaderUpgradeab1e11111111111111111111111`, loader v3 -/
def bpfLoaderUpgradeable : Pubkey :=
  Pubkey.ofNat 0x02a8f6914e88a1b0e210153ef763ae2b00c2b93d16c124d2c0537a1004800000
/-- `LoaderV411111111111111111111111111111111111` -/
def loaderV4 : Pubkey :=
  Pubkey.ofNat 0x0512b4115151e37aad0a8bc5d3882e7b7fda4cf3d2c028c8cf83361800000000
/-- `AddressLookupTab1e1111111111111111111111111` -/
def addressLookupTable : Pubkey :=
  Pubkey.ofNat 0x0277a6af97339b7ac88d1892c90446f50002309266f62e53c118244982000000
/-- `ComputeBudget111111111111111111111111111111` -/
def computeBudget : Pubkey :=
  Pubkey.ofNat 0x0306466fe5211732ffecadba72c39be7bc8ce5bbc5f7126b2c439b3a40000000
/-- `Config1111111111111111111111111111111111111` -/
def config : Pubkey :=
  Pubkey.ofNat 0x03064aa3002f74dcc86e43310f0c052af8c5da27f6104019a323efa000000000
/-- `Ed25519SigVerify111111111111111111111111111` -/
def ed25519Program : Pubkey :=
  Pubkey.ofNat 0x037d46d67c93fbbe12f9428f838d40ff0570744927f48a64fcca704480000000
/-- `Feature111111111111111111111111111111111111` -/
def feature : Pubkey :=
  Pubkey.ofNat 0x03c0a0cdcb06d2daefae82d16fee7acf61ec737b23481b21946a767000000000
/-- `KeccakSecp256k11111111111111111111111111111` -/
def secp256k1Program : Pubkey :=
  Pubkey.ofNat 0x04c6fc20f050ccf05584d7211c9f8cf59ec14785bb166a1e2830e81220000000
/-- `Secp256r1SigVerify1111111111111111111111111` -/
def secp256r1Program : Pubkey :=
  Pubkey.ofNat 0x06920dec2fea71b5b723814d742da9031c83e75fdb795d568e75478020000000
/-- `Stake11111111111111111111111111111111111111` -/
def stakeProgram : Pubkey :=
  Pubkey.ofNat 0x06a1d8179137542a983437bdfe2a7ab2557f535c8a78722b68a49dc000000000
/-- `StakeConfig11111111111111111111111111111111` -/
def stakeConfig : Pubkey :=
  Pubkey.ofNat 0x06a1d817a502050b680791e6ce6db88e1e5b7150f61fc6790a4eb4d100000000
/-- `Vote111111111111111111111111111111111111111` -/
def voteProgram : Pubkey :=
  Pubkey.ofNat 0x0761481d357474bb7c4d7624ebd3bdb3d8355e73d11043fc0da3538000000000
/-- `ZkE1Gama1Proof11111111111111111111111111111` -/
def zkElGamalProofProgram : Pubkey :=
  Pubkey.ofNat 0x086375ace2aeea281a6b374d681ba76a53ccf638c07455936c05d06540000000
/-- `ZkTokenProof1111111111111111111111111111111` -/
def zkTokenProofProgram : Pubkey :=
  Pubkey.ofNat 0x0863ba8dd9c4c2fb174a05cba27e2a2cd623573d79e90b35b579fc0d00000000
/-- `1nc1nerator11111111111111111111111111111111` -/
def incinerator : Pubkey :=
  Pubkey.ofNat 0x003390728d34116079bdc911bfff00dbd44d2ecdccf79ca6e10038e100000000

/-- `Sysvar1111111111111111111111111111111111111`, the owner of every sysvar account -/
def sysvarOwner : Pubkey :=
  Pubkey.ofNat 0x06a7d5171875f729c73d93408f216120067ed88c76e08c287fc1946000000000
/-- `Sysvar1nstructions1111111111111111111111111` -/
def sysvarInstructions : Pubkey :=
  Pubkey.ofNat 0x06a7d517187bd16635dad40455fdc2c0c124c68f215675a5dbbacb5f08000000
/-- `SysvarC1ock11111111111111111111111111111111` -/
def sysvarClock : Pubkey :=
  Pubkey.ofNat 0x06a7d51718c774c928566398691d5eb68b5eb8a39b4b6d5c73555b2100000000
/-- `SysvarEpochRewards1111111111111111111111111` -/
def sysvarEpochRewards : Pubkey :=
  Pubkey.ofNat 0x06a7d51718dc3fee02a558bf83ce66e144422a1c34950b27c1869b5a9c000000
/-- `SysvarEpochSchedu1e111111111111111111111111` -/
def sysvarEpochSchedule : Pubkey :=
  Pubkey.ofNat 0x06a7d51718dc3fee02d3e47f0100f8b054f7942e60591e3f508719a805000000
/-- `SysvarFees111111111111111111111111111111111` -/
def sysvarFees : Pubkey :=
  Pubkey.ofNat 0x06a7d51718e25a8d83503c251a7af07126fd7200df6fc4ed526a9c9000000000
/-- `SysvarLastRestartS1ot1111111111111111111111` -/
def sysvarLastRestartSlot : Pubkey :=
  Pubkey.ofNat 0x06a7d5171906dde1cd3f947dcab4c8f4f4f51bad0f9813b800d289471fc00000
/-- `SysvarRecentB1ockHashes11111111111111111111` -/
def sysvarRecentBlockhashes : Pubkey :=
  Pubkey.ofNat 0x06a7d517192c568ee08a845f73d29788cf035c3145b21ab344d8062ea9400000
/-- `SysvarRent111111111111111111111111111111111` -/
def sysvarRent : Pubkey :=
  Pubkey.ofNat 0x06a7d517192c5c51218cc94c3d4af17f58daee089ba1fd44e3dbd98a00000000
/-- `SysvarRewards111111111111111111111111111111` -/
def sysvarRewards : Pubkey :=
  Pubkey.ofNat 0x06a7d517192c6137cee092d9b6923ee1ccd61903fa82b8a16191578d80000000
/-- `SysvarS1otHashes111111111111111111111111111` -/
def sysvarSlotHashes : Pubkey :=
  Pubkey.ofNat 0x06a7d517192f0aafc6f265e3fb77cc7ada82c529d0be3b136e2d005520000000
/-- `SysvarS1otHistory11111111111111111111111111` -/
def sysvarSlotHistory : Pubkey :=
  Pubkey.ofNat 0x06a7d517192f0aafc875e2e184577c5069cfc84649e3eb92782f958d48000000
/-- `SysvarStakeHistory1111111111111111111111111` -/
def sysvarStakeHistory : Pubkey :=
  Pubkey.ofNat 0x06a7d517193584d0feed9bb3431d13206be544281b57b8566cc5375ff4000000

/-- The four loaders of `PROGRAM_OWNERS` in Agave 4.3.2,
`svm/src/account_loader.rs`. -/
def bpfLoaders : List Pubkey := [bpfLoaderDeprecated, bpfLoader, bpfLoaderUpgradeable, loaderV4]

/-- The account keys represented from Agave 4.3.2
`reserved-account-keys/src/lib.rs`. The message demotes them to read-only.
In that release secp256r1 is always reserved; the argument retains the historical
feature-dependent choice used by the 3.1.12 profile. See
[message privileges](../../source-notes/agave-4.3.2.md#message-privileges-and-instructions-sysvar).
-/
def reservedKeys (secp256r1Active : Bool) : List Pubkey :=
  [addressLookupTable, bpfLoader, bpfLoaderDeprecated, bpfLoaderUpgradeable, computeBudget,
    config, ed25519Program, feature, loaderV4, secp256k1Program] ++
  (if secp256r1Active then [secp256r1Program] else []) ++
  [stakeConfig, stakeProgram, systemProgram, voteProgram, zkElGamalProofProgram,
    zkTokenProofProgram, sysvarClock, sysvarEpochRewards, sysvarEpochSchedule, sysvarFees,
    sysvarInstructions, sysvarLastRestartSlot, sysvarRecentBlockhashes, sysvarRent,
    sysvarRewards, sysvarSlotHashes, sysvarSlotHistory, sysvarStakeHistory, nativeLoader,
    sysvarOwner]

end Solanalib.Runtime.Ids
