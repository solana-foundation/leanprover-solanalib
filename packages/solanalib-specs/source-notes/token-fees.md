# Token transfer fees

The fee model follows `spl-token-2022-interface` **3.1.1**, using its immutable
[transfer-fee source][fees] at revision
`e18f9c6f9bf6044b934f48e3090e8e59e4820f02`. The full file has SHA-256
`2f51ac04733271b7578f0fb8c05805aac237f1521ffa1505b4055c03b6cbda5c`.
The registered subset includes `calculate_post_fee_amount`,
`calculate_pre_fee_amount` and `TransferFeeConfig::get_epoch_fee`.
`calculate_fee` is the shared helper used by the post-fee operation.

The reusable arithmetic and record types live in
`Solanalib.Specs.Core.TokenFee`. The arithmetic contracts and copied-value
selector live in `Solanalib.Specs.SplToken2022Interface.Fees`; the primary borrowed
selector is in `Solanalib.Specs.SplToken2022Interface.FeeReference`. Their controls are
in the corresponding `SolanalibTest.Specs` modules. Account-borrow and invocation
implementations require separate correctness arguments.

## Source correspondence

| Source symbol | Line | Modeled behavior |
| --- | --- | --- |
| `MAX_FEE_BASIS_POINTS` | 26 | 10,000 represents 100 percent. It does not restrict decoded `u16` values. |
| `TransferFee` | 34 | Epoch and cap retain their full `u64` ranges; rate retains its full `u16` range. |
| `TransferFee::ceil_div` | 50 | Check `u128` addition, then subtraction by one, then division. |
| `TransferFee::calculate_fee` | 58 | Zero shortcut; checked product and ceiling; conversion to `u64`; then minimum with the cap. |
| `TransferFee::calculate_post_fee_amount` | 73 | Compute the fee first, then checked subtraction from the input amount. |
| `TransferFee::calculate_pre_fee_amount` | 89 | Ordered zero-rate, zero-output, exact-100-percent, and general inverse branches. |
| `TransferFeeConfig` | 135 | Preserve both authority fields, withheld amount, and both fee records. |
| `TransferFeeConfig::get_epoch_fee` | 152 | Return a reference to newer exactly when `epoch >= newer.epoch`; otherwise return a reference to older. |

Natural-number intermediates represent unsigned checked arithmetic without
modular reduction. Inputs come from `UInt64` and `UInt16`, and each `u128`
addition or multiplication checks that its result is below `2^128`.
Subtraction checks its operand order, division rejects a zero denominator,
and conversion to `UInt64` checks that the value is below `2^64` before using
`UInt64.ofNat`. The conversion theorem proves that no successful conversion
changes the mathematical value. All call sites of the intermediate helpers
receive bounded source values or preceding successful checked results.

The order of these operations matters. For a rate above 10,000 and a large
input, the raw fee may exceed `u64::MAX`; `calculate_fee` returns `None` even
when the configured maximum fee is zero. A small input at the same rate can
produce a representable fee, followed by underflow in
`calculate_post_fee_amount`. A zero cap can instead make that small deduction
succeed. The model retains each possibility.

For the inverse, zero rate returns the requested output, and zero output
returns zero before checking whether the rate exceeds 10,000. The exact
100-percent branch checks cap-plus-output addition. The remaining branch
checks multiplication by 10,000, subtraction of the rate from 10,000,
ceiling division, and subtraction of the requested output. It then compares
that extra amount against the cap. The capped branch checks output-plus-cap
addition; the uncapped branch narrows the raw input to `u64`. Thus a zero cap
can recover `u64::MAX` in this inverse branch even if the uncapped raw input
would not fit. A rate above 10,000 with positive output always fails checked
denominator subtraction, including with a zero cap.

Selection checks only the newer epoch. The older fee is selected even when
the supplied epoch precedes the activation field of the older fee. The authorities of the
configuration and withheld amount do not affect selection and
remain unchanged.

## Borrowed fee selection

The primary `get_epoch_fee_live_contract` uses the shared `FieldReference`
vocabulary. Its result retains the parent identity and the selected older or
newer field. It reads the current newer epoch at the call, preserves state and
neither acquires nor consumes a dynamic borrow guard. Admission requires a
readable, live parent reference supplied by the source interpretation.

Later reads use that same field in the supplied current state; they do not
repeat epoch selection when a threshold changes. Available bytes alone do not
establish live access. The parent identity must distinguish expired lifetimes
from reused storage. These current-state observations do not authorize mutation
of ordinary Rust fields while a shared reference is held; legal state changes
and reference validity remain separate source-binding obligations.

`run_observation` connects the initial reference read to the copied-value
`get_epoch_fee_contract`. The latter remains a supporting observation and does
not specify the lifecycle of the returned reference. The generic reference family
has closed correctness, satisfiability and finite-execution witnesses. Controls
cover the equality boundary, distinct parent identities, fixed field selection
across changed thresholds, expired access and missing parents.

## Byte layout used by the extension decoder

`TransferFee` and `TransferFeeConfig` have `repr(C)` at lines 30 and 131.
The reviewed dependency profile uses `solana-zero-copy` 1.2.0,
`solana-nullable` 1.3.0 and `solana-address` 2.6.1, with exact source files in
the [registry](../source-map.json). The fee functions have no target-dependent
branch; their `serde` attributes affect derivations rather than arithmetic.

In the [unaligned integer source][unaligned], `U16` and `U64` are transparent
wrappers of `[u8; 2]` and `[u8; 8]` at lines 408 and 449. The conversion macro
asserts alignment one and the corresponding primitive size at lines 68–69.
It writes little-endian bytes at line 74 and reads little-endian bytes at
line 151. Its full SHA-256 is
`257b6f006f5355082aff3da7ba1113dbf0c38c10b6eee3d74feeaeb004e5f7e4`.

[`MaybeNull<T>`][nullable] is transparent at line 27, with its declaration at
line 34. Its full SHA-256 is
`bd3794fab8efe7a600b8aad74369a247db8d8f72090185e40841ef0d9841b3ee`.
[`Address`][address] is transparent at line 86 and wraps `[u8; 32]` at
line 108; its nullable implementation at line 393 designates 32 zero bytes
as absent. Its full SHA-256 is
`c93a7d9fb216e2778fba29a478ebe17ff9a538a7691aeed22e35264f32624904`.
The mathematical configuration preserves these raw authority bytes without
inventing a separate tag byte.

Consequently the `TransferFee` layout is 18 bytes, with epoch at offset 0,
maximum fee at offset 8, and basis points at offset 16. The configuration is
108 bytes: two 32-byte authorities, an 8-byte withheld amount at offset 64,
the older record at offset 72, and the newer record at offset 90. Typed TLV
decoding and its bounds checks are supplied by the extension model; the fee
arithmetic consumes the resulting values. The layout argument above is a
source review, not a proved compiler-layout theorem.

## Mathematical evidence and limits

Each arithmetic contract and the copied-value selector has a closed
`RealizedBy` reference witness and a closed `Satisfiable` witness. Their
preconditions admit all representable records and amounts, including rates above 100 percent;
the witnesses do not rely on an assumed interpretation or caller proof.
The reference functions are total mathematical functions whose ordinary
results include `None`. They preserve the entire fee record or configuration.

Generic theorems establish ceiling-rounding bounds, successful fee capping,
exact net-plus-fee conservation, zero and exact-100-percent behavior, failure
of excessive rates for positive inverse inputs, and epoch selection. A
separate bound proves that the explicit conversion in the model after successful subtraction adds no failure beyond the underflow check of the source.
Three test theorems derive
cap, failure, and conservation results for every total interpretation
satisfying the versioned contracts. Nineteen further test theorems exercise
the checked helper, rounding, cap ordering, both inverse overflow paths,
full-width rates, and distinct fee outcomes on both sides of the epoch boundary.
These are kernel-checked mathematical model results.

The contracts do not prove that compiled Rust implements this arithmetic.
The source review records why the definitions were chosen; an implementation
binding must still connect source integers and record storage to these values
and justify the modeled ordinary exits. The borrowed selector additionally
requires physical reference, lifetime and permission correspondence. Its
mathematical identity and access predicates do not themselves supply Rust
permissions. There is no token-processor success, account-state effect, or Agave
execution claim in the fee contracts.

[fees]: https://github.com/solana-program/token-2022/blob/e18f9c6f9bf6044b934f48e3090e8e59e4820f02/interface/src/extension/transfer_fee/mod.rs
[unaligned]: https://github.com/anza-xyz/solana-sdk/blob/5d3cfe493b77f916cb6f73cf034558065cae554f/zero-copy/src/unaligned.rs
[nullable]: https://github.com/anza-xyz/solana-sdk/blob/df930d35439b67b848bda57b7851d41ad3ce9dd2/nullable/src/maybe_null.rs
[address]: https://github.com/anza-xyz/solana-sdk/blob/14a725d6e9180e6cfbd98054473d61ef3aabde57/address/src/lib.rs
