# Rent representations and arithmetic

The Rent models share arithmetic vocabulary but retain different
representations and calculations: the `threshold_rate` and `fixed_rate` variants of Pinocchio, and Solana Rent. `usize` is interpreted at the recorded
64-bit width. The arithmetic profile explicitly chooses checked or wrapping
unsigned operations and a panic strategy. Normal values and ordinary
`ProgramError` results are distinct from unwind and termination.

Pinocchio 0.10.2 stores a 64-bit rate and eight little-endian threshold bytes.
Its `try_minimum_balance` first checks the data limit, then tests the current
rate bound, and only in the `else if` branch tests the larger SIMD rate bound.
That second rate guard is unreachable; the model proves this fact and preserves
the source order. A threshold of 1.0 selects `(128 + length) * rate`; 2.0 selects
`2 * (128 + length) * rate`. Other thresholds select the floating calculation on
non-BPF targets and panic on BPF before executing that absent calculation.
Threshold-one rates above the intended bound therefore remain possible and can
wrap or panic according to the explicit profile. The model does not repair the
source guard.

Pinocchio 0.11.1 stores only a 64-bit rate. Its checks are `length ≤ 10485760`
and `rate ≤ 1759197129867`, followed by `(128 + length) * rate`. A general theorem
proves that every accepted product fits below `2^64`, independently of an
overflow-check setting. Threshold bytes are absent from this value type.

The 0.11.1 account reader checks for an exclusive lease before checking the Rent
address. It returns `AccountBorrowFailed` for that lease and `InvalidArgument`
for a wrong address. It acquires no shared guard and preserves the whole borrow
state, including any existing shared guards. `Rent111ReadReady` requires a
current account and eight logical bytes only when neither earlier error applies.
`rent111FromAccount_read` uses those conditions to prove the exact error branch
or a complete eight-byte decode from that cell. The source-facing contract
includes this result. The unchanged raw function still gives a mathematical
zero on empty data; that fallback is excluded by the contract. Short accounts
remain admitted for the earlier borrow and address errors. The precondition
does not impose unrelated whole-pool validity or integer bounds. Address,
physical storage, lifetime, legal access and the little-endian target remain
source-binding obligations. The `read_unaligned::<u64>` load needs no
eight-byte-aligned pointer.

Solana Rent 3.0.0 retains its rate, binary64 threshold and burn percentage. Its
minimum balance performs these operations in order:

1. Add 128 and the 64-bit data length using the chosen integer profile.
2. Multiply by the rate using that profile.
3. Round that integer to binary64.
4. Multiply by the threshold with a second binary64 rounding.
5. Apply the saturating binary64-to-u64 conversion of Rust.

The burn percentage does not enter the calculation. Arbitrary threshold bits
are retained, including negative values, signed zeros, infinities and NaNs.
The fixed rent parameters of the canonical runtime do not replace this function.

`Solanalib.Specs.Core.Float64` defines these floating operations using integers
and bit fields. A finite decoded value has a sign, an integer significand and a
power-of-two exponent. Rounding chooses the nearest representable value, with
ties to even and gradual underflow down to `2^-1074`; overflow yields signed
infinity. Conversion to u64 truncates nonnegative finite values and saturates at
`2^64 - 1`; negative values and NaNs yield zero. Arithmetic NaN payloads are
collapsed to one representative because the final integer cast cannot observe
their payload or sign. This helper is scoped to that observation, not to APIs
that inspect the raw bits of an arithmetic NaN.

No host floating instruction or rational approximation computes the model.
Its target interpretation requires ordinary binary64 round-to-nearest,
ties-to-even arithmetic without flushing subnormals or fusing the separate
conversion and multiplication. A proof about a compiler, software-float helper
or hardware implementation remains outside the mathematical layer. Kernel
controls cover both tie directions near `2^53`, conversion of `u64::MAX`,
subnormal ties, overflow, negative zero, NaNs, infinities and cases where the
separate conversion rounding affects the final integer.

Ordinary source anchors:

| Package | Immutable source | Anchors |
| --- | --- | --- |
| Pinocchio 0.10.2 | [rent.rs](https://github.com/anza-xyz/pinocchio/blob/5697fdd59d201466a23d67d0bceb284c5e6d9e79/sdk/src/sysvars/rent.rs#L102) | Representation 102; ordered integer/floating/BPF branches 230; checked wrapper 281 |
| Pinocchio 0.11.1 | [rent.rs](https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/sysvars/rent.rs#L43) | Representation and size assertions 43; account reader 59; address check 82; unaligned load 113; checked arithmetic 183 |
| Solana Rent 3.0.0 | [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/7208ca11e3c29a8847bb80b08635c6710041e639/rent/src/lib.rs#L32) | Representation 32; default 72; floating calculation 93 |

These models have closed reference and satisfiability witnesses. Outcome
references additionally have closed executions. None of those witnesses asserts
that a Rust body, account representation or target arithmetic implementation
has been verified.
