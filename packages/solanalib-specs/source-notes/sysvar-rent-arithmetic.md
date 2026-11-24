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

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:a0d3ea762a626f56 -->
<a id="review-a0d3ea762a626f56"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Versioned public aggregate of the reviewed mathematical models.

Instantiate the shared mathematical operations for this exact SDK version; keep closed reference, precondition and execution witnesses in the public version namespace.

The reviewed sources retain overhead 128, u64 rate, f64 threshold and ignored burn_percent. minimum_balance adds the u64 length to overhead, multiplies the integer rate, rounds that integer to binary64, multiplies the arbitrary threshold and saturating-casts to u64. is_exempt calls that computation first and compares balance >= the returned minimum; integer failures occur before comparison. Arbitrary public fields, nonfinite values and both overflow profiles remain admitted.
<!-- /registry -->

<!-- registry:review:35e58ab2dc0ec082 -->
<a id="review-35e58ab2dc0ec082"></a>

All 25 real releases through 3.1.0 have the same expression, u64 rate, f64 threshold and overhead 128. The source first casts data_len to u64, adds overhead, multiplies the integer rate, casts that result to f64, multiplies the arbitrary f64 threshold, and casts to u64. Checked overflow and wrapping overflow remain different profiles; arbitrary thresholds, NaN, infinities, signed zero, rounding and saturating casts remain in scope. burn_percent is ignored. All seven 4.x releases rename the rate field, replace the f64 field by little-endian bytes, change Default to rate 6960 and threshold 1.0, route through try_minimum_balance().expect(), reject lengths above 10 MiB and excessive rates, and use integer shortcuts for thresholds 1.0 and 2.0. Other thresholds retain a host floating calculation and panic on the BPF branch. 4.0.0 makes the byte threshold and burn fields private; 4.1.0 and later make them public and deprecated. The new guards already refute complete-contract correspondence, even under a numerical embedding of the new fields. Native 4.0.0 and 4.5.0 counterexamples distinguish those guards from mere representation changes.
<!-- /registry -->

<!-- registry:review:cbe188c592f94753 -->
<a id="review-cbe188c592f94753"></a>

The reviewed sources retain overhead 128, u64 rate, f64 threshold and ignored burn_percent. minimum_balance adds the u64 length to overhead, multiplies the integer rate, rounds that integer to binary64, multiplies the arbitrary threshold and saturating-casts to u64. is_exempt calls that computation first and compares balance >= the returned minimum; integer failures occur before comparison. Arbitrary public fields, nonfinite values and both overflow profiles remain admitted. The declared compatible range assumes preservation of this complete calculation, integer overflow behavior, binary64 rounding and casts, and failure-before-comparison order for all public field values. The 3.0.0 and 3.1.0 references preserve the threshold arithmetic and overflow behavior. Compatibility in 3.x assumes that protocol is unchanged. Version 4.0.0 replaces the public f64 threshold with private bytes and adds size/rate validation plus specialized arithmetic; it is excluded.
<!-- /registry -->
