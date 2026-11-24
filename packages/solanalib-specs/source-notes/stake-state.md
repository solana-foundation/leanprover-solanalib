# Stake state Borsh decoding

This is a mathematical model of one decoder. Its reference and execution
witnesses prove consistency of the stated model, not a Rust implementation,
compiler or memory theorem. The [source registry](../source-map.json) records
the exact model and its source anchors.

| Package | Source | Revision | SHA-256 |
| --- | --- | --- | --- |
| solana-stake-interface 3.1.0 | `interface/src/state.rs` | `3fc55bf917ef1dd4693318844f2bb696eb3485cd` | `10d016f3bb33ecdfa55745025cd5ca32db005f687a5cb25540d71472c77dc1e6` |
| solana-stake-interface 3.1.0 | `interface/src/stake_flags.rs` | `3fc55bf917ef1dd4693318844f2bb696eb3485cd` | `6109865a5be4c9e86ae228884cfd2502bfd3f053b8189a133a06531d301af4f0` |

The repository is `solana-program/stake`. Both hashes were checked against the
pinned GitHub files. The model uses the Borsh 1.6.1 primitive decoders of
`borsh` and the Address decoder of `solana_address`. Its
`Cargo.toml` requires borsh `1.6.0` and solana-pubkey `4.0.0` as caret ranges.
The model assumes that they resolve to borsh 1.6.1 and to a solana-pubkey that
re-exports `solana_address::Address` 2.6.0 as `Pubkey`, as solana-pubkey 4.2.0
does. A client must establish this resolution from its own lockfile; other
resolutions need their own comparison.

## Decoder

`StakeStateV2` has a hand-written decoder. The macro `impl_borsh_stake_state_v2`
at [state.rs:170](https://github.com/solana-program/stake/blob/3fc55bf917ef1dd4693318844f2bb696eb3485cd/interface/src/state.rs#L170)
defines `deserialize_reader` at line 173, and line 217 instantiates the macro
for `borsh`. The decoder reads a `u32` tag, not the one-byte tag of a derived
Borsh enum. Tag 0 gives `Uninitialized` and tag 3 gives `RewardsPool`, with no
further reads. Tag 1 reads `Meta`. Tag 2 reads `Meta`, `Stake` and `StakeFlags`
in this order. Any other tag returns `io::Error::new(InvalidData, "Invalid enum
value")` (line 189) after the four tag bytes have been consumed.

The field types use derived Borsh decoders, which read the fields in declaration
order and stop at the first error:

| Type | Derive line | Fields | Bytes |
| --- | --- | --- | --- |
| `Meta` | state.rs:410 | `rent_exempt_reserve: u64`, `authorized`, `lockup` | 120 |
| `Authorized` | state.rs:327 | `staker`, `withdrawer: Pubkey` | 64 |
| `Lockup` | state.rs:295 | `unix_timestamp: i64`, `epoch: u64`, `custodian: Pubkey` | 48 |
| `Stake` | state.rs:710 | `delegation`, `credits_observed: u64` | 72 |
| `Delegation` | state.rs:470 | `voter_pubkey: Pubkey`, `stake`, `activation_epoch`, `deactivation_epoch: u64`, `warmup_cooldown_rate: f64` | 64 |
| `StakeFlags` | stake_flags.rs:10 | `bits: u8` | 1 |

An encoded `Stake` variant has 197 bytes, and its flag byte is at offset 196.
The source test `stake_flag_member_offset` checks this offset. Stake accounts
have 200 bytes of data; the unchecked caller ignores the trailing bytes.

## Errors and the remaining slice

The decoder is modeled at `R = &[u8]`, the instance reached through the
default `deserialize`. It returns the result together with the remaining slice.

- Truncated input: every primitive read uses `read_exact`, and Borsh maps a
  short read to `InvalidData` "Unexpected length of input". This holds for
  every field, including the 32-byte address arrays.
- Invalid tag: the error is raised after the four tag bytes.
- NaN rate: the Borsh 1.6.1 `f64` decoder reads all eight bytes, then rejects
  every NaN bit pattern with `InvalidData` "For portability reasons we do not
  allow to deserialize NaNs.". The rate ends at offset 188 of the input. A NaN
  rate is reported even when later fields are truncated, because it is read
  first.

The contract `deserialize_reader_contract` states these cases as the relation
`Decodes` over the version-independent wire layout in
`Solanalib.Specs.Core.StakeState`. A success returns the value `s` and the
remainder `r` exactly when the input is `encode s ++ r` and the rate of `s` is
not NaN. Each error case fixes the error value. As in the Borsh contracts, the
remaining slice after an error is unconstrained: the `read_exact` of `std` for
`&[u8]` empties the slice on a short read, while the Borsh `nostd_io` reader
leaves it unchanged. `decodes_iff` shows that `Decodes` is exactly the `DecodeMatches` agreement of Borsh with the reference, so the contract admits the
reference result and no other.

The reference `StakeStateV2.decode` composes the registered models
`borsh.{u8,u32,u64,i64,f64}.deserialize_reader_model` and
`Solanalib.Specs.SolanaAddress.Address.deserialize_reader_model`. It follows the `std`
reader: a truncated read leaves an empty slice, an invalid tag leaves the bytes
after the tag, and a NaN rate leaves the bytes after the rate.
`deserialize_reader_run` is the graph of this function, so it can be executed.
`deserialize_reader_index` supplies it to the Borsh `deserialize` and Solana
Borsh `try_from_slice_unchecked` families.

The test root decodes the upstream live data (an `Initialized` account with
reserve 2282880, 76 trailing bytes) and a 200-byte `Stake` account with distinct
field values. Its controls cover an invalid tag, a big-endian tag, truncation
of the tag and of the flag byte, a NaN rate before and after truncated fields,
an accepted infinite rate, kept reserved flag bits, the flag offset 196 and the rejection of the
contract of a fabricated success or a wrong error.

## Limits

The stake state values keep all stored bits, including reserved flag bits, the
deprecated rent reserve and the raw rate bits. The model does not interpret
them. Readers other than `&[u8]`, Borsh serialization, the bincode path and the
deprecated `StakeState` decoder are not modeled. The derived field decoders
are part of this model; they are not registered as separate APIs.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:790c090ea27f6683 -->
<a id="review-790c090ea27f6683"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Versioned public aggregate of the reviewed mathematical models.

The StakeStateV2 decoder at R = &[u8] reads a u32 little-endian tag; tags 0 and 3 read nothing more, tag 1 reads Meta, tag 2 reads Meta, Stake and StakeFlags, and other tags return InvalidData "Invalid enum value" after the tag. Field decoders follow the derive order. The reference composes the registered borsh 1.6.1 u8/u32/u64/i64/f64 and solana-address 2.6.0 Address deserialize_reader models and is registered as the graph of that function. The contract relation Decodes states success as input = encode value ++ remaining with a non-NaN rate, and fixes the error of truncation, invalid-tag and NaN-rate failures; decodes_iff proves it equal to Borsh DecodeMatches agreement with the reference, so the remaining slice is fixed only on success.
<!-- /registry -->

<!-- registry:review:4124b2b87bde9782 -->
<a id="review-4124b2b87bde9782"></a>

All 18 releases have the same four-byte little-endian tag dispatcher. Tags 0/1/2/3 select Uninitialized, Initialized(Meta), Stake(Meta, Stake, StakeFlags) and RewardsPool, with widths 4/124/197/4. Other tags return InvalidData / Invalid enum value before reading a body; error construction is interpreted under the shared scope boundary. Through 3.1.0 the complete nested field order, integer/address decoding, every flag byte and success remainder match the model. Delegation warmup_cooldown_rate is f64, and NaNs fail with InvalidData / For portability reasons we do not allow to deserialize NaNs. before credits_observed and the trailing flag. Version 4.0.0 replaces this field with _reserved: [u8; 8], so NaN-shaped bytes are accepted and a truncated tail after them returns the short-input error instead. Retained native cases at 4.0.0 and 5.1.1 confirm these functional differences. Accordingly the nine releases through 3.1.0 are compatible and the nine later releases are incompatible, without excluding NaNs from the input domain or adding diagnostic-allocation premises. StakeStateV2 Borsh 1 trait implementation with Borsh/derive 1.6.1 and solana-pubkey 2.4.0. The f64 delegation field is retained.
<!-- /registry -->

<!-- registry:review:7908ca67224fa85f -->
<a id="review-7908ca67224fa85f"></a>

All 18 releases have the same four-byte little-endian tag dispatcher. Tags 0/1/2/3 select Uninitialized, Initialized(Meta), Stake(Meta, Stake, StakeFlags) and RewardsPool, with widths 4/124/197/4. Other tags return InvalidData / Invalid enum value before reading a body; error construction is interpreted under the shared scope boundary. Through 3.1.0 the complete nested field order, integer/address decoding, every flag byte and success remainder match the model. Delegation warmup_cooldown_rate is f64, and NaNs fail with InvalidData / For portability reasons we do not allow to deserialize NaNs. before credits_observed and the trailing flag. Version 4.0.0 replaces this field with _reserved: [u8; 8], so NaN-shaped bytes are accepted and a truncated tail after them returns the short-input error instead. Retained native cases at 4.0.0 and 5.1.1 confirm these functional differences. Accordingly the nine releases through 3.1.0 are compatible and the nine later releases are incompatible, without excluding NaNs from the input domain or adding diagnostic-allocation premises. StakeStateV2 Borsh 1 trait implementation with Borsh/derive 1.6.1 and solana-pubkey 3.0.0; its dependency chain resolves the same 32-byte address representation. The f64 delegation field is retained.
<!-- /registry -->

<!-- registry:review:9f0a4f30b4a38226 -->
<a id="review-9f0a4f30b4a38226"></a>

All 18 releases have the same four-byte little-endian tag dispatcher. Tags 0/1/2/3 select Uninitialized, Initialized(Meta), Stake(Meta, Stake, StakeFlags) and RewardsPool, with widths 4/124/197/4. Other tags return InvalidData / Invalid enum value before reading a body; error construction is interpreted under the shared scope boundary. Through 3.1.0 the complete nested field order, integer/address decoding, every flag byte and success remainder match the model. Delegation warmup_cooldown_rate is f64, and NaNs fail with InvalidData / For portability reasons we do not allow to deserialize NaNs. before credits_observed and the trailing flag. Version 4.0.0 replaces this field with _reserved: [u8; 8], so NaN-shaped bytes are accepted and a truncated tail after them returns the short-input error instead. Retained native cases at 4.0.0 and 5.1.1 confirm these functional differences. Accordingly the nine releases through 3.1.0 are compatible and the nine later releases are incompatible, without excluding NaNs from the input domain or adding diagnostic-allocation premises. StakeStateV2 Borsh 1 trait implementation with Borsh/derive 1.6.1 and solana-pubkey 4.4.0 / solana-address 2.9.0. The f64 delegation field is retained.
<!-- /registry -->
