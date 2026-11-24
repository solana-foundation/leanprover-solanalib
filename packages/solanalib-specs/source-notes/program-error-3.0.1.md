# ProgramError 3.0.1 vocabulary

ProgramError.Value records the 26 enum alternatives of solana-program-error
3.0.1, including a UInt32 Custom payload and payload-free BorshIoError. The
reviewed [source](https://github.com/anza-xyz/solana-sdk/blob/7cdfc06b7deb076e3d95e84eb6f23b8dc4f12378/program-error/src/lib.rs)
is revision `7cdfc06b7deb076e3d95e84eb6f23b8dc4f12378`, complete-file SHA-256
`047b9c337af95f1c7a7db4e45fa2f9e567bfcf31e632d3626a1162e9c4347810`.

V3_0_1 describes the source value conversions. Builtin tags occupy the upper
32 bits; AccountBorrowFailed uses tag 12. Custom zero encodes as `2^32`;
other Custom values retain their u32 code. Unrecognized u64 values fall back to
Custom with u32 truncation. Raw zero also converts to Custom zero; a syscall
convention interpreting zero as success is a separate caller policy.

This common vocabulary is not runtime InstructionError. Other SDK and Pinocchio
versions require explicit source comparison before reuse. The module asserts
no enum layout, status-policy equivalence or Rust body correctness. Selected
contracts and their closed witnesses live in versioned SDK roots; this module
supplies value vocabulary and two concrete encoding facts.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:908fb58c44828f09 -->
<a id="review-908fb58c44828f09"></a>

Reference 3.0.1 encodes builtin tags 2 through 26 in the upper word and uses 2^32 for Custom(0); other custom u32 values are unchanged. BorshIoError is payloadless. The declared compatible range assumes preservation of the complete 26-variant domain, this exact conversion table, and the allocation-free, state-preserving operation. Runtime success policy is separate.
<!-- /registry -->

<!-- registry:review:d3a5b1bca026581a -->
<a id="review-d3a5b1bca026581a"></a>

Reference 3.0.1 recognizes complete builtin status words with tags 2 through 26 and the custom-zero sentinel 2^32. Other u64 values are truncated to Custom(error as u32), including raw zero; a nonzero low word prevents a builtin match. The declared compatible range assumes preservation of the complete payloadless-Borsh error domain, this conversion table and the allocation-free, state-preserving operation. Runtime success policy is separate.
<!-- /registry -->
