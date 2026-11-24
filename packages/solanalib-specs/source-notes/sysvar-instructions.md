# Instructions sysvar models

The Pinocchio 0.11.1 constructor first reads the Instructions sysvar address,
then acquires a shared account guard. A wrong address yields `UnsupportedSysvar`
before any borrow conflict; a matching address preserves `AccountBorrowFailed`.
It does not validate the serialized instruction buffer. Its source admission
requires an actual selected cell, and backing/signed-length bounds only when
the matching-key borrow actually succeeds and forms a slice. Valid short and
empty slices remain admitted. `constructor_checked` preserves every raw result;
`constructor_success_readable` proves that a successful result has the live
current read and complete captured length. Neither result supplies decoder
serialization bounds.

The Ref-backed receiver retains the acquired guard in instruction, program-id
and data references. `Instructions.Ready` resolves that actual live shared slot,
checks its captured range against the current backing bytes, and requires a
slice length below `2^63`. It does not require unrelated lamport, owner or
other-account conditions. Mapped guards retain their actual allocation offset.
The native table check includes this offset: an odd mapped view is rejected even
though the relative table position is even. This specialization binds the
underlying AccountView data allocation to a nonnull, valid, two-aligned source
base. Physical placement, source permissions, coherent guard interpretation and
lifetimes are representation obligations; the abstract pool contains no numeric
base address or Rust provenance tags.

Decoder admission now rules out the invalid reached loads of the source. The checked
observers perform complete reads of the current bytes and form only bounded
references. Their success is included in the source-facing postconditions.
`checkedWord_reads` derives the actual two-byte read, decoded value below 65536,
and access alignment. The program-id and data posts also give the complete
32-byte or decoded-length current payload. The old raw observers are unchanged:
they still have their mathematical empty/truncated fallbacks outside admission.
Those raw values are not executions of the source-function contracts after a
guard is released, a table load is misaligned, or bytes are missing. Check
failure denotes excluded source access; it is not an invented Rust error.

The generic families separately preserve arbitrary `T: Deref<Target = [u8]>`
callbacks. Each call can return a different slice and state, unwind with that
state, or terminate. Their memory interpretation supplies current allocation
bytes, allocation identities and base addresses. The source order is:

| Method | Modeled sequence |
| --- | --- |
| `load_current_index` | Dereference for the first length; dereference again for a pointer; evaluate the subtraction and read two little-endian bytes from the second pointer using the first length, in the second callback state |
| `load_instruction_at` | Dereference and read the count; return `InvalidInstructionData` immediately if out of range; otherwise dereference again and read the native u16 offset table; dereference a third time and add the saved second-state offset to that third pointer |
| `get_program_id` | Read the two-byte account count of the current entry; form a complete 32-byte address reference after the `33 * count` metadata region |
| `get_instruction_data` | Read the current account count and data-length word; form the corresponding complete current-memory byte slice |

`CurrentReady` and `AtReady` quantify every actual returned callback alternative
at each reached prefix. They do not select one convenient readable return from
a nondeterministic provider. Every returned slice must be valid in that current
state. The first count read fits the first returned slice; the table read fits
the second; the footer fits the second slice at the first length. The footer
subtraction and its length comparisons are required only after the second call
returns. Thus a valid empty first slice followed by a second unwind or terminal
exit is admitted without inventing a footer read. An out-of-range lookup needs
no table bytes or third call. `current_checked` and `at_checked` prove that
**every finite raw exit** retains the identical outcome and callback states in
the checked execution. These theorems rule out a lost local continuation under
admission; they do not require downstream callbacks to terminate.

The generic checks establish current byte availability, complete extents,
nonnull/nonwrapping 64-bit addresses, signed pointer offsets, and the alignment
of each access. Forward additions require the same allocation or one-past;
zero addition to a valid dangling empty slice is permitted. The known returned
slice bounds are an explicit sufficient admission discipline, not a complete
characterization of all Rust raw-pointer permissions. `Memory.bytes` must be
related to initialized current allocation storage, and each actual checked
span/addition must also be permitted by the provenance, tag,
aliasing and lifetime of the source pointer. Allocation membership and numeric checks alone do not
prove that permission. The mathematical address map is not an allocator proof.

Successful lookup establishes pointer formation only. It may return one-past
and does not imply that a count, program id or payload is readable there; those
later methods have separate current-state admission. Empty returned data is
permitted only after both preceding scalar reads and the data-pointer addition
succeed. The current-index footer is not checked against the instruction count,
matching the source. Only the native u16 table load requires alignment two and
the selected little-endian target. Count, footer and length loads use `[u8; 2]`
and require alignment one. The source metadata layout is one flags byte plus a
32-byte address; arithmetic uses the selected 64-bit `usize` target.

The maintained controls include a nonempty 78-byte serialization, short-slice
constructor success with decoder rejection, count-only early errors, released
guards, odd mapped/native table addresses, complete versus truncated payloads,
and one-past lookup versus later decode. Generic controls distinguish callback
counts, changed pointers/current bytes, unsafe nondeterministic alternatives,
early unwind/terminal exits, and empty/dangling slice behavior. Closed reference,
satisfiability and execution witnesses retain the exact registered families and
samples with the restored admission and checked posts.

The ordinary source is
[Pinocchio 0.11.1 instructions.rs](https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/sysvars/instructions.rs):
count load at 47, current index at 56, unchecked table/pointer formation at 73,
checked lookup at 88, constructor at 122, program id at 214 and data at 230.
The exact source hash, anchors and Rust symbols remain recorded in the
[source registry](../source-map.json). This is source-reviewed mathematical
modeling, not a Rust execution or compiler correspondence proof or a standard-library proof.
CPI invocation implementations are not involved.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:d756e317a51890b1 -->
<a id="review-d756e317a51890b1"></a>

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Both checked loaders reject an incorrect instructions ID before borrowing data, then acquire a shared Ref and use the current cell. The current-index loader reads exactly the final two little-endian bytes; a short slice panics (checked subtraction or wrapping slice-range panic), and the Ref is released on unwind. The instruction loader reads count, checks index, reads table offset and account count, allocates the meta Vec, reads and pushes flags/key pairs, then reads program key and byte length and allocates data. High flag bits are ignored; every reached bounds error is SanitizeError::IndexOutOfBounds mapped to InvalidArgument. A 32-byte Pubkey conversion cannot produce ValueOutOfBounds after its bounds check. A parse Err drops local metas before releasing the shared Ref; successful Vecs move into Instruction. Terminal exits have no cleanup state.
<!-- /registry -->

<!-- registry:review:65b0fd24d896c644 -->
<a id="review-65b0fd24d896c644"></a>

The declared compatible range assumes ID rejection before shared borrowing, then ordered count/index/offset/account-count reads, metadata allocation and flag/key pushes, program key and data-length reads, and data allocation. Ignore high flag bits; reached bounds errors map IndexOutOfBounds to InvalidArgument. Parse Err drops local metas before releasing the guard; successful vectors move into Instruction and terminal exits supply no cleanup state.
<!-- /registry -->

<!-- registry:review:301b68a7d223a227 -->
<a id="review-301b68a7d223a227"></a>

Both checked loaders reject an incorrect instructions ID before borrowing data, then acquire a shared Ref and use the current cell. The current-index loader reads exactly the final two little-endian bytes; a short slice panics (checked subtraction or wrapping slice-range panic), and the Ref is released on unwind. The instruction loader reads count, checks index, reads table offset and account count, allocates the meta Vec, reads and pushes flags/key pairs, then reads program key and byte length and allocates data. High flag bits are ignored; every reached bounds error is SanitizeError::IndexOutOfBounds mapped to InvalidArgument. A 32-byte Pubkey conversion cannot produce ValueOutOfBounds after its bounds check. A parse Err drops local metas before releasing the shared Ref; successful Vecs move into Instruction. Terminal exits have no cleanup state. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:772927c571d336dc -->
<a id="review-772927c571d336dc"></a>

The declared compatible range assumes instructions-ID rejection before shared borrowing, then little-endian decoding of exactly the final two data bytes. A short slice follows the actual arithmetic/slicing panic path, with shared-guard cleanup on unwind and no fabricated terminal cleanup state.
<!-- /registry -->
