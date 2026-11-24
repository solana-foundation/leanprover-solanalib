# AccountInfo 3.1.1 mathematical models

The reviewed source is `solana-account-info` 3.1.1, revision
`9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23`,
[`account-info/src/lib.rs`](https://github.com/anza-xyz/solana-sdk/blob/9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23/account-info/src/lib.rs),
SHA-256 `f7aeb75e2f891502f8c3dd06650e86d57539528ad92f5e67372640ded0a194b7`.
The [source registry](../source-map.json) records the exact Rust names and
source anchors. Models cover `lamports`, `data_len`, `try_borrow_data`,
`try_borrow_mut_data` and derived `clone`, with drop behavior used in composition.

The shared Borrow model represents two distinct typed cells: UInt64 lamports
and data bytes. Aliases preserve these identities; stable guard IDs and
generations prevent using a released or consumed token again. The shared count
limit is the selected RefCell bound `2^(wordBits - 1) - 1`, not the bound of 254 for AccountView. The target profile is explicit. Logical IDs are not source addresses,
provenance or ownership permissions.

Getters perform temporary shared borrows and release them after observing
current contents. A conflict panics, with unwind or terminal abort selected by
the profile. Checked data borrowing returns a live guard or the exact SDK
AccountBorrowFailed error. Mutable borrowing has no writable-metadata check.

The checked-borrow contracts require only a protocol-valid guard world and a
present data cell. Those premises prove final protocol validity and current
typed data through every successfully returned guard. Getter admission requires
only a present, typed selected cell; `observe_reference_exists` uses it to rule
out a malformed-model path and provide a finite value or borrow panic. Neither
operation requires bounds on the target width or data length, or validity of
the unused cell, for these mathematical results. The broader `AccountInfo.Valid`
predicate remains available to source interpretations and other composed models.
Rust field widths, the selected RefCell policy, distinct source cells and
physical reference validity still require their own binding.

`Value.owner` is an entry observation; `OwnerRef` identifies the pointed owner
and `OwnerAt Aux` reads its current contents. Keeping or cloning an AccountInfo
does not imply immutable owner contents. Constructor and codec controls change
that owner between reads.

The primary clone family calls lamports Rc clone then data Rc clone in actual
state order. Success returns the same aliases and owner reference; overflow
may terminate. A corresponding drop binding must preserve the same field order. The selected
`Rc<RefCell<&mut u64>, Global>` and `Rc<RefCell<&mut [u8]>, Global>` have no user
destructor or allocator-clone callback that can unwind. This source capability
is explicit, while terminal exits remain possible. The registry pins supporting
Rc excerpts; no Rc implementation correctness is assumed or proved here.

`clone_observation_contract` forgets the Rc lifecycle and is supporting only.
Its identity operation has an unconditional mathematical precondition.
Concrete event traces witness dependency scheduling, not real allocation or
reference counts. Source binding must supply actual Rc operations and relate
logical live resources to source owners. Closed witnesses and model clients
cover conflicts, saturation, independent cells, mutation/release, consumed
guards, panic and exact Rc sequencing. Rust representation, dependency and body
proofs remain open.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:0095640bce0a850b -->
<a id="review-0095640bce0a850b"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The AccountInfo 3.1.1, Anchor 1.0.2 and Anchor SPL 1.0.2 functions compose identified borrows, current owner reads, explicit trait callbacks, owned resources and source-ordered cleanup. AccountInfo borrow/getter conditions support their actual typed-current and progress conclusions. Constructor admission covers only reached initialization reads, diagnostic Error resources and guarded decoder/discriminator continuations. Loading and amount admit earlier checked errors but require current data after successful acquisition; reached owned loading factories retain their held tokens. Their continuation results preserve actual finite exits without assuming dependency termination. Owned-error families retain their three boxing or four comparison capabilities; comparisons additionally require reached assignment availability, and with_values protects resources on continuing unwind/destructor paths through CallReady. Pure error observation facets retain their stated omissions. Context uses actual empty-provider current/fresh facts. Primary transfer requires current instruction vectors on each successful builder return; invocation remains opaque. Pinned edition-2021 cleanup destroys instruction metadata and bytes, the tail-expression account array, then the remaining vector. Conditional destructor non-unwind claims and concrete resource/reference/target interpretations remain explicit source bindings.

The selected AccountInfo functions reuse the identified Borrow/AccountInfo/Rc world. Reflexive AsRef preserves the existing source reference; lamports acquisition returns typed current guards; scalar/boolean getters preserve temporary lifecycle and errors. Owner assignment updates shared owner storage. Resize/realloc preserve original-length accounting, complete backing bytes, shared serialized/local lengths, source error order and guard cleanup, with termination at a reached zeroing syscall. Generic preservation/progress and exact output-length lemmas and closed reference witnesses are mathematical evidence under their stated premises. Exact versions and defining Rust identities, including legacy solana_program paths, are reviewed individually.
<!-- /registry -->

<!-- registry:review:bb9ea77ce7135a7a -->
<a id="review-bb9ea77ce7135a7a"></a>

Every API-bearing archive derives Clone on a struct with lamports:Rc<RefCell<&mut u64>> preceding data:Rc<RefCell<&mut [u8]>>. Actual pinned-compiler expansions at 0.0.2/3.0.0/3.1.1 confirm that order. The reached Global Rc clone increments the relevant strong count before the second dependency call, never clones the payload, and aborts on count wrap. The full existing indexed family retains dependency state, terminal exits and sequencing; no unconditional count/allocation guarantee is added to that family. Successful metadata, aliases and owner reference are unchanged across the rent/address/import transitions. Release 0.0.1 only defines a placeholder add function, so absence is distinct from incompatible behavior. No published release is skipped.
<!-- /registry -->

<!-- registry:review:15a96daa773ad9e9 -->
<a id="review-15a96daa773ad9e9"></a>

The underlying operation is the same derived Clone as the primary family. On its normal completion, all metadata, both cell aliases and the owner reference are preserved without observing the RefCell contents. The existing supporting observation intentionally forgets Rc lifecycle/terminal behavior and stays partial; it is not substituted for the primary clone family. Its unconditional mathematical premise is retained. Release 0.0.1 only defines a placeholder add function, so absence is distinct from incompatible behavior. No published release is skipped.
<!-- /registry -->

<!-- registry:review:283fcf0958e8ed38 -->
<a id="review-283fcf0958e8ed38"></a>

All 27 API-bearing releases have the same byte-identical method body self.data.borrow().len(). With the reached RefCell policy this temporarily acquires a shared lease, reads the current slice length, releases the temporary lease, or invokes the selected panic behavior on conflict/shared saturation. The contract retains selected-cell ObservationReady only; it does not require the lamports cell or an unused whole-account validity premise. Release 0.0.1 only defines a placeholder add function, so absence is distinct from incompatible behavior. No published release is skipped.
<!-- /registry -->

<!-- registry:review:e47b0588f96ca5a9 -->
<a id="review-e47b0588f96ca5a9"></a>

All 27 API-bearing releases have the same byte-identical body **self.lamports.borrow(). The selected live lamports cell supplies the current u64, a successful temporary shared lease is released, and conflict/shared saturation panics under the supplied strategy. The contract retains selected-cell ObservationReady and does not require validity of the unrelated data cell. Release 0.0.1 only defines a placeholder add function, so absence is distinct from incompatible behavior. No published release is skipped.
<!-- /registry -->

<!-- registry:review:38c70df7e203c822 -->
<a id="review-38c70df7e203c822"></a>

All 27 API-bearing releases have the same byte-identical body self.data.try_borrow().map_err(|_| ProgramError::AccountBorrowFailed). It returns a live shared Ref, not a snapshot; shared count increments subject to isize::MAX and guards retain the lease until drop. Both conflict and saturation map to the exact unit SDK error and preserve cell contents/lease state on failure. The reached unit variant exists in every allowed reviewed ProgramError release. Explicit lifetime spelling changes at 3.0.0 are equivalent. The existing DataBorrowReady premise and typed-current-data/protocol-validity postcondition are retained. Release 0.0.1 only defines a placeholder add function, so absence is distinct from incompatible behavior. No published release is skipped.
<!-- /registry -->

<!-- registry:review:8ac3802dd85dbecf -->
<a id="review-8ac3802dd85dbecf"></a>

All 27 API-bearing releases have the same byte-identical body self.data.try_borrow_mut().map_err(|_| ProgramError::AccountBorrowFailed). Only a free data cell admits a live exclusive RefMut; either shared or exclusive conflict maps to the exact unit SDK error, without inspecting is_writable or the lamports cell. Explicit lifetime spelling changes at 3.0.0 are equivalent. Existing DataBorrowReady and the current typed data/protocol-validity postcondition are retained. Release 0.0.1 only defines a placeholder add function, so absence is distinct from incompatible behavior. No published release is skipped.
<!-- /registry -->

<!-- registry:review:632068f1631cb579 -->
<a id="review-632068f1631cb579"></a>

Reference: solana-account-info 2.3.0. The declared [2.3.0, 3.0.0) range assumes preservation of the volatile current-owner update through self.owner, with new_owner.to_bytes copying all 32 bytes. The same writable storage changes through every alias while all borrow cells, buffers and unrelated state remain unchanged. This adds no signer, writability or runtime reassignment-authorization check. The actual key conversion and legal shared-reference write are interpreted by the existing source and OwnerRef conditions.
<!-- /registry -->

<!-- registry:review:712c5ddd232586b7 -->
<a id="review-712c5ddd232586b7"></a>

The declared compatible range assumes the volatile write of all 32 owner bytes through the actual owner reference, visible through aliases and with all other AccountInfo state retained.
<!-- /registry -->

<!-- registry:review:03394c3755d8cafe -->
<a id="review-03394c3755d8cafe"></a>

Reference: solana-account-info 2.3.0. The declared [2.3.0, 3.0.0) range assumes the same order: exclusive data borrow; equal-length return before original-header access; saturating growth from the immutable original length against 10,240 bytes; serialized-length write before slice replacement; optional nonempty-tail zeroing; guard release. Borrow conflicts and InvalidRealloc retain their error and cleanup behavior. Shrinking preserves spare bytes, and zero_init = false may expose them again. The Solana memory provider below preserves the reached zeroing operation, including its terminal exit after the length updates.
<!-- /registry -->

<!-- registry:review:b99f0323bc524a07 -->
<a id="review-b99f0323bc524a07"></a>

Reference: solana-account-info 2.3.0. The declared [2.3.0, 3.0.0) range assumes that resize(new_len) remains realloc(new_len, true), preserving the borrow-error/equal-length/original-header/growth-check order and serialized-length-before-slice update. Shrink retains backing bytes; successful regrowth zeroes only the newly exposed tail. Temporary-guard cleanup and a reached zeroing terminal exit remain unchanged. The explicit-zero-flag realloc contract stays separate.
<!-- /registry -->

<!-- registry:review:46070ae9c26c125b -->
<a id="review-46070ae9c26c125b"></a>

The declared compatible range assumes the checked exclusive data borrow, original-data-length growth limit and source-order length writes, followed by zeroing only newly exposed bytes through the selected memory provider. Alias-visible partial effects and actual guard cleanup survive errors or unwind; the current metadata field remains uninterpreted.
<!-- /registry -->

<!-- registry:review:c99bb6559ee45343 -->
<a id="review-c99bb6559ee45343"></a>

Reference: solana-account-info 2.3.0. The declared [2.3.0, 3.0.0) range assumes preservation of shared acquisition of the actual lamports Rc/RefCell, exact AccountBorrowFailed mapping and the live guard to its current typed value. Aliases, generations, finite shared-counter policy and guard lifetime remain in the common borrow world. No data-cell, signer or writability condition is introduced. This guard-returning operation stays distinct from a temporary observation.
<!-- /registry -->

<!-- registry:review:6bb99c027b125c61 -->
<a id="review-6bb99c027b125c61"></a>

Reference: solana-account-info 2.3.0. The declared [2.3.0, 3.0.0) range assumes preservation of self.try_borrow_data()?.len(): temporarily acquire the actual shared data guard, return AccountBorrowFailed on conflict, read the current length and release the successful temporary. The used RefCell policy, typed projection, aliases, counters and cleanup remain exact. No persistent guard, saved length or unchecked-getter panic behavior is substituted.
<!-- /registry -->

<!-- registry:review:ca18053f6a577cb8 -->
<a id="review-ca18053f6a577cb8"></a>

The declared compatible range assumes the actual shared RefCell borrow of the current data slice, its usize length, AccountBorrowFailed on conflict and release of the acquired guard.
<!-- /registry -->

<!-- registry:review:3359342fd56175b1 -->
<a id="review-3359342fd56175b1"></a>

The 2.3.0 reference returns the existing shared AccountInfo reference, with unchanged state and no Rc clone or new guard. Compatibility within the declared 2.x range assumes this identity operation remains unchanged. Actual record layout, lifetimes and reference permission remain source-binding obligations.
<!-- /registry -->

<!-- registry:review:68f6269bf0616f6a -->
<a id="review-68f6269bf0616f6a"></a>

The declared compatible range assumes return of the same shared AccountInfo object with its existing lifetime, aliases and complete state, without allocation or Rc cloning.
<!-- /registry -->

<!-- registry:review:e03745a506dd7d51 -->
<a id="review-e03745a506dd7d51"></a>

The inspected 2.1.0/2.2.1/2.3.0 data_is_empty definitions and legacy carrier agree. The declared 2.x range assumes temporary shared acquisition, current data emptiness and release, preserving conflict/saturation panic behavior and receiver state. The source reference and concrete layout remain separately bound; later metadata carriers are not silently substituted.
<!-- /registry -->

<!-- registry:review:ea7a106374a47293 -->
<a id="review-ea7a106374a47293"></a>

The declared compatible range assumes the unchecked shared data borrow and current-slice emptiness test, including the reached RefCell panic policy and guard lifetime; it is not replaced by a checked Result-returning borrow.
<!-- /registry -->

<!-- registry:review:3a43ac3d4ba144f8 -->
<a id="review-3a43ac3d4ba144f8"></a>

The declared compatible range assumes the checked exclusive lamports guard over the current cell, exact AccountBorrowFailed result on conflict and alias-visible typed value, preserving the actual source representation.
<!-- /registry -->
