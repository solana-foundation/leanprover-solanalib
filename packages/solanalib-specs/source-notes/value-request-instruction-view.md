# InstructionView values and checked CPI requests

The common instruction vocabulary reuses `Solanalib.Runtime.CpiMeta` and
`Solanalib.Runtime.CpiInstruction`. Boolean instruction flags become exactly 0 or 1.
Instruction values retain the ordered metadata list and data bytes. `RefMeta`
retains an address-reference identity and copied signer/writable flags; its
`observe` operation requires the address interpretation at the point of use.
It does not imply that arbitrary callbacks preserve that observation.

InstructionView 1.0.0 models `Seed::from(&[u8])` and `Signer::from(&[Seed])`.
InstructionView 2.1.0 models the recorded slice and array seed constructors,
the signer array constructor, and `InstructionAccount::readonly_signer`.
Conversions retain zero lengths, empty groups, duplicates, embedded zero bytes
and ordering; they do not validate PDA seed limits. `readonly_signer` has
signer flag 1 and writable flag 0. The flag argument order of its constructor differs
from `AccountMeta::new`.

The source-facing CPI contracts now model the ordinary checked wrappers.
The actual unchecked invocation remains opaque at its unit-returning signature.
A normal unchecked completion becomes `Ok(())`; it cannot supply an arbitrary
ordinary SDK error. Any unwind or terminal outcome admitted by the selected
dependency interpretation survives, with its actual unwind state. This is a
mathematical source comparison, not a proof about compiled Rust or the runtime.

## Version-specific local control flow

| Step | InstructionView 1.0.0 signed slice | InstructionView 2.1.0 signed array |
| --- | --- | --- |
| Capacity | Reject more than 128 instruction accounts with `InvalidArgument`, before allocation | Array cardinality at most 64 is a Rust compile-time assertion, justified by the source binding |
| Temporary storage | Allocate an uninitialized boxed array of the instruction-account count | Stack array of the const-generic cardinality |
| Supplied count | Fewer supplied accounts than instruction metas gives `NotEnoughAccountKeys`, after allocation | Same error, before any `AsRef` callback |
| Per-position address | Compare the address of the borrowed account with this meta, else `InvalidArgument` | First actual `AsRef`, then compare its current address, else `InvalidArgument` |
| Per-position borrow | Writable rejects any borrow; readonly rejects an exclusive borrow | Only writable calls `AsRef` again and checks for any borrow |
| Entry construction | Copy scalar fields from this borrowed account and retain its field references | A separate actual `AsRef` supplies the current handle and header for construction |
| Completion | Invoke the initialized prefix, return `Ok(())`, then destroy the box | Invoke the initialized prefix and return `Ok(())` |

Both traversals are positional and stop at the first failure. Duplicate
accounts occupy duplicate entries; they are not deduplicated. Supplied trailing
accounts beyond the instruction metadata length are neither visited nor passed
to unchecked invocation. Signer groups and seed bytes remain exactly ordered.
The unsigned v1 entry delegates with an empty signer list.

Version 2 performs two `AsRef` calls for each readonly position and three for
each writable position. The model supplies the same selected trait operation
to every call, but neither assumes purity nor equates successive returned
handles. Each check uses the state and handle of its own call. An earlier
initialized entry retains its copied fields while later calls run. The borrow checks in both versions only observe the lease state; they acquire no guard.

Version 1 allocates before checking the supplied slice length. Allocation may
have effects or a finite nonreturning exit according to its explicit primitive
dependency. Once a box token exists, scope cleanup uses that token in the modeled
state after a normal result, ordinary error, or unwind. A terminal exit stops
without cleanup. A destructor unwind can replace a pending normal result; a
second unwind uses the explicit terminal policy and actual destructor state.
No allocation exit is relabeled as an invented `ProgramError`.
Temporary descriptor-buffer writes are abstracted: `prepareV1` does not update
`State` for each initialized slot before a later validation error. A source
interpretation of allocation and `Box.drop` must cover every reachable partial
initialization, including early validation errors and unwind. Private scratch
may be projected out of `State` only with that justification. The drop relation
may soundly overapproximate effects depending on the hidden prefix; abstracting
that prefix does not establish that these effects leave state unchanged.
A precise allocator or destructor that observes buffer bytes needs an
additional storage relation, which is not provided here.

## Captured fields and remaining bindings

An initialized descriptor retains the selected account identity for address,
owner, lamports and data references, and copies length, rent epoch and flags at
its construction point. AccountView supplies no rent epoch, so both versions
write zero. The v1 initializer calls Boolean flag getters and normalizes their
observations. The v2 initializer copies the raw signer, writable, executable
and padding bytes. Its current raw-header observation is therefore an explicit
input to the common v2 model, and its descriptor retains those exact bytes.
Flag byte 2 and nonzero copied padding are not silently changed or discarded.

A Rust interpretation still needs the following source bindings:

- The selected const-generic array instantiation satisfies `ACCOUNTS <= 64`.
  `StaticAccounts` retains the structural equality between the array extent
  and its element count. The mathematical relation also retains executions
  outside the source bound; it introduces no corresponding runtime error.
- Every handle accessed denotes the intended live AccountView and legal field
  references, and the current pool/lease observation corresponds to the source
  account and borrow byte. The mathematical total fallback for a missing handle
  is not evidence that an invalid Rust reference is valid.
- The current raw header, Boolean observations, copied lengths and immutable
  instruction/seed observations correspond to the source representation at
  their actual access points. Callbacks must have their selected source trait
  identity and all legal memory and lifetime effects; the generic relation
  itself grants no frame or permission property.
- Initialized descriptors correspond to the actual temporary ABI entries and
  their retained field pointers. Box allocation/drop and stack storage have
  the selected target layout, capacity, ownership and cleanup interpretation.
  This model does not prove a standard-library allocator or choose an
  undocumented allocation strategy.
- The opaque unchecked operation is bound to the exact prepared prefix,
  instruction and signers and to the outcomes of its selected target. No success,
  rollback, runtime authorization, pointer translation or account preservation
  is inferred merely from the local wrapper returning normally.

The common v2 machinery is in `CpiRequestChecked*`; the v1 boxed-slice extension
is in `CpiRequestCheckedSlice*`. The indexed families retain explicit state,
trait, storage and invocation interpretations. Their preconditions impose no
success assumption. Closed nonempty executions traverse the actual modeled
checks; the v1 witnesses distinguish allocation, invocation and drop effects.
The controls additionally distinguish the readonly borrow handling of the revisions,
error order, repeated conversions, copied fields, duplicate prefixes, ignored
trailing inputs, and callback/destructor unwind and terminal exits.

## Reviewed source

Only ordinary constructors, checked wrapper bodies and the unchecked invocation
signatures were inspected. Actual unchecked invocation/syscall bodies are
outside the reviewed scope. Full-file hashes identify immutable source
files; they do not expand that reviewed body scope.

| Version | Source | Reviewed anchors |
| --- | --- | --- |
| 1.0.0 | [instruction-view/src/cpi.rs](https://github.com/anza-xyz/solana-sdk/blob/c4d0dabc8cbf086bd0b3027f65b158b946c0b5e7/instruction-view/src/cpi.rs#L71) | CPI entry conversion 71–92; Seed slice 117; Signer slice 165; unsigned wrapper 282–287; signed slice 440–458; checked inner 478–537 |
| 2.1.0 | [instruction-view/src/cpi.rs](https://github.com/anza-xyz/solana-sdk/blob/d8e311b30785b398f689528443ffd50db2a262f0/instruction-view/src/cpi.rs#L118) | CPI entry initialization 118–144; Seed slice 169; seed array 179; signer array 229; checked array 372–400; checked inner 545–592 |
| 2.1.0 | [instruction-view/src/lib.rs](https://github.com/anza-xyz/solana-sdk/blob/d8e311b30785b398f689528443ffd50db2a262f0/instruction-view/src/lib.rs#L80) | Readonly signer constructor 80 |

The selected dependency profile for InstructionView 1.0.0 uses AccountView
1.0.0 and Address 2.6.1; the 2.1.0 profile uses AccountView 2.0.0 and Address
2.6.0. These are explicit source profiles, not claims that every resolution of
the upstream dependency ranges is equivalent. System 0.6.0, associated-token
account 0.4.0 and Pinocchio Token-2022 0.3.1 request models compose through the
v2 fixed-array checked helper with their source-specific cardinalities.
