# System instruction values and local helpers

The common request vocabulary preserves ordered accounts and nested signer
seeds. The System program address is 32 zero bytes, the base58 value
`11111111111111111111111111111111`. Amount and space are mathematical naturals
encoded by the existing u64 little-endian helpers. Their correspondence to Rust
u64 arguments is a source-binding obligation, not a family entry restriction.

| Operation | Metadata flags `(signer, writable)` | Data |
| --- | --- | --- |
| Create account | From `(1, 1)`, to `(1, 1)` | u32 little-endian tag 0, u64 lamports, u64 space, 32 owner bytes |
| Transfer | From `(1, 1)`, to `(0, 1)` | u32 little-endian tag 2, u64 lamports |
| Allocate | Account `(1, 1)` | u32 little-endian tag 8, u64 space |
| Assign | Account `(1, 1)` | u32 little-endian tag 1, 32 owner bytes |

The `solana_system_interface.instruction::{create_account,transfer}`
value contracts remain **instruction value observations**. They describe the returned program address,
metadata and bytes, including duplicate keys with different flags. The source
allocates metadata and serializes the System instruction, selecting bincode or
wincode through features. Allocation, serialization errors and non-returning
behavior are not part of these two models, so they are not full operational
constructor coverage. They neither call nor prove the System program.

The primary source-facing models use
`create_account_operational_contract` and `transfer_operational_contract`.
These closed families model the complete constructor control flow above
explicit allocation, serialization, unwrap-failure and destruction providers.
The value models remain separate observations in the registry and
serve as model dependencies, without weakening or replacing the stated coverage of the operational
families.

The source first constructs `vec![...]` containing the two ordered metadata
values, including separate flags when the keys coincide. The `fromList`
dependency must return an owned metadata resource before serialization starts.
An allocation unwind or terminal exit cannot call the serializer or drop a
resource that was never returned. On allocation success, the model passes the
actual resulting state and handle to the matching Instruction 3.4.0 constructor.
Its serializer receives the tagged System data. Serialization success moves
the exact metadata and byte handles into the returned instruction; a serializer
error follows the non-returning unwrap path. Serialization or unwrap unwinding
drops retained metadata using the current state. Terminal exits skip later
cleanup, and double unwind follows the explicit terminal policy.

The operational argument explicitly chooses bincode or wincode. In the source,
wincode takes precedence when that feature is enabled; bincode is the other
enabled branch. Binding the features of a recorded binary remains a separate
obligation. The mathematical provider trace does not itself prove serialized
bytes or vector framing: those observations require the local primitive vector
laws, codec correctness and resource frames. No allocator success, callback
rollback, complete SDK postcondition, or std implementation proof is assumed.
The source owns partial-construction cleanup inside the allocation/serializer
dependencies, and error formatting/panic cleanup inside the unwrap dependency.

The Pinocchio System 0.6.0 helper models cover `Allocate::invoke_signed`,
`Assign::invoke_signed` and `Transfer::invoke`. Their account and metadata
arrays have exact sizes one, one and two. The selected profile resolves
`pinocchio::cpi::invoke_signed` through Pinocchio 0.11.1 to the InstructionView 2.1.0 checked array entry over AccountView 2.0.0. Unsigned transfer calls its
own signed wrapper with an empty signer slice. Signed helpers retain the full
nested seed tree, and account aliases retain every source position.

The request keys are read from the current shared account pool at wrapper
entry. They cannot be chosen independently from the supplied account handles.
The shared checked model performs the count check and ordered address/borrow
checks, initializes the actual descriptor prefix and only then reaches the
opaque unit-returning invocation. All System positions request writable access,
so any live data lease causes a local `AccountBorrowFailed`. Identity `AsRef`
conversion neither changes the pool nor acquires a new guard. The exact source
array sizes discharge the compile-time limit of 64.

The v2 initializer copies the current raw signer, writable, executable and
padding bytes. The family therefore receives a current raw-header observation
in addition to the account pool; it does not normalize nonzero flags to one or
discard padding. Canonical bytes are a choice of the closed sample only.

A checked error is returned unchanged, in the checking state. Normal opaque
completion returns `Ok(())` with its actual state; the Unit signature cannot
inject a new ordinary SDK error. Opaque unwind and terminal exits retain their
actual effects. These wrappers own only fixed stack arrays and borrowed
references, so they add no vector or account-guard cleanup callback. No funding,
allocation, owner change, authorization, rollback or callee-success property is
supplied by these contracts.

The local builder source slices stop at their checked invocation calls. The
checked-entry definitions and their source review are shared with the
[InstructionView model](value-request-instruction-view.md); unchecked invocation
bodies and invoked programs remain opaque. Legal live handles, concrete
`AsRef` identity, source storage/layout and local byte initialization remain
implementation-binding obligations. In particular, the source binding must
relate the supplied raw bytes to the Boolean getters of the pool at each legal current
handle. The mathematical family witnesses execute
nonempty checked paths; they are not Rust execution proofs.

| Version | Source | Anchors |
| --- | --- | --- |
| System interface 3.2.0 | [system-interface/src/instruction.rs](https://github.com/anza-xyz/solana-sdk/blob/c36b228d023aa6c1869565768b225b685d7dc7c1/system-interface/src/instruction.rs#L487) | Serialization helper alternatives 305/315; create account 487; transfer 902 |
| System interface 3.2.0 | [system-interface/src/lib.rs](https://github.com/anza-xyz/solana-sdk/blob/c36b228d023aa6c1869565768b225b685d7dc7c1/system-interface/src/lib.rs#L34) | System program ID 34 |
| Pinocchio System 0.6.0 | [programs/system/src/instructions/allocate.rs](https://github.com/anza-xyz/pinocchio/blob/ef16a3a3e134c44d1a5fcd49cc35d04246006bf4/programs/system/src/instructions/allocate.rs#L26) | Local builder 26; invocation stop 44 |
| Pinocchio System 0.6.0 | [programs/system/src/instructions/assign.rs](https://github.com/anza-xyz/pinocchio/blob/ef16a3a3e134c44d1a5fcd49cc35d04246006bf4/programs/system/src/instructions/assign.rs#L26) | Local builder 26; invocation stop 44 |
| Pinocchio System 0.6.0 | [programs/system/src/instructions/transfer.rs](https://github.com/anza-xyz/pinocchio/blob/ef16a3a3e134c44d1a5fcd49cc35d04246006bf4/programs/system/src/instructions/transfer.rs#L25) | Unsigned wrapper 25; local signed preparation 30; invocation stop 50 |

Tests check exact little-endian value observations, unsigned calls, aliases,
metadata flags and normal/terminal callback effects. Concrete successful
AccountView acquisitions supply live-lease rejection controls for allocate,
assign and the second position of the transfer, with an impossible invocation provider.
Operational System-interface constructor controls also check
allocation-before-serialization order, both serializer choices, fresh handles,
allocation failures and cleanup that retires only newly owned metadata.
Source/archive identity and these mathematical facts remain separate from
Rust implementation correctness.
