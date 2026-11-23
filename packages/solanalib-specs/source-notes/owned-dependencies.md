# Owned dependency and cleanup models

`Solanalib.Specs.Core.Owned` supplies the common mathematical vocabulary used by
instruction builders, token helpers and account wrappers when they call an
owned-value dependency. It does not implement `Vec`, an allocator, a destructor,
or a Rust capability model. The caller supplies each dependency relation and
sequences its actual finite return, unwind or terminal outcome.

`VectorOps` keeps a stable logical vector identity distinct from both its
machine address and its contents. `current state identity` reads the supplied
current state. The optional `Laws` express primitive partial correctness:
fresh construction, exact ordered values on a normal update, a live token after
an unwinding update, and retirement after a normally returning or unwinding drop.
They permit contents to change before an unwind. They do not imply progress,
determinism, exclusivity, separation, framing of another resource, validity of a
source pointer, or absence of identity reuse after retirement. These obligations
belong to a concrete dependency interpretation. A token alone grants no access.

`OwnedCleanup` runs retained destructors in their supplied source order. Every
next operation receives the actual state of the preceding operation. A first unwind
replaces a pending ordinary return. A second unwind can only use the explicitly
supplied terminal policy, with the actual state and both reasons. A terminal
outcome performs no later cleanup. `scope` cleans ordinary errors as well as
other ordinary returns. `protect` cleans only unwinds; its ordinary returns,
including `Result::Err`, move through unchanged. Callers that must clean an
ordinary error branch use `scope` or describe that branch explicitly.

The drop provider receives the current state and retained identity. Neither
`dropAction` nor the primitive laws derive element-by-element destructor
behavior, nested ownership transfer, or cleanup of inputs consumed by a failing
push. A vector containing guards or other owned values needs those additional
provider guarantees. Likewise, the exact `extend_current` law applies to a
dependency that preserves the supplied logical elements; it does not describe
an arbitrary effectful `Clone` callback without a separate interpretation.

`OwnedVector` gives a finite reference interpretation whose ledger never reuses
a slot. A new vector appends its values, a live update changes that same slot,
and a drop leaves a tombstone. Missing and dead identities admit no reference
operation. The proof `vectorReference_laws` discharges every primitive law for
this interpretation. It is a mathematical consistency witness, not a claim that
Rust allocation always succeeds or that the ledger is a concrete Rust layout.

`OwnedFocus` places such a dependency inside a larger mathematical state through
a lawful projection. It retains the exact inner return or unwind state and
preserves the surrounding state as specified by `set`. `OwnedFocusFacts` proves
exit inversion and preservation of every vector law. A focus is not a source
memory lens, alias proof or target-address correspondence.

`OwnedArray` records indexed expression calls, construction work and ordered
cleanup. A surviving unwind reports the completed prefix and failure site, so
an enclosing source scope can identify arguments not yet moved into a literal.
Its `CurrentLaw` relates completion to the actual current vector contents;
`construction_reference` derives the returned prefix, count and order.
The `initialInfos_success_current` of the Token helper applies this law to its
actual indexed AccountInfo clone calls and proves the exact four-account
result in source order, including duplicate identities.
These results leave the allocation schedule and the concrete ownership and
callback-frame bindings to the supplied dependencies.

The closed controls in `SolanalibTest.Specs.Core.Owned` include fresh construction
with preexisting resources, preservation of a separate slot, stale drop
rejection, an actual partial extension followed by a contents-sensitive cleanup,
order-dependent destructors, first and second unwinds, terminal short-circuiting,
ordinary errors, and a focused partial unwind. A separate failure-injection
provider satisfies the complete vector laws while changing its contents before
unwinding. This checks that those unwind obligations are usable beyond the
normal-only ledger reference.

The [package validation commands](../README.md#build-and-audit) build these
modules and audit every declaration. Source body correctness and the concrete
allocator, destructor, capability and representation bindings remain separate work.
