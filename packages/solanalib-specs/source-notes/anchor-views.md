# Anchor wrapper references and ownership

The [source registry](../source-map/libraries.json) binds the following
methods to the shared view families. The inherited view profiles use inspected Anchor Lang
references 0.32.1, 0.32.2 and 0.32.3 and declare compatible range
`[0.32.1, 0.33.0)` under the recorded operation and provider assumptions.
The complete method files and relevant manifest requirements agree across
those references. Exact source anchors, nominal providers and feature
conditions remain recorded; the exact selected source identities and native fixture
below retain their 0.32.1 specialization.

The selected 0.32.1 and 1.1.2 source revisions are respectively
`1ebbe58158d089a2a40b5e35ebead5a10db9090d` and
`24035e2b0035c87e321acc1c05f97793829a87f1`. The published 1.1.2 package
records `otter-sec/anchor`. Its selected methods retain exact source,
nominal provider and feature profiles. The 1.1.2 view profiles assume
the recorded references, key bytes and debug branch through `[1.1.2, 1.2.1)`,
before the new Solana provider cohorts. A shared family name alone adds
no method or concrete source binding.

The 1.0.2 methods retain revision
`1314a6b83b16e6a31947b372d57988fd0e81559c`, published by
`solana-foundation/anchor`, and their own nominal-provider profiles.
Their 1.0 alternatives leave both existing ranges intact.

The selected 0.29.0 methods retain revision
`fc9fd6d24b9be84abb2f40e47ed3faf7b11864ae` and their separate
`[0.29.0, 0.30.0)` assumptions. Nominal providers, the selected debug branch,
method anchors and feature gates remain explicit.

The selected 0.27.0 methods retain revision
`d456168d82e2725eaefd2306b516ee201e990820` and their separate
`[0.27.0, 0.28.0)` profiles. The owned AccountInfo field, nominal
providers and selected debug branch remain explicit for each operation.

The 0.27.0 subset is:

| Receiver | Registered methods |
| --- | --- |
| `Account<T>` | AccountInfo `AsRef::as_ref`, `DerefMut::deref_mut`, `Key::key`, `set_inner` |
| `Signer`, `UncheckedAccount` | AccountInfo `AsRef::as_ref`, `Deref::deref` |
| `SystemAccount` | `Deref::deref`, `Key::key` |
| `UncheckedAccount` | `Key::key` |
| `Program<T>`, `Sysvar<T>` | `Deref::deref` |
| `Pubkey` | Anchor `Key::key` |

The 0.29.0 subset is:

| Receiver | Registered methods |
| --- | --- |
| `Account<T>` | AccountInfo `AsRef::as_ref`, `DerefMut::deref_mut`, `Key::key`, `Clone::clone`, `into_inner` |
| `InterfaceAccount<T>` | AccountInfo `AsRef::as_ref`, `DerefMut::deref_mut`, `Key::key` |
| `Program<T>` | `Deref::deref` |
| `Signer` | AccountInfo `AsRef::as_ref`, `Deref::deref` |
| `Pubkey` | Anchor `Key::key` |

The 0.32.1 subset is:

| Receiver | Registered methods |
| --- | --- |
| `Account<T>` | AccountInfo `AsRef::as_ref`, `DerefMut::deref_mut`, `Key::key`, `Clone::clone` |
| `InterfaceAccount<T>` | AccountInfo `AsRef::as_ref`, `Key::key`, `Clone::clone` |
| `Program<T>` | `Deref::deref`, `Clone::clone` |
| `Signer` | AccountInfo `AsRef::as_ref`, `Deref::deref`, `Clone::clone` |
| `UncheckedAccount` | AccountInfo `AsRef::as_ref`, `Deref::deref`, `Key::key`, `Clone::clone` |
| `Pubkey` | Anchor `Key::key` |
| `Lamports` | Provided `get_lamports` |

`Lamports::get_lamports` was inspected at Anchor Lang 0.32.0 through
0.32.3 and declares `0.32.0 ≤ v < 0.33.0`. It retains the actual `AsRef`
provider, live receiver loan, current lamports cell, temporary shared borrow
and panic behavior. The native Signer specialization and exact source binding
remain at 0.32.1; generic Holder fixtures do not widen that binding.

The 1.0.2 subset is:

| Receiver | Registered methods |
| --- | --- |
| `Account<T>`, `InterfaceAccount<T>` | AccountInfo `AsRef::as_ref`, `Key::key` |
| `Program<T>` | `Deref::deref` |
| `Signer` | AccountInfo `AsRef::as_ref`, `Deref::deref` |
| `SystemAccount`, `UncheckedAccount` | AccountInfo `AsRef::as_ref`, `Deref::deref`, `Key::key` |
| `Address` | Anchor `Key::key` |

The 1.1.2 subset is:

| Receiver | Registered methods |
| --- | --- |
| `Account<T>` | AccountInfo `AsRef::as_ref`, `DerefMut::deref_mut`, `Key::key` |
| `InterfaceAccount<T>` | AccountInfo `AsRef::as_ref`, `Key::key` |
| `Program<T>` | `Deref::deref` |
| `Signer` | AccountInfo `AsRef::as_ref`, `Deref::deref` |
| `UncheckedAccount` | AccountInfo `AsRef::as_ref`, `Deref::deref`, `Key::key` |
| `Address` | Anchor `Key::key` |

`AnchorViews.Store` represents live receiver objects and source loans. These
loans are distinct from the runtime RefCell guards of AccountInfo. A decoded-field
reference retains its parent loan and observes the current value of that field.
A mutable reference writes the same field through the exclusive parent loan;
it is not a copied payload awaiting later write-back. Closing the parent loan
invalidates both decoded-field and AccountInfo references obtained through it.

The 0.27.0 wrappers own their AccountInfo; a view identifies that live field
inside the receiver. Later wrappers store AccountInfo by shared reference, so
their views identify the separately stored record. Cloned later wrappers can
share that record while retaining distinct decoded-field identities. Equal
lamports and data cell handles do not imply equal containing AccountInfo record
identities. InterfaceAccount delegates to
its contained Account and retains its saved owner.

Key methods copy all 32 bytes of the current key and preserve the world. The
defining key provider must be the one in the selected profile; the 1.1.2
rows use the reviewed Address 2.6.1 provider. Account
mutable dereference checks `is_writable` only when `anchor-debug` is enabled.
Its failing branch invokes the actual message operation and then panic. The feature index of the
family must match the compiled feature; no unconditional
writable precondition is added. The selected 0.29.0 InterfaceAccount mutable
dereference delegates to this same Account check.

The listed 0.29.0 Account clone and 0.32.1 Account and InterfaceAccount
clones call `T::clone` before retaining info. The callback receives the
original decoded-field reference, its object identity and its current value. Address-sensitive or interior-mutating callbacks cannot
be replaced with value copies. Retaining the shared AccountInfo reference has
no Rc clone effect. Signer and UncheckedAccount clones have no decoded-value
callback, and cloning the PhantomData of Program does not call `T::clone`.
Placing a returned wrapper gives it a distinct logical object identity without
claiming a heap allocation.

The selected 0.27.0 `Sysvar::deref` returns its current decoded field under
the existing parent loan. `Account::set_inner` calls the actual
destructor of the old payload through the same exclusive field reference, then installs the moved
replacement. Assignment also installs that replacement if destruction
unwinds, retaining its effects; a terminal destructor has no successor.
The AccountInfo field remains in the same receiver. These operations do not
allocate another wrapper or silently clone a payload.

The selected 0.29.0 `Account::into_inner` consumes the wrapper and moves its
current decoded payload into the result. It neither clones nor drops that
payload. The remaining AccountInfo field is a shared reference, so discarding
it adds no Rc decrement. Source ownership still identifies the moved payload.

The listed 0.32.1 `Lamports::get_lamports` first calls the actual
`AsRef` method of the receiver. It
then reads the current lamports cell of the returned record under a temporary shared
RefCell guard and releases that guard. The mutations and unwind of the callback are
retained; a borrow conflict invokes the selected panic provider. The reached
typed-cell condition excludes malformed mathematical interpretations, without
assuming borrow availability or a successful return.

The [binding obligations](../BINDINGS.md) keep source layouts, live loans,
payload ownership and callback effects in the same supplied world. The model
does not authorize mutation through a Rust shared borrow merely because its
state representation can express that mutation. Closed mathematical samples
and source comparison establish neither arbitrary callback termination nor
SDK, compiler or target-layout correctness.

The [Lean view scenarios](../SolanalibTest/Specs/AnchorLang/Views.lean) check live and
expired references, shared/exclusive access, clone callback effects, and both
debug branches. The debug failure scenarios retain logging effects before
panic, and preserve a logging unwind or terminal exit. These generic family
tests do not enlarge the debug-disabled callable entry. The existing
`AnchorViews` conformance family and `anchor-views-0-32-1` native driver check
the registered methods with their pinned debug-disabled configuration; use
the [conformance guide](../../../tools/library-conformance/README.md)
for selected replay and native reproduction.
