# Anchor 1.0.2 errors and CPI context

The four selected functions use anchor-lang 1.0.2 at revision
`1314a6b83b16e6a31947b372d57988fd0e81559c`. The
[source registry](../source-map.json) pins complete files and exact anchors.

| Function | Source |
| --- | --- |
| `From<AnchorError> for Error` | error.rs:301 |
| `Error::with_pubkeys` | error.rs:367 |
| `Error::with_values` | error.rs:376 |
| `CpiContext::new_with_signer` | context.rs:198 |

Complete-file SHA-256 values are
`c3f5fa7c0b79429191f6c7942344f592c81344dbdf18d3d2bc4ff932f9b7fd78`
for error.rs and
`9ea4fee12e81784dcdfa6a234e165054c1978eae2c2bccab2bd54cbb3902fbd7`
for context.rs. Generated ErrorCode construction is reviewed separately in
anchor-syn 1.0.2 src/codegen/error.rs, hash
`72b3a03dec38e7cbd0a06b5814f6f5bda6a2aee78e10e1861d175e6b1deaa459`.

## Owned error primaries

AnchorErrorOwned retains stable String and Box identities and reads their
contents from actual state. All error fields remain represented: name, u32 code,
message, optional source/account-name origin, and optional value/public-key
comparison. The program branch uses the separately reviewed ProgramError3.0.1
vocabulary, not a runtime error policy.

From<AnchorError> moves existing payload resources into a fresh Box.
With_pubkeys keeps that Box, drops old compared Strings and replaces the
comparison. Their shared type index contains operations without a hidden law
bundle. The boxing family explicitly requires only the current payload and freshness of the returned Box, plus preservation of the moved String fields. The
comparison families require the frame of the old-String destructor on other
Strings and Box descriptors, the current payload of the actual store, and its String
frame. `ComparisonStoreReady` additionally supplies an ordinary assignment
after every reached normal old-comparison cleanup. Its continuation theorem
constructs that actual write or retains the same terminal cleanup exit.
Unrelated allocation and Box-retirement laws are not required, and no opaque
dependency is assumed to return.

Their normal postconditions retain `Ready`: the initial fields are live and
pairwise distinct; allocation preserves moved fields, and comparison cleanup
preserves retained fields before the new payload is stored. Each of the three
boxing or four replacement guarantees contributes to those actual posts.
Retirement and current-value lifecycle results separately take the primitive
facts they use. They do not make broader unused guarantees admission conditions
of another family. Actual Rust destructor and allocator behavior remain source
binding obligations.

The generated fixed ErrorCode factory sequences name literal copying,
fixed-message formatting and Box allocation. These distinct dependencies
preserve their actual states and terminal exits. There is no user unwind
callback in these fixed operations and no opaque whole-SDK error factory.

With_values calls left then right ToString. Normal results are String resource
identities, not Result errors. The second callback receives the actual state of the first callback. The first String is protected while the second runs. After both
return, old comparison resources are dropped and the same Box is updated;
consumed operands drop left then right. On a conversion unwind, a partial
String is cleaned before the operand scope; receiver cleanup then reads the current payload of the
Box. The receiver has moved into the return place before the
operands drop. If an operand destructor then unwinds, the drop
semantics of the language release the return place, but rustc does not drop it
(rust-lang/rust#47949, observed with rustc 1.97.0-nightly 2026-04-30 at every
optimization level and in the library conformance suite): the updated Box and
its Strings stay live. `protectReturnPlace` admits both outcomes on exactly that
path; every other path is the protected operand scope.
A second unwind uses an explicit terminal-only policy. Terminal exits expose
no state and run no later callbacks. No rollback is inferred.

The with_values family requires the four replacement guarantees, live,
distinct error fields, and `CallReady` at the actual initial call. Its
`ReturnedAdmissible` component supplies the normal ownership result. A left
conversion unwind must leave the current error ready for cleanup; a right
unwind must also retain the actual first String, live and disjoint from the
current error fields. Reached operand drops retain those error resources only
when another local step follows. Terminal and double-unwind exits need no
later resources. After each actual pair of returning conversions, the reached
ordinary assignment must be available. These conditions establish local
assignment and cleanup continuations without requiring any opaque callback
to terminate. An operand may own disjoint String storage and retire it;
unrelated states where that storage aliases the error are not preconditions.

A returned right callback preserves the actual first result and held error
fields. A returned String may transfer storage from a capture; its ownership
transfer must be justified by the source interpretation. Other state may change.
The normal postcondition returns the same Box with `Ready`, proved using both
returned conversion frames, primitive comparison replacement and the normal
operand-drop frames. The separate `Admissible`, `StringFrame` and `DropFrame`
vocabulary can express stronger equality frames on all outcomes. The family
requires only current resource readiness on continuing unwind paths, allowing
changed but ready error payloads and unrelated state effects. Fixed
String/Error drops use Empty unwind; arbitrary operand destructors retain their
actual outcomes. No callback outcome is filtered to establish these properties.

Controls use operands owning String slots in the same heap: conversions create
distinct copies, then original operands retire left to right. Another admitted
execution unwinds, cleaning the partial String, both operands and the receiver.
An operand-drop unwind after assignment admits both the released receiver and
the live updated Box; a conversion unwind admits only the released receiver.
A following with_pubkeys call uses the returned `Ready` to admit replacement
on that same Box and retires both copied comparison Strings.
A normal destructor that invalidates a held comparison still has its raw finite
exit but fails returned-path admission. These are mathematical witnesses; their allocation
budget is not gas, heap size or source allocator behavior.

Additional exact-family controls admit boxing with an unrelated faulty String
constructor, and comparison replacement with an unrelated faulty Box destructor.
The normal posts still hold. Separate controls retain raw allocations that reuse
a live Box, fail to initialize it, or erase moved Strings; these actual outcomes
refute freshness, current payload or returned readiness, respectively.
Callback controls admit one provider with both a normal return and an unframed
conversion unwind, and another whose returned operand drop changes the Box
during unwind cleanup. The actual modified Box is retired in each unwind trace.
These providers fail the broader all-outcome ownership frame while satisfying
the exact family posts; they establish no Rust aliasing or ownership permission.
Further controls reject lost error or partial-String resources on a continuing
unwind and a missing reached assignment. They retain terminal and double-unwind
exits, and admit opaque callbacks with no finite outcome.

## Owned context construction

The primary new_with_signer_contract moves arbitrary T, copies the program ID
and stores nested signer seeds unchanged. It calls the existing infallible
empty-vector dependency once and returns a fresh remaining-vector owner. It
invents no allocation failure for Vec::new; provider state can record logical
ownership bookkeeping. The family requires only two guarantees about that
actual empty call: its returned owner currently denotes an empty sequence and
was absent before the call. Both establish the current/fresh
postconditions of the constructor. Capacity construction, array construction, push, extend and
drop laws are not required by this constructor. The constructor calls neither
ToAccountInfos nor ToAccountMetas, validates no seeds and invokes no program.

Controls admit a provider whose unused drop operation fails the generic vector
law, then execute the constructor and derive its exact current/fresh post.
Separate controls reject a nonempty primitive result and reuse of a live owner;
each violates one of the two retained guarantees. The copied-value observation
family has no vector-provider premise.

Later observation reads the current state of the vector; a push does not leave every
context modeled as permanently empty. Transfer consumes the same resource-bearing
context type. A versioned client passes the exact owner of the constructor into
transfer and checks retirement. Rust references, lifetimes, source addresses,
empty Vec representation and destructor implementation remain binding work.

## Observation facets and proof boundary

The earlier value functions are named from_anchor_error_observation_contract,
with_pubkeys_observation_contract, with_values_observation_contract and
new_with_signer_observation_contract. They retain the original value/callback
facets while forgetting stable resources and are not primary lifecycle models.
Each parameterized observation has an exactly linked closed family.
These observation families have unconditional preconditions: the two pure value
operations preserve their copied payloads, and with_values retains its explicit
conversion and cleanup callback relation. They require none of the owned
String/Box primitive laws.

Every primary has a closed Family, named run and sample, and closed
FamilyReference, FamilySatisfiable and FamilyHasExecution witnesses. References
cover every admitted dependency interpretation; concrete samples establish
finite execution only for that interpretation. The separate tests cover
composition, callback/error order, resource retirement and exceptional exits.

These are mathematical models, not Rust body proofs, heap/layout interpretation,
implementation semantics or program logic proofs, executable Rust clients or canonical implementation specifications. All
Rust proof statuses remain open. The reviewed SDK files can be found under
[lang/src](https://github.com/solana-foundation/anchor/tree/1314a6b83b16e6a31947b372d57988fd0e81559c/lang/src).
