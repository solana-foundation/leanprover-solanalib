/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuardComposition
public import Solanalib.Specs.Core.TokenRequestAllocatedAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedResourceAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedBorrowAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedResults

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

open AllocatedControl

/-- The complete ordinary preparation for fee=None. The first two stages
retain all four owned arguments, so their failures clean local resources
before those arguments. A hook call moves source/destination/authority and a
new mint clone into the helper; only the original mint owner of the caller remains
after that point. No-hook success drops all four original arguments. In both
branches the mint data Ref ends before preparation returns to the CPI caller.

Allocation, Rc, standard collection, panic and cleanup dependencies expose
their actual finite exits. Their Rust implementations and the memory binding
are not assumed proved by this composition. -/
def prepare (types : Types) (deps : Dependencies types) (args : Onchain.Args) :
    Run types (Prepared types) :=
  bind (moveOnOk types.doubleUnwind (argumentDrops types args) (base types args)) fun prepared =>
  bind (moveOnOk types.doubleUnwind (argumentDrops types args)
    (moveOnOk types.doubleUnwind (prepared.drops types) (beginMint types args)))
    fun (mintReference, program) =>
    match program with
    | none => scope types.doubleUnwind (argumentDrops types args)
        (scope types.doubleUnwind [mintReference.drop] (pure prepared))
    | some programId =>
      bind (cloneInfo types args.mint) fun mintClone =>
        scope types.doubleUnwind [dropInfo types args.mint]
          (moveOnOk types.doubleUnwind (prepared.drops types)
            (scope types.doubleUnwind [mintReference.drop]
              (bind (addHook types deps { args with mint := mintClone } programId prepared)
                fun _ => pure prepared)))

/-- The actual opaque invocation receives the current constructed instruction,
ordered AccountInfos and unchanged signer seed slices. Its Err, unwind and
terminal exits are retained; locally owned vectors are cleaned on ordinary
return or unwind, and a terminal exit bypasses those destructors. -/
def invoke (types : Types) (deps : Dependencies types) (args : Onchain.Args) :
    Run types Unit :=
  bind (prepare types deps args) fun prepared =>
    scope types.doubleUnwind (prepared.drops types)
      (bind (inspect fun state => prepared.observe types state args.signers) fun request =>
        fun state => deps.invoke state request)

/-- Types and explicit dependency interpretations for the source family. -/
structure Index where
  /-- The target, storage types and primitive dependency interpretations. -/
  types : Types
  /-- The collection and CPI dependencies for those exact types. -/
  dependencies : Dependencies types

/-- The operational fee=None family admits the actual preparation primitives
before dependent reads and checked releases. Each finite primitive exit must
retain held guards and separately owned resources, and normal returns retain
typed data needed by subsequent acquisitions. One actual collection protocol
is shared by the guard, data, resource and cleanup-order obligations. Actual
source prefixes also supply the local domain of each selected borrow, with protocol
validity required only where a successful acquisition retains a Ref. No
completed preparation or invocation outcome is assumed. The post is
unchanged raw behavior; provider termination and source representation remain
separate obligations, with no filter on actual error/unwind/terminal exits. -/
def family : Family where
  Index := Index
  State := fun index => World index.types.Extra
  Args := fun _ => Onchain.Args
  Value := fun _ => Except Error Unit
  Unwind := fun index => index.types.Unwind
  Terminal := fun index => index.types.Terminal
  contract := fun index => {
    requires := fun state args => ∃ protocol,
      Admission.Admitted index.types index.dependencies protocol ∧
      Admission.ResourceReady index.types index.dependencies protocol ∧
      Admission.BorrowReady index.types index.dependencies protocol state args
    post := fun state args => invoke index.types index.dependencies args state }

/-- The reference follows exactly the ordinary preparation of the source and the
chosen opaque dependency relations, including exceptional cleanup. -/
def reference : FamilyRun family :=
  fun index state args => invoke index.types index.dependencies args state

/-- Every dependency interpretation satisfies the relational control-flow
contract, independently of the concrete successful sample used for nonvacuity. -/
theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ execution
  exact execution

/-- Family admission supplies a real continuation for every finite ordinary
primitive exit while a source data Ref is held. The next read and checked drop
cannot silently disappear after a guard-destroying callback. -/
theorem family_primitive_retain {index : Index} {initial : World index.types.Extra}
    {initialArgs : Onchain.Args} (ready : (family.contract index).requires initial initialArgs)
    {Args Value : Type}
    {call : Callback.Run (World index.types.Extra) Args Value
      index.types.Unwind index.types.Terminal}
    (selected : Admission.Primitive index.types call)
    {before : World index.types.Extra} {args : Args} {reference : DataRef} {bytes : Bytes}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    {pending : Outcome (World index.types.Extra) Value index.types.Unwind index.types.Terminal}
    (called : call before args pending) :
    ∃ observed final,
      bind (perform fun state => call state args) (fun _ => inspect reference.read) before observed
        ∧
      AccountInfo.GuardCallback.releaseOutcome reference.guard observed = some final ∧
      scope index.types.doubleUnwind [reference.drop]
        (bind (perform fun state => call state args) (fun _ => inspect reference.read)) before
          final := by
  obtain ⟨protocol, admitted, _⟩ := ready
  exact admitted.read_cleanup selected valid read called

/-- The actual successful base prefix reaches the mint borrow. Family
admission supplies its selected read domain; no separate initial validity or
typed-cell assumption is needed by this continuation. -/
theorem family_borrow_continue {index : Index} {initial : World index.types.Extra}
    {initialArgs : Onchain.Args} (ready : (family.contract index).requires initial initialArgs)
    {prepared : Prepared index.types} {before : World index.types.Extra}
    (reached : base index.types initialArgs initial (.returned (.ok prepared) before)) :
    ∃ result after, borrow index.types.raise true initialArgs.mint before (.returned result after)
      := by
  obtain ⟨protocol, _, _, borrows⟩ := ready
  exact borrows.mint_continue reached

/-- After the reached mint acquisition, every actual selected primitive exit
retains its local source read and checked release. The required live bytes and
protocol invariant follow from the family gate at that exact acquisition. -/
theorem family_mint_primitive_retain {index : Index} {initial : World index.types.Extra}
    {initialArgs : Onchain.Args} (ready : (family.contract index).requires initial initialArgs)
    {prepared : Prepared index.types} {before : World index.types.Extra}
    (reached : base index.types initialArgs initial (.returned (.ok prepared) before))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow .shared initialArgs.mint.data before.1 = (.ok guard, during))
    {Args Value : Type}
    {call : Callback.Run (World index.types.Extra) Args Value
      index.types.Unwind index.types.Terminal}
    (selected : Admission.Primitive index.types call) {args : Args}
    {pending : Outcome (World index.types.Extra) Value index.types.Unwind index.types.Terminal}
    (called : call (during, before.2) args pending) :
    ∃ bytes : Bytes, ∃ observed final,
      borrow index.types.raise true initialArgs.mint before
        (.returned (.ok ⟨guard, bytes.length⟩) (during, before.2)) ∧
      bind (perform fun state => call state args)
        (fun _ => inspect (⟨guard, bytes.length⟩ : DataRef).read) (during, before.2) observed ∧
      AccountInfo.GuardCallback.releaseOutcome guard observed = some final ∧
      withData index.types.raise index.types.doubleUnwind true initialArgs.mint
        (fun reference => bind (perform fun state => call state args)
          (fun _ => inspect reference.read)) before final := by
  obtain ⟨protocol, admitted, _, borrows⟩ := ready
  exact borrows.primitive_scope admitted (.mint reached) (by decide) acquired selected called

/-- The actual successful PDA reply of a family has the exact local wrapper
continuation. The initialized address is obtained before decoding the reply. -/
theorem family_pda_success {index : Index} {initial : World index.types.Extra}
    {initialArgs : Onchain.Args} (ready : (family.contract index).requires initial initialArgs)
    {before after : World index.types.Extra} {inputs : Address.Syscall.PdaInputs}
    (bounded : inputs.Bounded) {reply : Address.Syscall.PdaReply}
    (called : index.types.pdaSyscall before (Address.Syscall.pdaRequest inputs) (.returned reply
      after))
    (zero : reply.status = 0) :
    ∃ address, reply.addressOutput = some address ∧
      index.types.findPda before inputs (.returned (address, reply.bumpOutput) after) := by
  obtain ⟨protocol, admitted, _⟩ := ready
  exact admitted.pdaReady.success_retain bounded called zero

/-- Successful collection observes the same source-sized owned Ref vector,
using the same selected protocol as its guard and storage admission. -/
theorem family_collection_current {index : Index} {initial : World index.types.Extra}
    {initialArgs : Onchain.Args} (ready : (family.contract index).requires initial initialArgs)
    {resource : index.types.InfoResource} {before after : World index.types.Extra}
    {collected : index.types.GuardResource} {infos : List AccountInfo.Value}
    (current : index.types.infos.current before resource = some infos)
    (called : collectRefs index.types index.dependencies resource before (.returned (.ok collected)
      after)) :
    ∃ elements, index.types.guards.current after collected = some elements ∧
      elements.length = infos.length := by
  obtain ⟨protocol, admitted, _⟩ := ready
  exact collectRefs_success_length index.types index.dependencies protocol
    admitted.conforms admitted.collected resource before after collected infos current called

end Solanalib.Specs.Core.Token.OnchainAllocated
