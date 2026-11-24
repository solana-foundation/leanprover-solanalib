/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuard
public import Solanalib.Specs.Core.TokenRequestAllocatedTypes
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardInputs
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardResources

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

/-- Every vector primitive has its own admission law. The exemption of the destructor is computed
from its actual owned elements, never from an unrelated
list supplied by a caller. Empty construction is an actual state transition. -/
structure VectorFrames {Extra Element Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps (World Extra) Element Resource Unwind Terminal)
    (owned : World Extra → Resource → List Borrow.Guard) : Prop where
  /-- Infallible empty construction preserves existing caller-held guards. -/
  empty : ∀ before, before.1.Valid → ∀ guard slot,
    before.1.resolve guard = some slot →
      AccountInfo.GuardCallback.StateFrame before.1 (ops.empty before).2.1 guard
  /-- Every finite capacity-constructor exit preserves held guards. -/
  capacity : Preserves ops.withCapacity
  /-- Every finite array-constructor exit preserves held guards. -/
  fromList : Preserves ops.fromList
  /-- A push cannot consume a guard held by its caller or enclosing scope. -/
  push : Preserves ops.push
  /-- The complete extend dependency preserves every caller-held guard. -/
  extend : Preserves ops.extend
  /-- Drop may release its actual owned elements and preserves other guards. -/
  drop : PreservesExcept owned ops.drop

/-- These vector resources own no AccountInfo data guards. Their allocation,
contents, resource identities and other auxiliary effects may still change. -/
abbrev PlainVectorFrames {Extra Element Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps (World Extra) Element Resource Unwind Terminal) :=
  VectorFrames ops (fun _ _ => [])

/-- The destructor exemption for a guard vector is exactly its current elements.
Malformed or absent vector storage grants no exemption. This observation is
connected to collection by the separate required `ResourceLaws`. -/
def ownedGuards {Extra Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps (World Extra) OnchainAllocated.GuardElement
      Resource Unwind Terminal) (before : World Extra) (resource : Resource) :
    List Borrow.Guard :=
  ((ops.current before resource).getD []).map (fun entry => entry.2.guard)

/-- Primitive work between collect callbacks, final ownership transfer and
storage-only retirement all preserve each live guard at that call input.
These laws apply even when a later callback/read has no final trace. Actual
borrow acquisitions and element releases are proved local operations instead. -/
structure CollectionFrames {Extra Resource Unwind Terminal : Type}
    (protocol : AllocatedCollect.Protocol Extra Resource Unwind Terminal) : Prop where
  /-- Every intermediate allocator/provider chunk has pointwise admission. -/
  internal : ∀ index acquired,
    Preserves (fun state (_ : Unit) => protocol.internal index acquired state)
  /-- Moving acquired guards into the returned vector does not release them. -/
  finish : Preserves protocol.finish
  /-- Failed collection has no result resource; its storage retirement
  preserves every guard remaining after element cleanup. -/
  retire : ∀ acquired,
    Preserves (fun state (_ : Unit) => protocol.retire none acquired state)

/-- A metas push inside the multisig loop or a hook scope preserves the exact
reference read even if the next loop iteration has no other admitted effects. -/
theorem after_meta_push {types : OnchainAllocated.Types}
    (law : Preserves types.metas.push) {before after : World types.Extra}
    {reference : AllocatedControl.DataRef} {bytes : Bytes}
    {resource : types.MetaResource} {item : Solanalib.Runtime.CpiMeta}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (pushed : types.metas.push before (resource, item) (.returned () after)) :
    reference.read after = some bytes :=
  law.read_returned valid read pushed

/-- Padding allocation cannot erase the mint reference before the subsequent
comparison re-reads it. This consumes the primitive law, not a mint-body exit. -/
theorem after_mint_padding {types : OnchainAllocated.Types}
    (law : Preserves types.paddingBytes.fromList) {before after : World types.Extra}
    {reference : AllocatedControl.DataRef} {bytes padding : Bytes}
    {resource : types.ByteResource}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (allocated : types.paddingBytes.fromList before padding (.returned resource after)) :
    reference.read after = some bytes :=
  law.read_returned valid read allocated

/-- A TLV discriminator push preserves each live enclosing reference before
the decoder observes its next current byte range. -/
theorem after_tlv_push {types : OnchainAllocated.Types}
    (law : Preserves types.discriminators.push) {before after : World types.Extra}
    {reference : AllocatedControl.DataRef} {bytes discriminator : Bytes}
    {resource : types.DiscResource}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (pushed : types.discriminators.push before (resource, discriminator) (.returned () after)) :
    reference.read after = some bytes :=
  law.read_returned valid read pushed

/-- Every held reference, including the outer mint and validation Ref and the
inner collected guards, survives an actual seed-reference vector push. -/
theorem after_seed_push {types : OnchainAllocated.Types}
    (law : Preserves types.seedOps.refs.push) {before after : World types.Extra}
    {reference : AllocatedControl.DataRef} {bytes : Bytes}
    {resource : types.SeedRefResource} {view : AllocatedSeeds.BytesView (World types.Extra)}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (pushed : types.seedOps.refs.push before (resource, view) (.returned () after)) :
    reference.read after = some bytes :=
  law.read_returned valid read pushed

end Solanalib.Specs.Core.Token.AllocatedGuard
