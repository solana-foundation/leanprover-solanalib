/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedHooks
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardProviders
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardCollection
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardObservations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

open AllocatedGuard

/-- The actual source clone helper preserves held guards through its two Rc
operations, at their real sequential call inputs. -/
theorem cloneInfo_frames {types : Types} (rcClone : Preserves types.rc.cloneRc)
    (info : AccountInfo.Value) :
    Preserves (fun state (_ : Unit) => cloneInfo types info state) :=
  perform_preserves ((rc_clone_preserves rcClone).rcLift.arguments (fun (_ : Unit) => info))

/-- Source insertion clones an AccountInfo before the vector callback. Each
primitive is admitted independently of the final outcome of the continuation. -/
theorem pushClonedInfo_frames {types : Types} (rcClone : Preserves types.rc.cloneRc)
    (infoPush : Preserves types.infos.push)
    (resource : types.InfoResource) (info : AccountInfo.Value) :
    Preserves (fun state (_ : Unit) => pushClonedInfo types resource info state) :=
  bind_preserves (cloneInfo_frames rcClone info)
    (fun cloned => perform_preserves
      (infoPush.arguments (fun (_ : Unit) => (resource, cloned))))

/-- Every finite multisig-loop exit frames its held reference and all outer
guards. The source loop re-reads current signer bytes after actual vector and
Rc callbacks; its proof uses those primitive laws, never a whole-loop premise. -/
theorem appendMultisigSigners_frames {types : Types} (rcClone : Preserves types.rc.cloneRc)
    (infoPush : Preserves types.infos.push) (metaPush : Preserves types.metas.push)
    (prepared : Prepared types) (reference : AllocatedControl.DataRef) (count : Nat)
    (additional : List AccountInfo.Value) :
    Preserves (fun state (_ : Unit) =>
      appendMultisigSigners types prepared reference count additional state) := by
  induction additional with
  | nil => exact result_preserves (.ok ())
  | cons info rest induction =>
    apply bind_preserves (inspect_preserves (signerKeysAt types reference count))
    intro keys
    split
    · apply bind_preserves (perform_preserves
        (metaPush.arguments (fun (_ : Unit) =>
          (prepared.instruction.metas, Instruction.accountMeta info.key true false))))
      intro _
      exact bind_preserves (pushClonedInfo_frames rcClone infoPush prepared.infos info)
        (fun _ => induction)
    · exact induction

/-- The actual collectRefs stage preserves caller-held guards. The proof
consumes the local protocol of the higher-order provider and pointwise internal
laws and follows each real borrow/acquisition/cleanup trace. -/
theorem collectRefs_frames {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (conforms : deps.collect.Conforms protocol) (frames : CollectionFrames protocol)
    (raiseLaw : Preserves types.raise) (resource : types.InfoResource) :
    Preserves (fun state (_ : Unit) => collectRefs types deps resource state) :=
  bind_preserves (inspect_preserves (fun state => types.infos.current state resource))
    (fun infos => collection_preserves conforms frames raiseLaw
      (infoIterator types resource infos.length))

/-- An actual returned collectRefs state still reads every outer data Ref.
Only guards freshly acquired by this collection are owned by its vector. -/
theorem collectRefs_outer_read {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (conforms : deps.collect.Conforms protocol) (frames : CollectionFrames protocol)
    (raiseLaw : Preserves types.raise)
    {resource : types.InfoResource} {before after : World types.Extra}
    {reference : AllocatedControl.DataRef} {bytes : Bytes} {collected : types.GuardResource}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (called : collectRefs types deps resource before (.returned (.ok collected) after)) :
    reference.read after = some bytes :=
  (collectRefs_frames conforms frames raiseLaw resource).read_returned (args := ()) valid read
    called

end Solanalib.Specs.Core.Token.OnchainAllocated
