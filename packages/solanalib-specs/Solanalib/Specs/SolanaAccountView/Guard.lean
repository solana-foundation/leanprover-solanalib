/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewMapFamily
public import Solanalib.Specs.Core.AccountViewMap

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAccountView

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView

/-! Generic mathematical reference models. A mapped target has its own
interpreted access permission while its original account lease remains held.
Source callbacks preserve the whole world, including ordinary-error effects.
The source ManuallyDrop sequence selects retainLease for callback unwind. -/

namespace Ref

/-- The generic source contract for all interpreted target types. -/
def deref_contract : Family := derefFamily .shared false

/-- The reference delegates to the common account and lease model. -/
def deref_model : FamilyRun deref_contract := derefRun .shared false

/-- The explicit byte-target instance used for finite-execution evidence. -/
def deref_sample : deref_contract.Index := sliceProfile

/-- Reference correctness covers every family index. -/
theorem deref_reference : FamilyReference deref_contract deref_model :=
  derefFamily_reference .shared false

/-- The named instance has a satisfiable precondition. -/
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  derefFamily_satisfiable .shared false

/-- The named reference has a concrete permitted finite execution. -/
theorem deref_execution : FamilyHasExecution deref_contract deref_model deref_sample :=
  derefFamily_execution .shared false

/-- The supplemental destructor contract for this guard kind. -/
def release_contract : Family := releaseFamily .shared

/-- The reference delegates to the common account and lease model. -/
def release_model : FamilyRun release_contract := releaseRun .shared

/-- The explicit byte-target instance used for finite-execution evidence. -/
def release_sample : release_contract.Index := sliceProfile

/-- Reference correctness covers every family index. -/
theorem release_reference : FamilyReference release_contract release_model :=
  releaseFamily_reference .shared

/-- The named instance has a satisfiable precondition. -/
theorem release_satisfiable : FamilySatisfiable release_contract release_sample :=
  releaseFamily_satisfiable .shared

/-- The named reference has a concrete permitted finite execution. -/
theorem release_execution : FamilyHasExecution release_contract release_model release_sample :=
  releaseFamily_execution .shared

/-- The generic source contract for all interpreted target types. -/
def map_contract : Family := mapFamily .shared

/-- The reference delegates to the common account and lease model. -/
def map_model : FamilyRun map_contract := mapRun .shared

/-- The explicit byte-target instance used for finite-execution evidence. -/
def map_sample : map_contract.Index := mapSample

/-- Reference correctness covers every family index. -/
theorem map_reference : FamilyReference map_contract map_model :=
  mapFamily_reference .shared

/-- The named instance has a satisfiable precondition. -/
theorem map_satisfiable : FamilySatisfiable map_contract map_sample :=
  mapFamily_satisfiable .shared

/-- The named reference has a concrete permitted finite execution. -/
theorem map_execution : FamilyHasExecution map_contract map_model map_sample :=
  mapFamily_execution .shared

end Ref

namespace RefMut

/-- The generic source contract for all interpreted target types. -/
def deref_mut_contract : Family := derefFamily .exclusive true

/-- The reference delegates to the common account and lease model. -/
def deref_mut_model : FamilyRun deref_mut_contract := derefRun .exclusive true

/-- The explicit byte-target instance used for finite-execution evidence. -/
def deref_mut_sample : deref_mut_contract.Index := sliceProfile

/-- Reference correctness covers every family index. -/
theorem deref_mut_reference : FamilyReference deref_mut_contract deref_mut_model :=
  derefFamily_reference .exclusive true

/-- The named instance has a satisfiable precondition. -/
theorem deref_mut_satisfiable : FamilySatisfiable deref_mut_contract deref_mut_sample :=
  derefFamily_satisfiable .exclusive true

/-- The named reference has a concrete permitted finite execution. -/
theorem deref_mut_execution : FamilyHasExecution deref_mut_contract deref_mut_model
  deref_mut_sample :=
  derefFamily_execution .exclusive true

/-- The supplemental destructor contract for this guard kind. -/
def release_contract : Family := releaseFamily .exclusive

/-- The reference delegates to the common account and lease model. -/
def release_model : FamilyRun release_contract := releaseRun .exclusive

/-- The explicit byte-target instance used for finite-execution evidence. -/
def release_sample : release_contract.Index := sliceProfile

/-- Reference correctness covers every family index. -/
theorem release_reference : FamilyReference release_contract release_model :=
  releaseFamily_reference .exclusive

/-- The named instance has a satisfiable precondition. -/
theorem release_satisfiable : FamilySatisfiable release_contract release_sample :=
  releaseFamily_satisfiable .exclusive

/-- The named reference has a concrete permitted finite execution. -/
theorem release_execution : FamilyHasExecution release_contract release_model release_sample :=
  releaseFamily_execution .exclusive

end RefMut

end Solanalib.Specs.SolanaAccountView

namespace Solanalib.Specs.SolanaAccountView

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView

/-! Generic mathematical reference models. A mapped target has its own
interpreted access permission while its original account lease remains held.
Source callbacks preserve the whole world, including ordinary-error effects.
The source ManuallyDrop sequence selects retainLease for callback unwind. -/

namespace Ref

/-- The generic source contract for all interpreted target types. -/
def try_map_contract : Family := tryMapFamily .shared

/-- The reference delegates to the common account and lease model. -/
def try_map_model : FamilyRun try_map_contract := tryMapRun .shared

/-- The explicit byte-target instance used for finite-execution evidence. -/
def try_map_sample : try_map_contract.Index := tryMapSample

/-- Reference correctness covers every family index. -/
theorem try_map_reference : FamilyReference try_map_contract try_map_model :=
  tryMapFamily_reference .shared

/-- The named instance has a satisfiable precondition. -/
theorem try_map_satisfiable : FamilySatisfiable try_map_contract try_map_sample :=
  tryMapFamily_satisfiable .shared

/-- The named reference has a concrete permitted finite execution. -/
theorem try_map_execution : FamilyHasExecution try_map_contract try_map_model try_map_sample :=
  tryMapFamily_execution .shared

end Ref

namespace RefMut

/-- The generic source contract for all interpreted target types. -/
def deref_contract : Family := derefFamily .exclusive false

/-- The reference delegates to the common account and lease model. -/
def deref_model : FamilyRun deref_contract := derefRun .exclusive false

/-- The explicit byte-target instance used for finite-execution evidence. -/
def deref_sample : deref_contract.Index := sliceProfile

/-- Reference correctness covers every family index. -/
theorem deref_reference : FamilyReference deref_contract deref_model :=
  derefFamily_reference .exclusive false

/-- The named instance has a satisfiable precondition. -/
theorem deref_satisfiable : FamilySatisfiable deref_contract deref_sample :=
  derefFamily_satisfiable .exclusive false

/-- The named reference has a concrete permitted finite execution. -/
theorem deref_execution : FamilyHasExecution deref_contract deref_model deref_sample :=
  derefFamily_execution .exclusive false

/-- The generic source contract for all interpreted target types. -/
def try_map_contract : Family := tryMapFamily .exclusive

/-- The reference delegates to the common account and lease model. -/
def try_map_model : FamilyRun try_map_contract := tryMapRun .exclusive

/-- The explicit byte-target instance used for finite-execution evidence. -/
def try_map_sample : try_map_contract.Index := tryMapSample

/-- Reference correctness covers every family index. -/
theorem try_map_reference : FamilyReference try_map_contract try_map_model :=
  tryMapFamily_reference .exclusive

/-- The named instance has a satisfiable precondition. -/
theorem try_map_satisfiable : FamilySatisfiable try_map_contract try_map_sample :=
  tryMapFamily_satisfiable .exclusive

/-- The named reference has a concrete permitted finite execution. -/
theorem try_map_execution : FamilyHasExecution try_map_contract try_map_model try_map_sample :=
  tryMapFamily_execution .exclusive

end RefMut

end Solanalib.Specs.SolanaAccountView
