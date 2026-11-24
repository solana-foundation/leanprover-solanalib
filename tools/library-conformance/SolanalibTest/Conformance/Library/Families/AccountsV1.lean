/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV1.View
import SolanalibTest.Conformance.Library.Families.AccountsV1.Info

/-!
# Family `AccountsV1`: solana-account-view 1.0.0 and solana-account-info 3.1.1

Driver `rust/accounts-v1`. The projections from the input region of the loader to the model
states are described in `AccountsV1/View.lean` and `AccountsV1/Info.lean`; the decision
procedure, an existential over the ghost components of the state after decided through the graph
of each registered relation, in `AccountsV1/Common.lean`.

* `solana_account_view`: the fourteen `AccountView` members (total references registered as
  `RealizedBy`), and the `Ref`/`RefMut` families at the byte-range index `sliceProfile`
  (`T = [u8]` and `T = u8`), `Ref::map` at `⟨sliceProfile, String, Empty⟩` with scripted
  closures.
* `solana_account_view_1_0_0_forged`: the same checkers on RuntimeAccount headers the loader
  cannot produce (a `resize_delta` near the `i32` bounds, flag bytes other than 0 and 1). The
  `AccountView` checkers decide the registered precondition of each member first: every
  main-corpus record must satisfy it; a forged record outside it (where the `i32` arithmetic of
  the source overflows) must show the documented panic and an unchanged state.
* `solana_account_info`: the four AccountInfo members, and derived `Clone` decided by both the
  Rc family (`clone_reference` at `Info.cloneIndex`) and `clone_observation_reference`. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AccountsV1

def corpora : List (String × List SolanalibTest.Conformance.Library.Checker) := [
  ("solana_account_view_1_0_0", View.checkers),
  ("solana_account_view_1_0_0_forged", View.forgedCheckers),
  ("solana_account_info_3_1_1", Info.checkers)
]

end SolanalibTest.Conformance.Library.Families.AccountsV1
