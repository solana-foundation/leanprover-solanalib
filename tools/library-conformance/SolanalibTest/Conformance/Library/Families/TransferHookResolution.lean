/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TransferHookResolution.Check

/-!
# Transfer-hook-interface 0.9.0 account resolution

Native calls of `add_extra_accounts_for_execute_cpi`, including real shared
RefCell borrows, Rc clones/drops, caller instruction/vector updates and the
ordinary TLV/seed resolver. PDA syscalls are scripted; there is no CPI.
The sample vector allocator never fails; finite allocation failures remain
in the generic model, outside these native records. Seed-vector tests cover
fixed/key-data extras, malformed configurations and empty-seed PDA calls;
this finite checker does not support nonempty borrowed-seed vectors.

`fullRun_fn`, `run_iff` and `observed_iff` connect the computed relation to the
registered reference. Compared observations include unchanged account bytes,
all value fields, live caller guards, exact output metas/infos and their alias
order, Rc counts, ordered PDA inputs, bump initialization and leftover replies.
Terminal cases exercise the first mandatory PDA request, which has no after
world; that forced request is checked separately. Native tests select unwind
panics with release optimization/check flags, not deployment abort semantics.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TransferHookResolution

def checkers : List Checker := [{
  function := "spl_transfer_hook_interface::onchain::add_extra_accounts_for_execute_cpi"
  generics := []
  reference :=
    "Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_re\
      ference"
  check := check
  decides :=
    ["Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_r\
      eference"]
  decidesRequires :=
    ["Solanalib.Specs.SplTransferHookInterface.onchain.add_extra_accounts_for_execute_cpi_r\
      eference"] }]

def corpora : List (String × List Checker) := [("spl_transfer_hook_interface_0_9_0", checkers)]

end SolanalibTest.Conformance.Library.Families.TransferHookResolution
