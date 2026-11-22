/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.CopyBack
public import Solanalib.Runtime.Env

@[expose] public section

/-! Initialize a library account store from transaction state.
`initialStore` copies each account with its entry length and a free lease.
Library contracts can import `AccountState` or `StoreOps` independently. -/

namespace Solanalib.Runtime

/-- The store of an instruction at its start: every account of the transaction context,
with its length at entry and no lease. -/
def initialStore (ts : TxState) : Store := fun t =>
  let a := ts.acct t
  { owner := a.owner, lamports := a.lamports, data := a.data, entryLen := a.data.length,
    lease := .free, copy := none }

end Solanalib.Runtime
