/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic
public import Solanalib.Runtime.AccountState
public import Solanalib.Runtime.StoreOps
public import Solanalib.Runtime.CopyBack
public import Solanalib.Runtime.View
public import Solanalib.Runtime.Protocol
public import Solanalib.Runtime.Ids
public import Solanalib.Runtime.Profile
public import Solanalib.Runtime.Error
public import Solanalib.Runtime.Account
public import Solanalib.Runtime.ProgramCache
public import Solanalib.Runtime.Context
public import Solanalib.Runtime.Borrowed
public import Solanalib.Runtime.Layout
public import Solanalib.Runtime.ReadBack
public import Solanalib.Runtime.Sysvar
public import Solanalib.Runtime.Prims
public import Solanalib.Runtime.Memory
public import Solanalib.Runtime.Syscall
public import Solanalib.Runtime.Cpi
public import Solanalib.Runtime.System
public import Solanalib.Runtime.LoaderEffects
public import Solanalib.Runtime.Exec
public import Solanalib.Runtime.Message
public import Solanalib.Runtime.FlagConsistency
public import Solanalib.Runtime.Nonce
public import Solanalib.Runtime.Transaction
public import Solanalib.Runtime.Frame
public import Solanalib.Runtime.Executable
public import Solanalib.Runtime.LamportFrame
public import Solanalib.Runtime.StackFrame
public import Solanalib.Runtime.SysvarCoherence
public import Solanalib.Runtime.ReadonlyFrame
public import Solanalib.Runtime.Env
public import Solanalib.Runtime.Store
public import Solanalib.Runtime.WritesLegal
public import Solanalib.Runtime.Theorems

@[expose] public section

/-!
# Solana execution model

The complete model of account state, program-visible memory, runtime checks and
transaction commit. This package depends only on Lean.

The [model documentation](../README.md#model-report) follows a transaction through these
definitions and links each stage to versioned runtime sources. The report includes
the complete Lean sources and declaration reference.
-/
