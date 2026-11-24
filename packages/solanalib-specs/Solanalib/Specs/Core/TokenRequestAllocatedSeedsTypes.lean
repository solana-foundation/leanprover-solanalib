/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestHooks
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.AddressSyscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds

universe u v w x y z

/-- An unpacked configuration retains ownership of its literal byte vector.
The other fields have the exact byte widths of account-resolution 0.11.1. -/
inductive Seed (ByteResource : Type v) where
  /-- The zero tag ends the packed seed configuration. -/
  | uninitialized
  /-- A literal seed owns the retained byte-vector resource. -/
  | literal (resource : ByteResource)
  /-- An instruction-data seed retains its byte offset and length. -/
  | instructionData (offset length : UInt8)
  /-- An account-key seed retains the selected account index. -/
  | accountKey (index : UInt8)
  /-- An account-data seed retains its account index, byte offset and length. -/
  | accountData (index offset length : UInt8)
  deriving DecidableEq, Repr

/-- A retained source slice: its length is copied when the borrow is formed,
and its bytes are read from the actual later state. The source binding must
justify that `read` follows the same reference and preserves its lifetime. -/
structure BytesView (State : Type u) where
  /-- The slice length fixed when the retained view is formed. -/
  length : Nat
  /-- Read through the retained reference in the supplied current state. -/
  read : State → Option Bytes

/-- Missing or length-changing views are representation failures, not new
ProgramErrors or source panic outcomes. -/
def BytesView.observe {State : Type u} (view : BytesView State) (state : State) :
    Option Bytes := do
  let bytes ← view.read state
  if bytes.length = view.length then some bytes else none

/-- A subslice keeps its original extent while following its retained parent
reference. The caller models the source bounds error before making this view. -/
def BytesView.slice {State : Type u} (view : BytesView State) (offset length : Nat) :
    BytesView State :=
  { length := length
    read := fun state => do
      let bytes ← view.observe state
      if offset + length ≤ view.length then some (Solanalib.Runtime.slice bytes offset length) else
        none }

/-- Current observations at the selected resolver call. `accountsAt` models
the ordinary closure over retained account keys and data guards, rather than
an arbitrary effectful implementation of the generic source callback. -/
structure Args (State : Type u) where
  /-- Observe the current extra-account metadata through the selected source reference. -/
  extraAt : State → Option Hook.ExtraMeta
  /-- Observe the instruction bytes through the retained source slice. -/
  instructionAt : State → Option Bytes
  /-- Observe the program key through the selected source reference. -/
  programAt : State → Option Solanalib.Runtime.Pubkey
  /-- Observe the current keys and data of the accounts retained by the source closure. -/
  accountsAt : State → Option Hook.Observations

/-- The ordinary address-library dependency, using the shared selected-target
input vocabulary. Instantiate it with `Address.Syscall.findRun syscall panic`
to retain syscall returns, independent finite failures, and the local panic
site. Returning a ProgramError is not an outcome of this source function. -/
abbrev FindPda (State : Type u) (Unwind : Type y) (Terminal : Type z) :=
  Callback.Run State Address.Syscall.PdaInputs (Solanalib.Runtime.Pubkey × UInt8) Unwind Terminal

/-- The three vector dependencies in source order. A literal moves into
`seeds.push`: that provider owns cleanup of a moved argument on unwind and
recursive literal cleanup during `seeds.drop`. Dropping the literal again in
the caller would duplicate ownership. Reference-vector drop owns no referent.
These are concrete provider binding obligations, not universal frame laws. -/
structure Ops (State : Type u) (ByteResource : Type v) (SeedResource : Type w)
    (RefResource : Type x) (Unwind : Type y) (Terminal : Type z) where
  /-- The dependency that constructs and owns literal byte vectors. -/
  bytes : Owned.VectorOps State UInt8 ByteResource Unwind Terminal
  /-- The dependency that owns unpacked seeds, including transferred literal resources. -/
  seeds : Owned.VectorOps State (Seed ByteResource) SeedResource Unwind Terminal
  /-- The dependency that owns the vector of borrowed seed views, without owning their
  referents. -/
  refs : Owned.VectorOps State (BytesView State) RefResource Unwind Terminal

/-- Primitive vector guarantees stay separate from source ownership and
reference-identity obligations. In particular they impose no blanket frame. -/
structure Ops.Laws {State : Type u} {ByteResource : Type v} {SeedResource : Type w}
    {RefResource : Type x} {Unwind : Type y} {Terminal : Type z}
    (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal) : Prop where
  /-- Local vector guarantees for the literal-byte dependency. -/
  bytes : ops.bytes.Laws
  /-- Local vector guarantees for the owning seed dependency. -/
  seeds : ops.seeds.Laws
  /-- Local vector guarantees for the borrowed-view vector dependency. -/
  refs : ops.refs.Laws

end Solanalib.Specs.Core.Token.AllocatedSeeds
