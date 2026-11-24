/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsUnpack
public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsPda

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds

universe u v w x y z

variable {State : Type u} {ByteResource : Type v} {SeedResource : Type w}
  {RefResource : Type x} {Unwind : Type y} {Terminal : Type z}

/-- Follow the same selected account-key reference in the supplied current
observation. The source binding justifies its identity across callbacks. -/
def accountKeyAt (args : Args State) (index : Nat) (state : State) : Option
  Solanalib.Runtime.Pubkey := do
  let accounts ← args.accountsAt state
  let account ← accounts[index]?
  some account.1

/-- Missing data at initial selection is a source error; losing this retained
view later is a representation failure instead. -/
def accountDataAt (args : Args State) (index : Nat) (state : State) : Option Bytes := do
  let accounts ← args.accountsAt state
  let account ← accounts[index]?
  account.2

/-- Resolve one borrowed seed slice in the state of its source match arm.
The resulting view fixes the borrow length, not its future byte contents.
Uninitialized elements are skipped, as in the ordinary `resolve_pda` helper. -/
def seedView (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (args : Args State) (instruction : BytesView State) (seed : Seed ByteResource) :
    Callback.Run State Unit (Except Error (Option (BytesView State))) Unwind Terminal :=
  fun before _ outcome =>
    match seed with
    | .uninitialized => outcome = .returned (.ok none) before
    | .literal resource =>
      ∃ bytes, ops.bytes.current before resource = some bytes ∧
        outcome = .returned (.ok (some
          ⟨bytes.length, fun state => ops.bytes.current state resource⟩)) before
    | .instructionData offset length =>
      ∃ bytes, instruction.observe before = some bytes ∧
        if instruction.length < offset.toNat + length.toNat then
          outcome = .returned (.error Hook.instructionDataTooSmall) before
        else outcome = .returned (.ok (some (instruction.slice offset.toNat length.toNat))) before
    | .accountKey index =>
      ∃ accounts, args.accountsAt before = some accounts ∧
        match accounts[index.toNat]? with
        | none => outcome = .returned (.error Hook.accountNotFound) before
        | some _ => outcome = .returned (.ok (some
            ⟨32, fun state => (accountKeyAt args index.toNat state).map (·.bytes)⟩)) before
    | .accountData index offset length =>
      ∃ accounts, args.accountsAt before = some accounts ∧
        match accounts[index.toNat]? with
        | none => outcome = .returned (.error Hook.accountNotFound) before
        | some (_, none) => outcome = .returned (.error Hook.accountDataNotFound) before
        | some (_, some bytes) =>
          if bytes.length < offset.toNat + length.toNat then
            outcome = .returned (.error Hook.accountDataTooSmall) before
          else
            let parent : BytesView State := ⟨bytes.length, accountDataAt args index.toNat⟩
            outcome = .returned (.ok (some (parent.slice offset.toNat length.toNat))) before

/-- Iterate over the retained seed slice. Its entry length is fixed, while
each element is read in the state after the preceding vector callback. -/
def pushViewsFrom (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (args : Args State) (instruction : BytesView State) (seeds : SeedResource)
    (references : RefResource) (seedCount index : Nat) (before : State)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) : Prop :=
  if index < seedCount then
    ∃ current, ops.seeds.current before seeds = some current ∧ current.length = seedCount ∧
      ∃ seed, current[index]? = some seed ∧
        bindResult (seedView ops args instruction seed)
          (fun view state _ result =>
            match view with
            | none => pushViewsFrom ops args instruction seeds references seedCount
                (index + 1) state result
            | some borrowed =>
              Callback.bind (fun current (_ : Unit) => ops.refs.push current (references, borrowed))
                (fun _ after final => pushViewsFrom ops args instruction seeds references seedCount
                  (index + 1) after final) state () result)
          before () outcome
  else outcome = .returned (.ok ()) before
termination_by seedCount - index
decreasing_by all_goals omega

/-- Read borrowed seed values only at the PDA call, in their recorded order. -/
def readViews (state : State) (views : List (BytesView State)) : Option (List Bytes) :=
  views.mapM (fun view => view.observe state)

/-- The address-library call receives the current referenced bytes and program
key. Its actual returned state, unwind or terminal exit is retained exactly.
The selected dependency is `Address.Syscall.findRun`, including syscall failure
even when a mathematical PDA exists. Only the returned address is copied. -/
def searchPda (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (find : FindPda State Unwind Terminal)
    (programAt : State → Option Solanalib.Runtime.Pubkey) (references : RefResource) :
    Callback.Run State Unit (Except Error Solanalib.Runtime.Pubkey) Unwind Terminal :=
  fun before _ outcome =>
    ∃ views values program, ops.refs.current before references = some views ∧
      readViews before views = some values ∧ programAt before = some program ∧
      Callback.map (fun value => Except.ok value.1) find before ⟨values, program⟩ outcome

/-- A returned address comes from an actual ordinary dependency return with
the same post-state. The seed and program observations describe its call state. -/
theorem searchPda_returned (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (find : FindPda State Unwind Terminal) (programAt : State → Option Solanalib.Runtime.Pubkey)
    (references : RefResource) (before after : State) (key : Solanalib.Runtime.Pubkey)
    (execution : searchPda ops find programAt references before () (.returned (.ok key) after)) :
    ∃ views values program bump, ops.refs.current before references = some views ∧
      readViews before views = some values ∧ programAt before = some program ∧
      find before ⟨values, program⟩ (.returned (key, bump) after) := by
  obtain ⟨views, values, program, current, read, selected, actual, called, mapped⟩ := execution
  cases actual with
  | returned value state =>
    obtain ⟨address, bump⟩ := value
    cases mapped
    exact ⟨views, values, program, bump, current, read, selected, called⟩
  | unwound _ _ => cases mapped
  | terminated _ => cases mapped

/-- Pure search is only a returned-value projection under an explicit provider
law. The conclusion retains the actual dependency post-state and call inputs. -/
theorem searchPda_returned_projection
    (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (find : FindPda State Unwind Terminal) (crypto : Address.Crypto)
    (agreement : NormalFindAgreement find crypto) (programAt : State → Option
      Solanalib.Runtime.Pubkey)
    (references : RefResource) (before after : State) (key : Solanalib.Runtime.Pubkey)
    (execution : searchPda ops find programAt references before () (.returned (.ok key) after)) :
    ∃ views values program bump, ops.refs.current before references = some views ∧
      readViews before views = some values ∧ programAt before = some program ∧
      find before ⟨values, program⟩ (.returned (key, bump) after) ∧
      Address.tryFind ⟨crypto, values, program⟩ = some (key, bump) := by
  obtain ⟨views, values, program, bump, current, read, selected, called⟩ :=
    searchPda_returned ops find programAt references before after key execution
  exact ⟨views, values, program, bump, current, read, selected, called,
    agreement before ⟨values, program⟩ (key, bump) after called⟩

/-- An independent address-call unwind is preserved with its exact actual
state; it is not conditioned on failure of the pure mathematical search. -/
theorem searchPda_unwound (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (find : FindPda State Unwind Terminal) (programAt : State → Option Solanalib.Runtime.Pubkey)
    (references : RefResource) (before after : State) (reason : Unwind)
    (execution : searchPda ops find programAt references before () (.unwound reason after)) :
    ∃ views values program, ops.refs.current before references = some views ∧
      readViews before views = some values ∧ programAt before = some program ∧
      find before ⟨values, program⟩ (.unwound reason after) := by
  obtain ⟨views, values, program, current, read, selected, actual, called, mapped⟩ := execution
  cases actual with
  | returned _ _ => cases mapped
  | unwound actual state =>
    cases mapped
    exact ⟨views, values, program, current, read, selected, called⟩
  | terminated _ => cases mapped

/-- A terminal address exit remains terminal without any synthetic post-state. -/
theorem searchPda_terminated
    (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (find : FindPda State Unwind Terminal) (programAt : State → Option Solanalib.Runtime.Pubkey)
    (references : RefResource) (before : State) (reason : Terminal)
    (execution : searchPda ops find programAt references before () (.terminated reason)) :
    ∃ views values program, ops.refs.current before references = some views ∧
      readViews before views = some values ∧ programAt before = some program ∧
      find before ⟨values, program⟩ (.terminated reason) := by
  obtain ⟨views, values, program, current, read, selected, actual, called, mapped⟩ := execution
  cases actual with
  | returned _ _ => cases mapped
  | unwound _ _ => cases mapped
  | terminated actual =>
    cases mapped
    exact ⟨views, values, program, current, read, selected, called⟩

/-- `resolve_pda` owns its temporary reference vector, but borrows the seed
vector and literal resources. It drops the reference vector on Ok, Err or
unwind before returning to the outer resolver; terminal exits skip that drop. -/
def resolvePda (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (find : FindPda State Unwind Terminal)
    (args : Args State)
    (instruction : BytesView State) (programAt : State → Option Solanalib.Runtime.Pubkey)
    (seeds : SeedResource) : Callback.Run State Unit (Except Error Solanalib.Runtime.Pubkey) Unwind
      Terminal :=
  fun before _ outcome =>
    ∃ current, ops.seeds.current before seeds = some current ∧
      let allocated := ops.refs.empty before
      Owned.scope double [ops.refs.dropAction allocated.1]
        (bindResult
          (fun state (_ : Unit) =>
            pushViewsFrom ops args instruction seeds allocated.1 current.length 0 state)
          (fun _ => searchPda ops find programAt allocated.1)) allocated.2 () outcome

/-- Flags are read after successful PDA-helper cleanup and before the outer
seed-vector destructor. The resolved key has already been copied. -/
def finishMeta (args : Args State) (key : Solanalib.Runtime.Pubkey) :
    Callback.Run State Unit (Except Error Solanalib.Runtime.CpiMeta) Unwind Terminal :=
  fun before _ outcome =>
    ∃ extra, args.extraAt before = some extra ∧
      outcome = .returned (.ok (Solanalib.Specs.Core.Instruction.accountMeta
        key extra.isSigner extra.isWritable)) before

/-- Once the selected program reference is available, unpack the seed vector,
borrow it for PDA resolution, copy the resulting flags, then drop that owner.
Unpack errors have already cleaned their partial vector and do not enter this
scope. The instruction slice keeps the length of the outer source argument. -/
def resolveSelected (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (find : FindPda State Unwind Terminal)
    (args : Args State)
    (programAt : State → Option Solanalib.Runtime.Pubkey) :
    Callback.Run State Unit (Except Error Solanalib.Runtime.CpiMeta) Unwind Terminal :=
  fun before _ outcome =>
    ∃ instruction, args.instructionAt before = some instruction ∧
      let view : BytesView State := ⟨instruction.length, args.instructionAt⟩
      bindResult (unpack ops double (fun state => (args.extraAt state).map (·.configuration)))
        (fun seeds => Owned.scope double [ops.seeds.dropAction seeds]
          (bindResult (resolvePda ops double find args view programAt seeds)
            (finishMeta args))) before () outcome

/-- The ordinary PubkeyData branch has no vector dependency. Only byte sources
selected by the decoded configuration are observed. The bounds checks precede
the fixed-width key conversion, so conversion unwraps cannot fail here. -/
def resolveKeyData (args : Args State) (configuration : Solanalib.Runtime.Pubkey) :
    Callback.Run State Unit (Except Error Solanalib.Runtime.Pubkey) Unwind Terminal :=
  fun before _ outcome =>
    match configuration.bytes with
    | 1 :: index :: _ =>
      ∃ instruction, args.instructionAt before = some instruction ∧
        outcome = .returned
          (if index.toNat + 32 ≤ instruction.length then
            .ok (.ofBytes (Solanalib.Runtime.slice instruction index.toNat 32))
          else .error Hook.instructionDataTooSmall) before
    | 2 :: index :: offset :: _ =>
      ∃ accounts, args.accountsAt before = some accounts ∧
        outcome = .returned
          (match accounts[index.toNat]? with
          | none => .error Hook.accountNotFound
          | some (_, none) => .error Hook.accountDataNotFound
          | some (_, some bytes) =>
            if offset.toNat + 32 ≤ bytes.length then
              .ok (.ofBytes (Solanalib.Runtime.slice bytes offset.toNat 32))
            else .error Hook.accountDataTooSmall) before
    | 1 :: _ | 2 :: _ => outcome = .returned (.error Hook.invalidPubkeyBytes) before
    | _ => outcome = .returned (.error .InvalidAccountData) before

/-- The complete ordinary `ExtraAccountMeta::resolve` allocation flow for
account-resolution 0.11.1 and the selected pure account-observation closure.
External-program lookup precedes any seed decoding or vector construction.
Static and PubkeyData branches remain allocation-free. Every allocator,
destructor and address dependency retains all of its finite outcomes and states.
An absent required observation has no modeled finite exit.

This is a dependency-composed mathematical model, not a Rust body proof.
Provider ownership, stable borrowed identities, target scalar bounds and the
binding of the selected closure remain explicit source obligations. -/
def resolve (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal) (find : FindPda State Unwind Terminal)
    (args : Args State) :
    Callback.Run State Unit (Except Error Solanalib.Runtime.CpiMeta) Unwind Terminal :=
  fun before _ outcome =>
    ∃ extra, args.extraAt before = some extra ∧
      let tag := extra.discriminator.toNat
      if tag = 0 then
        outcome = .returned (.ok (Solanalib.Specs.Core.Instruction.accountMeta
          extra.configuration extra.isSigner extra.isWritable)) before
      else if tag = 1 then
        ∃ program, args.programAt before = some program ∧
          resolveSelected ops double find args args.programAt before () outcome
      else if 128 ≤ tag then
        ∃ accounts, args.accountsAt before = some accounts ∧
          match accounts[tag - 128]? with
          | none => outcome = .returned (.error Hook.accountNotFound) before
          | some _ => resolveSelected ops double find args
              (accountKeyAt args (tag - 128)) before () outcome
      else if tag = 2 then
        bindResult (resolveKeyData args extra.configuration) (finishMeta args) before () outcome
      else outcome = .returned (.error .InvalidAccountData) before

end Solanalib.Specs.Core.Token.AllocatedSeeds
