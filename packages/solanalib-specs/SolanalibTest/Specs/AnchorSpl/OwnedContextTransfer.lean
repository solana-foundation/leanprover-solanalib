/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorSpl.Token
public import Solanalib.Specs.AnchorLang.context

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorSpl.OwnedContextTransfer

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTransfer

def contextTypes : AnchorContextOwned.Types where
  State := Sample.State
  Accounts := AnchorSpl.TransferAccounts
  Resource := Nat
  Unwind := Nat
  Terminal := Nat
  remaining := Sample.remainingOps

def contextArgs : AnchorContext.NewWithSignerArgs contextTypes.Accounts :=
  ⟨.ofNat 99, Sample.args.context.accounts, Sample.args.context.signerSeeds⟩
def beforeContext : Sample.State :=
  (([], []), { Sample.auxiliary with remaining := [] })
def constructed := AnchorContextOwned.newWithSigner contextTypes beforeContext contextArgs
def args : Args Sample.resources := ⟨constructed.1, 42⟩
def built : Sample.State := (Sample.builtState.1, constructed.2.2)
def invoked : Sample.State := (built.1, { built.2 with calls := [Sample.call] })
def boxed := AnchorErrorOwned.Reference.fromProgramResult invoked.2.errors .insufficientFunds
def afterBox : Sample.State := Sample.errorsFocus.set invoked boxed.2
def afterMetas : Sample.State := ((afterBox.1.1, [none]), afterBox.2)
def afterBytes : Sample.State := (([none], [none]), afterBox.2)
def afterAccounts : Sample.State :=
  Sample.afterInfo (Sample.afterInfo (Sample.afterInfo afterBytes (Sample.info 1))
    (Sample.info 2)) (Sample.info 3)
def finalState : Sample.State := Sample.remainingFocus.set afterAccounts [none]

/-- The exact versioned constructor returns the resource subsequently moved
into the transfer call, using the same state and dependency interpretation. -/
theorem constructor_post :
    (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_contract.contract
      contextTypes).post
      beforeContext contextArgs (.returned constructed.1 constructed.2) :=
  AnchorContextOwned.realizes contextTypes beforeContext contextArgs
    ⟨Sample.remainingOps_laws.empty_current beforeContext,
      Sample.remainingOps_laws.empty_fresh beforeContext⟩

theorem builder_returns : Token.InstructionAllocated.run Sample.resources.builder constructed.2
  (plan args)
    (.returned (.ok Sample.instruction) built) :=
  VectorSample.run_returns (plan args) constructed.2.2 (plan_admitted args)

theorem invocation_returns : invokeAndConvert Sample.types args Sample.instruction built ()
    (.returned (.error boxed.1) afterBox) := by
  refine ⟨.returned (.error .insufficientFunds) invoked, rfl, ?_⟩
  refine ⟨.returned boxed.1 afterBox, ?_, rfl⟩
  refine ⟨.returned boxed.1 afterBox, ?_, rfl⟩
  exact AnchorErrorOwned.fromProgram_focus_returned AnchorErrorOwned.Reference.natOps
    Sample.errorsFocus
    invoked .insufficientFunds boxed.1 boxed.2
    (AnchorErrorOwned.Reference.fromProgram_returns_nat invoked.2.errors .insufficientFunds (by
      decide))

theorem cleanup_returns :
    Owned.DropReturns (invocationDrops args Sample.instruction) afterBox finalState := by
  refine .cons _ _ _ afterMetas finalState ?_ ?_
  · exact ⟨.returned () (afterBox.1.1, [none]),
      Token.InstructionAllocated.Witness.metas_drop _ _, rfl⟩
  refine .cons _ _ _ afterBytes finalState ?_ ?_
  · exact ⟨.returned () ([none], [none]),
      Token.InstructionAllocated.Witness.bytes_drop _ _, rfl⟩
  refine .cons _ _ _ (Sample.afterInfo afterBytes (Sample.info 1)) finalState
    (Sample.sdk_info_drop _ _) ?_
  refine .cons _ _ _ (Sample.afterInfo (Sample.afterInfo afterBytes (Sample.info 1))
    (Sample.info 2)) finalState (Sample.sdk_info_drop _ _) ?_
  refine .cons _ _ _ afterAccounts finalState (Sample.sdk_info_drop _ _) ?_
  exact .cons _ _ _ finalState finalState (Sample.remaining_drop afterAccounts [] rfl) (.nil _)

/-- Model composition consumes the exact vector owner of the constructor. The
request retains its three moved accounts and seeds; all temporary resources
retire while the boxed invocation error remains live. -/
theorem constructor_then_transfer :
    (Solanalib.Specs.AnchorSpl.token.transfer_contract.contract Sample.types).post constructed.2
      args
      (.returned (.error boxed.1) finalState) :=
  run_after_build Sample.types args constructed.2 built Sample.instruction _ _ builder_returns
    invocation_returns (cleanup_returns.cleanup_returned _ (Except.error boxed.1))

/-- The exact constructed context also satisfies the reached transfer domain;
all successful vector-builder returns have both current observations. -/
theorem constructed_context_transfer_admitted :
    (Solanalib.Specs.AnchorSpl.token.transfer_contract.contract Sample.types).requires
      constructed.2 args ∧
    (Solanalib.Specs.AnchorSpl.token.transfer_contract.contract Sample.types).post constructed.2
      args
      (.returned (.error boxed.1) finalState) :=
  ⟨Sample.build_ready constructed.2.2 args, constructor_then_transfer⟩

theorem exact_cleanup_and_error :
    Sample.remainingOps.current finalState constructed.1.remaining = none ∧
    AnchorErrorOwned.current Sample.types.errors finalState boxed.1 =
      some (AnchorAccount.programError .insufficientFunds) ∧
    finalState.2.rcEvents = Sample.infoEvents (Sample.info 1) ++
      Sample.infoEvents (Sample.info 2) ++ Sample.infoEvents (Sample.info 3) ∧
    finalState.2.calls = [Sample.call] := ⟨rfl, rfl, rfl, rfl⟩

end SolanalibTest.Specs.AnchorSpl.OwnedContextTransfer
