/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionSize
public import Solanalib.Specs.Core.TokenExtensionFee
public import Solanalib.Specs.Core.TokenExtensionGetter
public import Solanalib.Specs.Core.TokenExtensionListReference
public import Solanalib.Specs.Core.TokenExtensionListFrame
public import Solanalib.Specs.Core.TokenExtensionUnpackFacts
public import Solanalib.Specs.Core.TokenExtensionLegacyFamilies

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022Interface.extension

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

/-- Immutable observations of the base association and the exact TLV slice.
The source binding establishes its reference, lifetime and pointer provenance. -/
structure ExtensionSlice where
  /-- The source S::ACCOUNT_TYPE association. -/
  accountType : ExtensionAccountType
  /-- Mathematical address bits used by the Pod alignment check. -/
  address : Nat
  /-- The bytes returned by self.get_tlv_data(). -/
  bytes : Bytes
  deriving DecidableEq, Repr

namespace BaseStateWithExtensions

/-- Default-lookup Pod retrieval. The index records the layout and logical value
observation of V; raw selected bytes and reference offset remain in the result.
Base association, first-match lookup, bounds, exact size and alignment checks
precede that observation, with their original ordinary errors. -/
def get_extension_contract : Family where
  Index := ExtensionRepresentation
  State := fun _ => ExtensionSlice
  Args := fun _ => Unit
  Value := fun representation => Except Error (ExtensionReference representation.Value)
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun representation => .returning
    (fun _ _ => True)
    (fun before _ result after =>
      result = getRepresentedExtension representation before.accountType before.address
        before.bytes ∧ after = before)

/-- The total mathematical family of typed extension observations. -/
def get_extension_run : FamilyRun get_extension_contract := fun representation =>
  returnsOf fun before _ =>
    (getRepresentedExtension representation before.accountType before.address before.bytes, before)

/-- One reference proof covers every source Pod representation index. -/
theorem get_extension_reference :
    FamilyReference get_extension_contract get_extension_run := by
  intro representation
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro before args precondition
  exact ⟨rfl, rfl⟩

/-- The registered sample is the actual fixed fee-configuration representation. -/
def get_extension_sample : get_extension_contract.Index := transferFeeConfigRepresentation

/-- A complete zero-filled fee TLV, used only as a mathematical witness. -/
def feeExtensionSample : ExtensionSlice :=
  ⟨.mint, 4096, [1, 0, 108, 0] ++ List.replicate 108 0⟩

/-- Typed extension retrieval has a concrete admitted state and layout. -/
theorem get_extension_satisfiable :
    FamilySatisfiable get_extension_contract get_extension_sample :=
  ⟨feeExtensionSample, (), trivial⟩

/-- The registered reference has an actual finite execution on a complete
fee TLV; its decoded success is additionally checked in the model controls. -/
theorem get_extension_has_execution :
    FamilyHasExecution get_extension_contract get_extension_run get_extension_sample := by
  refine ⟨feeExtensionSample, (),
    .returned (getTransferFeeConfig feeExtensionSample.address feeExtensionSample.bytes)
      feeExtensionSample, ?_, ?_⟩
  · trivial
  · rfl

/-- Primary generic getter: invoke the actual resolved byte-retrieval method,
including trait overrides, then perform the source Pod cast. Every dependency
exit and state is preserved, and a success retains its reference identity. -/
def get_extension_operational_contract : Family where
  Index := ExtensionGetter
  State := fun getter => getter.provider.State
  Args := fun _ => Unit
  Value := fun getter => Except Error
    (TypedExtensionReference getter.provider.Reference getter.representation.Value)
  Unwind := fun getter => getter.provider.Unwind
  Terminal := fun getter => getter.provider.Terminal
  contract := fun getter =>
    { requires := fun _ _ => True
      post := fun before _ => getExtensionOperational getter.provider getter.representation before }

/-- Reference composition over all resolved method interpretations. -/
def get_extension_operational_run : FamilyRun get_extension_operational_contract :=
  fun getter before _ => getExtensionOperational getter.provider getter.representation before

/-- Closed reference correctness for the entire operational getter family. -/
theorem get_extension_operational_reference :
    FamilyReference get_extension_operational_contract get_extension_operational_run := by
  intro getter before args outcome precondition execution
  exact execution

/-- Actual default retrieval of TransferFeeConfig supplies the sample provider. -/
def get_extension_operational_sample : get_extension_operational_contract.Index :=
  ⟨transferFeeConfigRepresentation, defaultExtensionByteProvider⟩

/-- The operational sample uses the same complete fee TLV as the pure control. -/
def feeOperationalReceiver : ExtensionReceiver :=
  ⟨feeExtensionSample.accountType, feeExtensionSample.address, feeExtensionSample.bytes⟩

/-- The generic operational precondition has a concrete admitted receiver. -/
theorem get_extension_operational_satisfiable :
    FamilySatisfiable get_extension_operational_contract get_extension_operational_sample :=
  ⟨feeOperationalReceiver, (), trivial⟩

/-- The sample executes actual default byte lookup followed by its Pod cast. -/
theorem get_extension_operational_has_execution :
    FamilyHasExecution get_extension_operational_contract get_extension_operational_run
      get_extension_operational_sample := by
  refine ⟨feeOperationalReceiver, (),
    .returned (getDefaultExtension transferFeeConfigRepresentation feeOperationalReceiver)
      feeOperationalReceiver, ?_, ?_⟩
  · trivial
  · exact getDefaultExtension_execution transferFeeConfigRepresentation feeOperationalReceiver

/-- Pure ordered-list observation, preserving duplicates and source TLV
admission. The operational family below additionally exposes vector effects. -/
def get_extension_types_contract : Solanalib.Contracts.Model Bytes Unit (Except Error (List
  ExtensionType)) :=
  .returning (fun _ _ => True)
    (fun before _ result after => result = getExtensionTypes before ∧ after = before)

/-- Total immutable reference for extension-type listing. -/
def getExtensionTypesReference (before : Bytes) (_args : Unit) :
    Except Error (List ExtensionType) × Bytes := (getExtensionTypes before, before)

/-- Closed correctness of the mathematical list reference. -/
theorem get_extension_types_reference :
    get_extension_types_contract.RealizedBy getExtensionTypesReference := by
  intro before args precondition
  exact ⟨rfl, rfl⟩

/-- The type-listing precondition is inhabited. -/
theorem get_extension_types_satisfiable : get_extension_types_contract.Satisfiable :=
  ⟨[], (), trivial⟩

/-- Primary generic listing: call the resolved accessor, construct an empty
vector, validate each entry and invoke one actual push, then move or clean that
same vector as source control flow requires. Bytes are read from actual states. -/
def get_extension_types_operational_contract : Family where
  Index := CurrentExtensionTypeReader
  State := CurrentExtensionTypeReader.State
  Args := fun _ => Unit
  Value := fun reader => Except Error reader.Resource
  Unwind := CurrentExtensionTypeReader.Unwind
  Terminal := CurrentExtensionTypeReader.Terminal
  contract := fun reader =>
    { requires := fun _ _ => True
      post := fun before _ => getExtensionTypesCurrent reader before }

/-- Reference composition through each selected accessor and vector provider. -/
def get_extension_types_operational_run : FamilyRun get_extension_types_operational_contract :=
  fun reader before _ => getExtensionTypesCurrent reader before

/-- Closed correctness for every operational type-listing instantiation. -/
theorem get_extension_types_operational_reference :
    FamilyReference get_extension_types_operational_contract get_extension_types_operational_run :=
      by
  intro reader before args outcome _ execution
  exact execution

/-- A concrete vector-ledger provider and complete nonempty TLV instantiate
the operational family without any assumed successful callback result. -/
def get_extension_types_operational_sample : get_extension_types_operational_contract.Index :=
  extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty)
    extensionListSample

/-- The concrete reader supplies an admitted caller for the operational family. -/
theorem get_extension_types_operational_satisfiable :
    FamilySatisfiable get_extension_types_operational_contract
      get_extension_types_operational_sample :=
  ⟨[], (), trivial⟩

/-- Nonvacuity includes empty construction, two actual pushes and transfer of
the resulting live vector, rather than merely admitting an error return. -/
theorem get_extension_types_operational_has_execution :
    FamilyHasExecution get_extension_types_operational_contract get_extension_types_operational_run
      get_extension_types_operational_sample :=
  ⟨[], (), .returned (.ok (0 : Nat)) [some extensionListSampleValues],
    trivial, extensionListSample_executes⟩

end BaseStateWithExtensions

namespace StateWithExtensions

/-- Supporting value observation of parsing and extension-layout checks for
an immutable byte input and trivial base destruction. All parser exits remain
explicit. The operational family below adds generic S destruction, live reads
and retained input-region identity. -/
def unpack_contract : Family where
  Index := ExtensionBaseParser
  State := ExtensionBaseParser.State
  Args := fun _ => Bytes
  Value := fun parser => Except Error (Solanalib.Specs.Core.Token.StateWithExtensions parser.Value)
  Unwind := ExtensionBaseParser.Unwind
  Terminal := ExtensionBaseParser.Terminal
  contract := fun parser =>
    { requires := fun _ _ => True
      post := unpackExtensionState parser }

/-- The reference relation invokes the indexed parser on the exact base prefix. -/
def unpack_run : FamilyRun unpack_contract := unpackExtensionState

/-- Closed reference correctness for every base type and callback relation. -/
theorem unpack_reference : FamilyReference unpack_contract unpack_run := by
  intro parser before bytes outcome precondition execution
  exact execution

/-- The nonvacuity sample instantiates S with the actual packed Mint codec. -/
def unpack_sample : unpack_contract.Index := mintExtensionParser

/-- A valid initialized base Mint with absent authorities and zero supply. -/
def initializedMintSample : Bytes := List.replicate 45 0 ++ [1] ++ List.replicate 36 0

/-- The source-facing unpack family has a concrete admissible Mint input. -/
theorem unpack_satisfiable : FamilySatisfiable unpack_contract unpack_sample :=
  ⟨(), initializedMintSample, trivial⟩

/-- The closed sample runs the actual shared Mint decoder, rather than an
unconstrained successful callback assumption. -/
theorem unpack_has_execution : FamilyHasExecution unpack_contract unpack_run unpack_sample := by
  refine ⟨(), initializedMintSample, .returned (unpackMintWithExtensions initializedMintSample) (),
    ?_, ?_⟩
  · trivial
  · exact unpackStateWithExtensions_execution mintLength .mint unpackMint initializedMintSample

/-- Primary generic unpacking with the resolved parser, source slice identity
and actual destructor. A parsed base is moved to the result or destroyed after
a layout failure; parser and destructor abnormal exits retain their states. -/
def unpack_operational_contract : Family where
  Index := ExtensionUnpacker
  State := ExtensionUnpacker.State
  Args := ExtensionUnpacker.Reference
  Value := fun unpacker => Except Error (ExtensionUnpacked unpacker.Base unpacker.Reference)
  Unwind := ExtensionUnpacker.Unwind
  Terminal := ExtensionUnpacker.Terminal
  contract := fun unpacker =>
    { requires := fun _ _ => True
      post := unpackExtensionOperational unpacker }

/-- Reference relation over every resolved parser and destructor interpretation. -/
def unpack_operational_run : FamilyRun unpack_operational_contract := unpackExtensionOperational

/-- Closed reference correctness covers the full operational family. -/
theorem unpack_operational_reference :
    FamilyReference unpack_operational_contract unpack_operational_run := by
  intro unpacker before input outcome precondition execution
  exact execution

/-- The shared Mint codec and its actual trivial destructor instantiate the
generic model; arbitrary source S values retain their supplied destructor. -/
def unpack_operational_sample : unpack_operational_contract.Index := mintExtensionUnpacker

/-- A complete initialized Mint inhabits the operational precondition. -/
theorem unpack_operational_satisfiable :
    FamilySatisfiable unpack_operational_contract unpack_operational_sample :=
  ⟨(), initializedMintSample, trivial⟩

/-- The concrete sample actually runs the Mint parser and retains the source
empty-tail reference, with no assumed successful parser outcome. -/
theorem unpack_operational_has_execution :
    FamilyHasExecution unpack_operational_contract unpack_operational_run unpack_operational_sample
      := by
  refine ⟨(), initializedMintSample,
    .returned (unpackDroplessExtension mintLength .mint unpackMint initializedMintSample) (), ?_,
      ?_⟩
  · trivial
  · exact unpackDroplessExtension_executes mintLength .mint unpackMint initializedMintSample

end StateWithExtensions

namespace account_len

/-- Raw mint data and additional account extension types, in supplied order. -/
structure Arguments where
  /-- Raw bytes of the mint, before PodMint/layout admission. -/
  mintData : Bytes
  /-- Requested account extensions, retaining order and duplicates. -/
  additional : List ExtensionType
  deriving DecidableEq, Repr

/-- Size the mint-required and requested account extensions, with source error
precedence, PodMint admission, bounded TLV values, deduplication and multisig
adjustment. Ownership and extension semantic validity are not invented here. -/
def try_calculate_account_len_from_mint_data_contract :
    Solanalib.Contracts.Model Unit Arguments (Except Error Nat) :=
  .returning
    (fun _ _ => True)
    (fun before args result after =>
      result = calculateAccountLengthFromMint args.mintData args.additional ∧ after = before)

/-- Total mathematical reference of the exact account-length calculation. -/
def calculateAccountLengthReference (before : Unit) (args : Arguments) : Except Error Nat × Unit :=
  (calculateAccountLengthFromMint args.mintData args.additional, before)

/-- Closed realization of the versioned size contract. -/
theorem try_calculate_account_len_from_mint_data_reference :
    try_calculate_account_len_from_mint_data_contract.RealizedBy calculateAccountLengthReference :=
      by
  intro before args precondition
  exact ⟨rfl, rfl⟩

/-- A concrete initialized mint admits the size contract. -/
theorem try_calculate_account_len_from_mint_data_satisfiable :
    try_calculate_account_len_from_mint_data_contract.Satisfiable :=
  ⟨(), ⟨StateWithExtensions.initializedMintSample, []⟩, trivial⟩

end account_len

end Solanalib.Specs.SplToken2022Interface.extension

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solanalib.Specs.SplToken2022Interface.extension

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

namespace StateWithExtensions

/-- Version 2.1.0 accepts an empty extended TLV tail while retaining its padding-vector allocation.
-/
def unpack_owned_base_contract : Family := Legacy.unpackFamily false

/-- The full operational reference for the selected source version. -/
def unpack_owned_base_run : FamilyRun unpack_owned_base_contract := Legacy.unpackRun false

/-- Closed correctness retains every dependency interpretation. -/
theorem unpack_owned_base_reference : FamilyReference unpack_owned_base_contract
  unpack_owned_base_run := Legacy.unpack_reference false

/-- A concrete interpretation with an actual successful execution. -/
def unpack_owned_base_sample : unpack_owned_base_contract.Index := Legacy.mintUnpacker

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem unpack_owned_base_has_execution :
    FamilyHasExecution unpack_owned_base_contract unpack_owned_base_run unpack_owned_base_sample :=
      Legacy.unpack_execution false

/-- The same actual execution supplies an admitted caller. -/
theorem unpack_owned_base_satisfiable : FamilySatisfiable unpack_owned_base_contract
  unpack_owned_base_sample := by
  rcases unpack_owned_base_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end StateWithExtensions

end Solanalib.Specs.SplToken2022Interface.extension

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solanalib.Specs.SplToken2022Interface.extension

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

namespace BaseStateWithExtensions

/-- The reviewed old scanner retains its push-before-payload-validation ordering. -/
def get_extension_types_push_before_payload_contract : Family := Legacy.typesFamily

/-- The full operational reference for the selected source version. -/
def get_extension_types_push_before_payload_run : FamilyRun
  get_extension_types_push_before_payload_contract := Legacy.typesRun

/-- Closed correctness retains every dependency interpretation. -/
theorem get_extension_types_push_before_payload_reference : FamilyReference
  get_extension_types_push_before_payload_contract get_extension_types_push_before_payload_run :=
  Legacy.types_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_extension_types_push_before_payload_sample :
  get_extension_types_push_before_payload_contract.Index := Legacy.typesSample

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_extension_types_push_before_payload_has_execution :
    FamilyHasExecution get_extension_types_push_before_payload_contract
      get_extension_types_push_before_payload_run get_extension_types_push_before_payload_sample :=
      Legacy.types_execution

/-- The same actual execution supplies an admitted caller. -/
theorem get_extension_types_push_before_payload_satisfiable : FamilySatisfiable
  get_extension_types_push_before_payload_contract get_extension_types_push_before_payload_sample
  := by
  rcases get_extension_types_push_before_payload_has_execution with ⟨before, args, outcome,
    admitted, execution⟩
  exact ⟨before, args, admitted⟩

end BaseStateWithExtensions

namespace ExtensionType

/-- The reviewed fixed-size calculation deduplicates first, then validates and drops its vector. -/
def try_calculate_account_len_contract : Family := Legacy.sizeFamily

/-- The full operational reference for the selected source version. -/
def try_calculate_account_len_run : FamilyRun try_calculate_account_len_contract := Legacy.sizeRun

/-- Closed correctness retains every dependency interpretation. -/
theorem try_calculate_account_len_reference : FamilyReference try_calculate_account_len_contract
  try_calculate_account_len_run := Legacy.size_reference

/-- A concrete interpretation with an actual successful execution. -/
def try_calculate_account_len_sample : try_calculate_account_len_contract.Index := Legacy.sizeSample

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem try_calculate_account_len_has_execution :
    FamilyHasExecution try_calculate_account_len_contract try_calculate_account_len_run
      try_calculate_account_len_sample := Legacy.size_execution

/-- The same actual execution supplies an admitted caller. -/
theorem try_calculate_account_len_satisfiable : FamilySatisfiable
  try_calculate_account_len_contract try_calculate_account_len_sample := by
  rcases try_calculate_account_len_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

/-- Individual required-extension pushes preserve input order and duplicates. -/
def get_required_init_account_extensions_contract : Family := Legacy.requiredFamily

/-- The full operational reference for the selected source version. -/
def get_required_init_account_extensions_run : FamilyRun
  get_required_init_account_extensions_contract := Legacy.requiredRun

/-- Closed correctness retains every dependency interpretation. -/
theorem get_required_init_account_extensions_reference : FamilyReference
  get_required_init_account_extensions_contract get_required_init_account_extensions_run :=
  Legacy.required_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_required_init_account_extensions_sample :
  get_required_init_account_extensions_contract.Index := Legacy.typeArrayReference

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_required_init_account_extensions_has_execution :
    FamilyHasExecution get_required_init_account_extensions_contract
      get_required_init_account_extensions_run get_required_init_account_extensions_sample :=
      Legacy.required_execution

/-- The same actual execution supplies an admitted caller. -/
theorem get_required_init_account_extensions_satisfiable : FamilySatisfiable
  get_required_init_account_extensions_contract get_required_init_account_extensions_sample := by
  rcases get_required_init_account_extensions_has_execution with ⟨before, args, outcome, admitted,
    execution⟩
  exact ⟨before, args, admitted⟩

end ExtensionType

end Solanalib.Specs.SplToken2022Interface.extension
