/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram
import Solanalib.Specs.SolanaLoaderV3Interface
import Solanalib.Specs.SplAssociatedTokenAccountInterface
import SolanalibTest.Conformance.Library.Families.AddressProfiles.Io
import Solanalib.Specs.SolanaPubkey
import Solanalib.Specs.SplAssociatedTokenAccountClient

/-! Native comparisons cover value operations, PDA creation/search, seed
derivation and Borsh codecs for the exact profiles listed in `corpora`.
The function-provider equivalences are proved in Evaluation and Io; the
concrete test callbacks retain the full observed state. Native selection
keeps the recorded source/build identities. These tests do not select a
production Borsh implementation. -/

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.SplAssociatedTokenAccountClient
open Solanalib.Specs.SplAssociatedTokenAccountInterface

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
  Solanalib.Specs.Core.Address.Syscall
open Solanalib.Specs.Core.Address.Operations
open Address (valueChecker pubkey pubkeyJson array32 array32Json selfArg pairArg arrayArg asBool
  asFound foundJson)

/-- A direct registered finite-exit relation at a deterministic test callback. -/
def runtimeChecker {Args V : Type} [DecidableEq V] (function reference : String)
    (run : Shim.State → Args → Shim.Exit V → Prop)
    (compute : Shim.State → Args → Shim.Exit V)
    (graph : ∀ before args o, run before args o ↔ compute before args = o)
    (args : Json → Result Args) (value : Json → Result V) (render : V → Json) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    let before ← Shim.state c.state
    let input ← args c.args
    pure (decideGraph (run before input) (compute before input) (graph before input)
      (some (← Shim.exit value c.outcome)) (Shim.exitJson render))

def createChecker (function reference : String) (mode : Initialization) (profile : ErrorProfile)
    (run : Shim.State → PdaInputs → Shim.Exit (Except Error Value) → Prop)
    (precondition : Shim.State → PdaInputs → Prop)
    (graph : ∀ before inputs o, run before inputs o ↔
      Evaluation.createEval profile (Shim.createProvider mode) Shim.stringPanic before inputs =
        some o)
    (admission : ∀ before inputs, precondition before inputs ↔
      Evaluation.createReadyB mode (Shim.createProvider mode) before inputs = true) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  decidesRequires := [reference]
  check := fun c => do
    let before ← Shim.state c.state
    let inputs ← Address.Syscall.pdaInputs c.args
    Shim.checkAdmission (precondition before inputs) _ (admission before inputs)
    pure (Shim.decideOpt (run before inputs)
      (Evaluation.createEval profile (Shim.createProvider mode) Shim.stringPanic before inputs)
      (graph before inputs) (← Shim.exit Shim.result c.outcome) Shim.resultJson)

def ordering (j : Json) : Result Ordering := do
  match ← j.getStr? with
  | "Less" => pure .lt
  | "Equal" => pure .eq
  | "Greater" => pure .gt
  | other => throw s!"unknown Ordering {other}"

def orderingJson : Ordering → Json
  | .lt => "Less"
  | .eq => "Equal"
  | .gt => "Greater"

def method (key method : String) : String := s!"{key}::{method}"
def traitMethod (key trait method : String) : String := s!"<{key} as {trait}>::{method}"

def PUBKEY := "solana_pubkey::Pubkey"
def ATA_CLIENT :=
  "spl_associated_token_account_client::address::get_associated_token_address_with_program_\
    id"
namespace Pubkey
open Solanalib.Specs.SolanaPubkey.Pubkey

def values : List Checker := [
  valueChecker (method PUBKEY "new_from_array")
    "Solanalib.Specs.SolanaPubkey.Pubkey.new_from_array_model"
    new_from_array_model arrayArg pubkey pubkeyJson,
  valueChecker (traitMethod PUBKEY "core::convert::From<[u8; 32]>" "from")
    "Solanalib.Specs.SolanaPubkey.Pubkey.from_model"
    from_model arrayArg pubkey pubkeyJson,
  valueChecker (method PUBKEY "to_bytes") "Solanalib.Specs.SolanaPubkey.Pubkey.to_bytes_mod\
    el"
    to_bytes_model selfArg array32 array32Json,
  valueChecker (traitMethod PUBKEY "core::convert::AsRef<[u8]>" "as_ref")
    "Solanalib.Specs.SolanaPubkey.Pubkey.as_ref_model"
    as_ref_model selfArg asBytes bytesJson,
  valueChecker (traitMethod PUBKEY "core::default::Default" "default")
    "Solanalib.Specs.SolanaPubkey.Pubkey.default_model"
    default_model asUnit pubkey pubkeyJson,
  valueChecker (traitMethod PUBKEY "core::clone::Clone" "clone")
    "Solanalib.Specs.SolanaPubkey.Pubkey.clone_model"
    clone_model selfArg pubkey pubkeyJson,
  valueChecker (traitMethod PUBKEY "core::cmp::PartialEq" "eq")
    "Solanalib.Specs.SolanaPubkey.Pubkey.eq_model"
    eq_model pairArg asBool toJson,
  valueChecker (traitMethod PUBKEY "core::cmp::Ord" "cmp")
    "Solanalib.Specs.SolanaPubkey.Pubkey.cmp_model"
    cmp_model pairArg ordering orderingJson]

def pda : List Checker := [
  createChecker (method PUBKEY "create_program_address")
    "Solanalib.Specs.SolanaPubkey.Pubkey.create_program_address_solana_run"
    .zeroed .pubkey (create_program_address_solana_run (Shim.createIndex .zeroed))
    (create_program_address_solana_contract.contract (Shim.createIndex .zeroed)).requires
    (Evaluation.createRun_ofFunction .pubkey (Shim.createProvider .zeroed) Shim.stringPanic)
    (Evaluation.createReady_ofFunction .zeroed (Shim.createProvider .zeroed) Shim.stringPanic),
  runtimeChecker (V := Value × UInt8) (method PUBKEY "find_program_address")
    "Solanalib.Specs.SolanaPubkey.Pubkey.find_program_address_solana_run"
    (find_program_address_solana_run Shim.zeroFindIndex)
    (Evaluation.zeroFindEval Shim.zeroFindProvider Shim.searchPanic)
    (Evaluation.zeroFindRun_ofFunction Shim.zeroFindProvider Shim.searchPanic)
    Address.Syscall.pdaInputs asFound foundJson,
  runtimeChecker (V := Except Error Value) (method PUBKEY "create_with_seed")
    "Solanalib.Specs.SolanaPubkey.Pubkey.create_with_seed_run"
    (create_with_seed_run Shim.seedIndex) (Evaluation.seedEval Shim.hashProvider)
    (Evaluation.seedRun_ofFunction Shim.hashProvider) Shim.seedInputs Shim.result Shim.resultJson]

def io : List Checker := [
  Io.writerChecker (traitMethod PUBKEY "borsh::ser::BorshSerialize" "serialize")
    "Solanalib.Specs.SolanaPubkey.Pubkey.serialize_run"
    (serialize_run Io.writeIndex) Io.serializeRun_evaluated,
  Io.readerChecker (traitMethod PUBKEY "borsh::de::BorshDeserialize" "deserialize_reader")
    "Solanalib.Specs.SolanaPubkey.Pubkey.deserialize_reader_run" .invalidInput
    (deserialize_reader_run Io.readIndex) (Io.readRun_evaluated .invalidInput)]

end Pubkey

namespace Program

end Program

namespace AddressValue

end AddressValue

namespace Derived

def client : Checker :=
  runtimeChecker (V := Value) ATA_CLIENT
    "Solanalib.Specs.SplAssociatedTokenAccountClient.address.get_associated_token_address_w\
      ith_program_id_run"
    (address.get_associated_token_address_with_program_id_run Shim.zeroFindIndex)
    (fun before args => Outcome.map Prod.fst (Evaluation.zeroFindEval Shim.zeroFindProvider
      Shim.searchPanic
      before (associatedInputs args)))
    (Evaluation.zeroDerivedRun_ofFunction associatedInputs Shim.zeroFindProvider Shim.searchPanic)
    Shim.associatedArgs pubkey pubkeyJson

end Derived

end SolanalibTest.Conformance.Library.Families.AddressProfiles

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
  Solanalib.Specs.Core.Address.Syscall
open Solanalib.Specs.Core.Address.Operations
open Address (valueChecker pubkey pubkeyJson array32 array32Json selfArg pairArg arrayArg asBool
  asFound foundJson)

def uninitDerivedChecker {Args : Type} (function reference : String) (inputs : Args → PdaInputs)
    (run : Shim.State → Args → Shim.Exit Value → Prop)
    (precondition : Shim.State → Args → Prop)
    (graph : ∀ before args o, run before args o ↔
      (Address.Syscall.findOutcome Shim.searchPanic (Shim.uninitFindProvider before (pdaRequest
        (inputs args)))).map
        (Outcome.map Prod.fst) = some o)
    (admission : ∀ before args, precondition before args ↔
      Address.Syscall.successInitializedB (Shim.uninitFindProvider before (pdaRequest (inputs
        args))) = true)
    (args : Json → Result Args) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  decidesRequires := [reference]
  check := fun c => do
    let before ← Shim.state c.state
    let input ← args c.args
    Shim.checkAdmission (precondition before input) _ (admission before input)
    pure (Shim.decideOpt (run before input)
      ((Address.Syscall.findOutcome Shim.searchPanic (Shim.uninitFindProvider before (pdaRequest
        (inputs input)))).map
        (Outcome.map Prod.fst))
      (graph before input) (← Shim.exit pubkey c.outcome) pubkeyJson)

def ADDRESS := "solana_address::Address"
def ADDRESS_CREATE :=
  "solana_address::syscalls::<impl solana_address::Address>::create_program_address"
def LOADER := "solana_loader_v3_interface::get_program_data_address"
def ATA_INTERFACE :=
  "spl_associated_token_account_interface::address::get_associated_token_address_with_progr\
    am_id"

namespace Pubkey
open Solanalib.Specs.SolanaPubkey.Pubkey

end Pubkey


namespace AddressValue
open Solanalib.Specs.SolanaAddress.Address

def comparison : Checker :=
  valueChecker (traitMethod ADDRESS "core::cmp::Ord" "cmp")
    "Solanalib.Specs.SolanaAddress.Address.cmp_model"
    cmp_model pairArg ordering orderingJson

def create : Checker :=
  createChecker ADDRESS_CREATE
    "Solanalib.Specs.SolanaAddress.Address.create_program_address_solana_run"
    .uninitialized .address (create_program_address_solana_run (Shim.createIndex .uninitialized))
    (create_program_address_solana_contract.contract (Shim.createIndex .uninitialized)).requires
    (Evaluation.createRun_ofFunction .address (Shim.createProvider .uninitialized) Shim.stringPanic)
    (Evaluation.createReady_ofFunction .uninitialized (Shim.createProvider .uninitialized)
      Shim.stringPanic)

def io261 : List Checker := [
  Io.writerChecker (traitMethod ADDRESS "borsh::ser::BorshSerialize" "serialize")
    "Solanalib.Specs.SolanaAddress.Address.serialize_run"
    (Solanalib.Specs.SolanaAddress.Address.serialize_run Io.writeIndex)
    (Solanalib.Specs.SolanaAddress.Address.serialize_run_iff Io.writeIndex),
  Io.readerChecker (traitMethod ADDRESS "borsh::de::BorshDeserialize" "deserialize_reader")
    "Solanalib.Specs.SolanaAddress.Address.deserialize_reader_read_exact_run" .invalidData
    (Solanalib.Specs.SolanaAddress.Address.deserialize_reader_read_exact_run Io.readIndex)
      (Io.readRun_evaluated .invalidData)]

end AddressValue

namespace Derived

def interface : Checker :=
  uninitDerivedChecker ATA_INTERFACE
    "Solanalib.Specs.SplAssociatedTokenAccountInterface.address.get_associated_token_addres\
      s_with_program_id_run"
    associatedInputs
    (address.get_associated_token_address_with_program_id_run Shim.uninitFindIndex)
    (address.get_associated_token_address_with_program_id_contract.contract
      Shim.uninitFindIndex).requires
    (Evaluation.uninitDerivedRun_ofFunction associatedInputs Shim.uninitFindProvider
      Shim.searchPanic)
    (fun before args => Address.Syscall.successInitialized_ofFunction Shim.uninitFindProvider
      before (associatedInputs args))
    Shim.associatedArgs

def loader : Checker :=
  uninitDerivedChecker LOADER
    "Solanalib.Specs.SolanaLoaderV3Interface.get_program_data_address_run" loaderInputs
    (Solanalib.Specs.SolanaLoaderV3Interface.get_program_data_address_run Shim.uninitFindIndex)
    (Solanalib.Specs.SolanaLoaderV3Interface.get_program_data_address_contract.contract
      Shim.uninitFindIndex).requires
    (Evaluation.uninitDerivedRun_ofFunction loaderInputs Shim.uninitFindProvider Shim.searchPanic)
    (fun before args => Address.Syscall.successInitialized_ofFunction Shim.uninitFindProvider
      before (loaderInputs args))
    (fun j => do pubkey (← field j "wallet"))

end Derived

end SolanalibTest.Conformance.Library.Families.AddressProfiles

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

end SolanalibTest.Conformance.Library.Families.AddressProfiles

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
  Solanalib.Specs.Core.Address.Syscall
open Solanalib.Specs.Core.Address.Operations
open Address (valueChecker pubkey pubkeyJson array32 array32Json selfArg pairArg arrayArg asBool
  asFound foundJson)

def PROGRAM := "solana_program::pubkey::Pubkey"
namespace Pubkey
open Solanalib.Specs.SolanaPubkey.Pubkey

end Pubkey

namespace Program
open Solanalib.Specs.SolanaProgram.pubkey.Pubkey

def values : List Checker := [
  valueChecker (method PROGRAM "to_bytes")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.to_bytes_model"
    to_bytes_model selfArg array32 array32Json,
  valueChecker (traitMethod PROGRAM "core::convert::AsRef<[u8]>" "as_ref")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.as_ref_model"
    as_ref_model selfArg asBytes bytesJson,
  valueChecker (traitMethod PROGRAM "core::default::Default" "default")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.default_model"
    default_model asUnit pubkey pubkeyJson,
  valueChecker (traitMethod PROGRAM "core::clone::Clone" "clone")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.clone_model"
    clone_model selfArg pubkey pubkeyJson,
  valueChecker (traitMethod PROGRAM "core::cmp::PartialEq" "eq")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.eq_model"
    eq_model pairArg asBool toJson]

def pda : List Checker := [
  createChecker (method PROGRAM "create_program_address")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.create_program_address_solana_run"
    .zeroed .legacyPubkey (create_program_address_solana_run (Shim.createIndex .zeroed))
    (create_program_address_solana_contract.contract (Shim.createIndex .zeroed)).requires
    (Evaluation.createRun_ofFunction .legacyPubkey (Shim.createProvider .zeroed) Shim.stringPanic)
    (Evaluation.createReady_ofFunction .zeroed (Shim.createProvider .zeroed) Shim.stringPanic),
  runtimeChecker (V := Value × UInt8) (method PROGRAM "find_program_address")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.find_program_address_solana_run"
    (find_program_address_solana_run Shim.zeroFindIndex)
    (Evaluation.zeroFindEval Shim.zeroFindProvider Shim.searchPanic)
    (Evaluation.zeroFindRun_ofFunction Shim.zeroFindProvider Shim.searchPanic)
    Address.Syscall.pdaInputs asFound foundJson,
  runtimeChecker (V := Except Error Value) (method PROGRAM "create_with_seed")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.create_with_seed_run"
    (create_with_seed_run Shim.seedIndex) (Evaluation.seedEval Shim.hashProvider)
    (Evaluation.seedRun_ofFunction Shim.hashProvider) Shim.seedInputs Shim.result Shim.resultJson]

def serializer : Checker :=
  Io.writerChecker (traitMethod PROGRAM "borsh::ser::BorshSerialize" "serialize")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.serialize_run"
    (serialize_run Io.writeIndex) Io.serializeRun_evaluated

def reader118 : Checker :=
  Io.readerChecker (traitMethod PROGRAM "borsh::de::BorshDeserialize" "deserialize_reader")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.deserialize_reader_run" .invalidInput
    (Solanalib.Specs.SolanaProgram.pubkey.Pubkey.deserialize_reader_run Io.readIndex)
      (Io.readRun_evaluated .invalidInput)

end Program

namespace AddressValue
open Solanalib.Specs.SolanaAddress.Address

end AddressValue

end SolanalibTest.Conformance.Library.Families.AddressProfiles

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

end SolanalibTest.Conformance.Library.Families.AddressProfiles

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
  Solanalib.Specs.Core.Address.Syscall
open Solanalib.Specs.Core.Address.Operations
open Address (valueChecker pubkey pubkeyJson array32 array32Json selfArg pairArg arrayArg asBool
  asFound foundJson)

namespace Pubkey
open Solanalib.Specs.SolanaPubkey.Pubkey

end Pubkey

namespace Program
open Solanalib.Specs.SolanaProgram.pubkey.Pubkey

def legacyReader : Checker :=
  valueChecker (traitMethod PROGRAM "borsh::de::BorshDeserialize" "deserialize")
    "Solanalib.Specs.SolanaProgram.pubkey.Pubkey.deserialize_model" deserialize_model asBytes
      Io.legacyResult Io.legacyResultJson

end Program

namespace AddressValue
open Solanalib.Specs.SolanaAddress.Address

end AddressValue

end SolanalibTest.Conformance.Library.Families.AddressProfiles

namespace SolanalibTest.Conformance.Library.Families.AddressProfiles

def corpora : List (String × List Checker) := [
  ("pubkey_profiles_221", Pubkey.values ++ Pubkey.pda ++ Pubkey.io ++ [Derived.client]),
  ("pubkey_profiles_240", Pubkey.values ++ Pubkey.pda ++ Pubkey.io ++ [Derived.client]),
  ("address_profiles_261", [AddressValue.comparison, AddressValue.create, Derived.loader,
    Derived.interface] ++ AddressValue.io261),
  ("address_profiles_260", [AddressValue.comparison, AddressValue.create, Derived.loader,
    Derived.interface]),
  ("program_pubkey_118", Program.values ++ Program.pda ++ [Program.serializer, Program.reader118]),
  ("program_pubkey_115", Program.values ++ Program.pda ++ [Program.serializer,
    Program.legacyReader])]

end SolanalibTest.Conformance.Library.Families.AddressProfiles
