/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorLang.error_codes
import Solanalib.Specs.AnchorLang.error_log
import Solanalib.Specs.AnchorLang.error_operations
import Solanalib.Specs.AnchorLang.context_operations
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Decoders
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Logging
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Writer

/-!
The explicit corpora select reviewed Anchor 0.32.1, 1.1.2, 1.0.2, 0.29.0 and 0.27.0
context, error and codec operations, including anchor-lang-error 1.1.2.
Each corpus selects only its registered methods.
The references retain callback exits, field assignment cleanup, owned diagnostic
payloads and the source-specific cursor behavior. The native drivers use the
Solana logging/copy syscall profile; invocation is never traversed here.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

private def quiet (checker : Checker) : Checker :=
  Anchor.withFrame [("no syscalls", noSyscalls)] checker

def corpora : List (String × List Checker) := [
  ("anchor_operations_0_32_1", [
    quiet (codeNameChecker .v032 "anchor_lang::error::ErrorCode::name"
      (Solanalib.Specs.AnchorLang.error.ErrorCode.name_run codeNameIndex) (fun before _ =>
        PGraph.ofFunction newString before _)),
    quiet (codeChecker .v032
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::ErrorCode>>::from"
      (Solanalib.Specs.AnchorLang.error.Error.from_error_code_run ⟨heapTypes .boxed, rfl⟩)
      (fun before _ => Fn.fromCode_graph heapGraph .boxed before _)),
    quiet (pubkeysChecker .v032 "anchor_lang::error::Error::with_pubkeys"
      (fun before error => Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_pubkeys_run
        ⟨heapTypes .boxed, rfl⟩ before
        (error, pubkey 3, pubkey 7)) (fun before error => Fn.withCompared_graph heapGraph .boxed
          (some (.pubkeys (pubkey 3) (pubkey 7))) before error)),
    quiet (nameChecker .v032 "anchor_lang::error::Error::with_account_name"
      (Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run ⟨nameTypes
        .boxed, rfl⟩) (nameGraph .boxed)),
    quiet (valuesChecker .v032 "anchor_lang::error::Error::with_values"
      (Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_values_run ⟨valuesTypes .boxed,
        rfl⟩) (valuesGraph .boxed)),
    quiet (equalityChecker "<anchor_lang::error::Error as core::cmp::PartialEq>::eq"),
    quiet (ioChecker
      "<anchor_lang::error::Error as core::convert::From<std::io::error::Error>>::from"),
    Logging.checker .v032 "anchor_lang::error::Error::log"
      (Solanalib.Specs.AnchorLang.error.Error.log_run ⟨Logging.types (.legacy .programError2_2_2)
        .boxed, rfl⟩)
      (Logging.logGraph (.legacy .programError2_2_2) .boxed),
    Writer.checker "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as \
      std::io::Write>::write_all",
    Contexts.contextChecker "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
    Contexts.cpiChecker .v032 0 "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
      T>::new",
    Contexts.cpiChecker .v032 1
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
    Contexts.cpiChecker .v032 2
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"
  ]),
  ("anchor_operations_1_1_2", [
    quiet (codeNameChecker .v112 "anchor_lang_error::ErrorCode::name"
      (Solanalib.Specs.AnchorLangError.ErrorCode.name_run codeNameIndex) (fun before _ =>
        PGraph.ofFunction newString before _)),
    quiet (codeChecker .v112
      "<anchor_lang_error::Error as \
        core::convert::From<anchor_lang_error::ErrorCode>>::from"
      (Solanalib.Specs.AnchorLangError.Error.from_error_code_run ⟨heapTypes .boxed, rfl⟩)
      (fun before _ => Fn.fromCode_graph heapGraph .boxed before _)),
    quiet (nameChecker .v112 "anchor_lang_error::Error::with_account_name"
      (Solanalib.Specs.AnchorLangError.Error.with_account_name_run ⟨nameTypes .boxed, rfl⟩)
        (nameGraph .boxed)),
    Logging.checker .v112 "anchor_lang_error::Error::log"
      (Solanalib.Specs.AnchorLangError.Error.log_run ⟨Logging.types .modern .boxed, rfl⟩)
      (Logging.logGraph .modern .boxed),
    Writer.checker "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as \
      std::io::Write>::write_all",
    Decoders.loaderChecker
      "anchor_lang::bpf_upgradeable_state::<impl anchor_lang::AccountDeserialize for \
        solana_loader_v3_interface::state::UpgradeableLoaderState>::try_deserialize_uncheck\
        ed",
    Decoders.defaultChecker "anchor_lang::AccountDeserialize::try_deserialize",
    Contexts.contextChecker "anchor_lang::context::Context::<'info, T>::new",
    Contexts.cpiChecker .v112 0 "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
      T>::new",
    Contexts.cpiChecker .v112 2
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"
  ]),
  ("anchor_operations_1_0_2", [
    quiet (codeNameChecker .v102 "anchor_lang::error::ErrorCode::name"
      (Solanalib.Specs.AnchorLang.error.ErrorCode.name_account_migration_run codeNameIndex) (fun
        before _ => PGraph.ofFunction newString before _)),
    quiet (codeChecker .v102
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::ErrorCode>>::from"
      (Solanalib.Specs.AnchorLang.error.Error.from_error_code_account_migration_run ⟨heapTypes
        .boxed, rfl⟩)
      (fun before _ => Fn.fromCode_graph heapGraph .boxed before _)),
    quiet (nameChecker .v102 "anchor_lang::error::Error::with_account_name"
      (Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run ⟨nameTypes
        .boxed, rfl⟩) (nameGraph .boxed)),
    Logging.checker .v102 "anchor_lang::error::Error::log"
      (Solanalib.Specs.AnchorLang.error.Error.log_modern_run ⟨Logging.types .modern .boxed, rfl⟩)
      (Logging.logGraph .modern .boxed),
    Contexts.contextChecker "anchor_lang::context::Context::<'info, T>::new",
    Contexts.cpiChecker .v102 0 "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
      T>::new",
    Contexts.cpiChecker .v102 2
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
    Contexts.cpiChecker .v102 3
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_remaining_accounts"
  ]),
  ("anchor_operations_0_29_0", [
    quiet (codeNameChecker .v029 "anchor_lang::error::ErrorCode::name"
      (Solanalib.Specs.AnchorLang.error.ErrorCode.name_legacy_run codeNameIndex) (fun before _ =>
        PGraph.ofFunction newString before _)),
    quiet (codeChecker .v029
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::ErrorCode>>::from"
      (Solanalib.Specs.AnchorLang.error.Error.from_legacy_error_code_run ⟨heapTypes .boxed, rfl⟩)
      (fun before _ => Fn.fromCode_graph heapGraph .boxed before _)),
    quiet (pubkeysChecker .v029 "anchor_lang::error::Error::with_pubkeys"
      (fun before error => Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_pubkeys_run
        ⟨heapTypes .boxed, rfl⟩ before
        (error, pubkey 3, pubkey 7)) (fun before error => Fn.withCompared_graph heapGraph .boxed
          (some (.pubkeys (pubkey 3) (pubkey 7))) before error)),
    quiet (nameChecker .v029 "anchor_lang::error::Error::with_account_name"
      (Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_account_name_run ⟨nameTypes
        .boxed, rfl⟩) (nameGraph .boxed)),
    quiet (valuesChecker .v029 "anchor_lang::error::Error::with_values"
      (Solanalib.Specs.AnchorLang.error.Error.GenericProgram.with_values_run ⟨valuesTypes .boxed,
        rfl⟩) (valuesGraph .boxed)),
    Logging.checker .v029 "anchor_lang::error::Error::log"
      (Solanalib.Specs.AnchorLang.error.Error.log_legacy_program_run ⟨Logging.types (.legacy
        .solana1_18_26) .boxed, rfl⟩)
      (Logging.logGraph (.legacy .solana1_18_26) .boxed),
    Writer.checker "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as \
      std::io::Write>::write_all",
    Contexts.contextChecker "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
    Contexts.cpiChecker .v029 0 "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
      T>::new",
    Contexts.cpiChecker .v029 1
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
    Contexts.cpiChecker .v029 2
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"
  ]),
  ("anchor_operations_0_27_0", [
    quiet (codeNameChecker .v027 "anchor_lang::error::ErrorCode::name"
      (Solanalib.Specs.AnchorLang.error.ErrorCode.name_pre_token_program_checks_run codeNameIndex)
        (fun before _ => PGraph.ofFunction newString before _)),
    quiet (codeChecker .v027
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::ErrorCode>>::from"
      (Solanalib.Specs.AnchorLang.error.Error.from_error_code_inline_run ⟨heapTypes .inline, rfl⟩)
      (fun before _ => Fn.fromCode_graph heapGraph .inline before _)),
    quiet (fromAnchorChecker
      "<anchor_lang::error::Error as \
        core::convert::From<anchor_lang::error::AnchorError>>::from"),
    quiet (fromProgramChecker
      "<anchor_lang::error::Error as \
        core::convert::From<solana_program::program_error::ProgramError>>::from"),
    quiet (pubkeysChecker .v027 "anchor_lang::error::Error::with_pubkeys"
      (fun before error => Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_inline_run
        ⟨heapTypes .inline, rfl⟩ before
        (error, pubkey 3, pubkey 7)) (fun before error => Fn.withCompared_graph heapGraph .inline
          (some (.pubkeys (pubkey 3) (pubkey 7))) before error)),
    quiet (sourceChecker "anchor_lang::error::Error::with_source"),
    quiet (nameChecker .v027 "anchor_lang::error::Error::with_account_name"
      (Solanalib.Specs.AnchorLang.error.Error.with_account_name_inline_run ⟨nameTypes .inline,
        rfl⟩) (nameGraph .inline)),
    quiet (valuesChecker .v027 "anchor_lang::error::Error::with_values"
      (Solanalib.Specs.AnchorLang.error.Error.with_values_inline_run ⟨valuesTypes .inline, rfl⟩)
        (valuesGraph .inline)),
    Logging.checker .v027 "anchor_lang::error::Error::log"
      (Solanalib.Specs.AnchorLang.error.Error.log_inline_run ⟨Logging.types (.legacy .solana1_15_2)
        .inline, rfl⟩)
      (Logging.logGraph (.legacy .solana1_15_2) .inline),
    Writer.checker "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as \
      std::io::Write>::write_all",
    Decoders.idlChecker
      "<anchor_lang::idl::IdlInstruction as borsh::de::BorshDeserialize>::deserialize",
    Contexts.contextChecker "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
    Contexts.cpiChecker .v027 0 "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, \
      T>::new",
    Contexts.cpiChecker .v027 1
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
    Contexts.cpiChecker .v027 2
      "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer"
  ])]

end SolanalibTest.Conformance.Library.Families.AnchorOperations
