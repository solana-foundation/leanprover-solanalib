/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaDefineSyscall.Runtime
public import Solanalib.Specs.SolanaDefineSyscall.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SolanalibTest.Specs.SolanaDefineSyscall.Runtime

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

theorem copy_bytes : RawMemory.copyStep Sample.index Sample.state ⟨256, 512, [4, 8, 4]⟩ =
    .ok (⟨0, [[4, 8, 4]]⟩, Sample.state) := rfl

theorem copy_overlap : RawMemory.copyStep Sample.index Sample.state ⟨256, 257, [4, 8]⟩ =
    .error .ProgramFailedToComplete := rfl

theorem copy_empty : RawMemory.copyStep Sample.index Sample.state ⟨0, 0, []⟩ =
    .ok (⟨0, [[]]⟩, Sample.state) := rfl

theorem set_bytes : RawMemory.setStep Sample.index Sample.state ⟨255, 3⟩ =
    .ok (⟨0, [[255, 255, 255]]⟩, Sample.state) := rfl

theorem set_empty : RawMemory.setStep Sample.index Sample.state ⟨255, 0⟩ =
    .ok (⟨0, [[]]⟩, Sample.state) := rfl

theorem create_success : RawAddress.createStep Sample.index Sample.state
    ⟨[[1, 2], [], [1, 2]], Solanalib.Runtime.Pubkey.zero⟩ =
    .ok (⟨0, [(Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 7)).bytes]⟩, Sample.state) := rfl

def onCurve : Index := { Sample.index with world := { Sample.world with
  prims := { Sample.world.prims with onCurve := fun _ => true } } }

theorem create_on_curve : RawAddress.createStep onCurve Sample.state ⟨[[]],
  Solanalib.Runtime.Pubkey.zero⟩ =
    .ok (⟨1, []⟩, Sample.state) := rfl

theorem create_count : RawAddress.createStep Sample.index Sample.state
    ⟨List.replicate 17 [], Solanalib.Runtime.Pubkey.zero⟩ = .error .ProgramFailedToComplete := rfl

theorem create_seed_length : RawAddress.createStep Sample.index Sample.state
    ⟨[List.replicate 33 1], Solanalib.Runtime.Pubkey.zero⟩ = .error .ProgramFailedToComplete := rfl

theorem find_success : RawAddress.findStep Sample.index Sample.state
    ⟨⟨[[1]], Solanalib.Runtime.Pubkey.zero⟩, 256, 512⟩ =
    .ok (⟨0, [(Solanalib.Runtime.Pubkey.ofBytes (List.replicate 32 7)).bytes, [255]]⟩,
      Sample.state) := rfl

theorem find_on_curve_overlap : RawAddress.findStep onCurve Sample.state
    ⟨⟨[[1]], Solanalib.Runtime.Pubkey.zero⟩, 256, 256⟩ = .ok (⟨1, []⟩, Sample.state) := rfl

theorem find_overlap : RawAddress.findStep Sample.index Sample.state
    ⟨⟨[[1]], Solanalib.Runtime.Pubkey.zero⟩, 256, 256⟩ = .error .ProgramFailedToComplete := rfl

theorem clock_bytes : RawState.typedStep .clock Sample.index Sample.state 256 =
    .ok (⟨0, [Sample.sysvars.clock.encode]⟩, Sample.state) := rfl

theorem rent_bytes : RawState.typedStep .rent Sample.index Sample.state 256 =
    .ok (⟨0, [Sample.sysvars.rent.reprC]⟩, Sample.state) := rfl

theorem typed_v0 : RawState.typedStep .clock
    { Sample.index with context := { Sample.context with abi := .v0 } } Sample.state 256 =
    .error .ProgramFailedToComplete := rfl

theorem typed_input_restricted : RawState.typedStep .clock Sample.index Sample.state
  Solanalib.Runtime.MM_INPUT_START =
    .error .ProgramFailedToComplete := rfl

theorem typed_unaligned : RawState.typedStep .rent Sample.index Sample.state 257 =
    .error .ProgramFailedToComplete := rfl

def selectedBuild : Versioning.Build where
  package := "solana-define-syscall"
  version := "2.3.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  targetFeatures := some []

theorem dynamic_declaration_admitted :
    (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild selectedBuild).identities
      .definitions_sol_memcpy_ ≠ [] := by decide +kernel

def runtimeMembers : List (Solanalib.Specs.SolanaDefineSyscall.Capabilities.Key × String) :=
  [(.definitions_sol_memcpy_, "sol_memcpy_"),
    (.definitions_sol_memset_, "sol_memset_"),
    (.definitions_sol_create_program_address, "sol_create_program_address"),
    (.definitions_sol_try_find_program_address, "sol_try_find_program_address"),
    (.definitions_sol_get_clock_sysvar, "sol_get_clock_sysvar"),
    (.definitions_sol_get_rent_sysvar, "sol_get_rent_sysvar")]

/-- Every new raw operation retains its defining identity across the declared
compatibility line, including releases outside the exact native reference. -/
theorem compatible_runtime_identities :
    ["2.3.0", "2.3.1", "2.9.0"].all (fun version => runtimeMembers.all (fun (key, name) =>
      decide ((Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities key =
        [⟨"solana-define-syscall", version, "solana_define_syscall::definitions::" ++ name,
          "solana_define_syscall::definitions::" ++ name⟩]))) = true := by
  decide +kernel

theorem outside_runtime_range_rejected :
    ["2.2.1", "3.0.0", "2.3.1-rc.1"].all (fun version => runtimeMembers.all (fun (key, _) =>
      decide ((Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities key = []))) = true := by
  decide +kernel

theorem static_dispatch_rejected :
    (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        targetFeatures := some ["static-syscalls"] }).identities
        .definitions_sol_memcpy_ = [] := by decide +kernel

theorem unknown_dispatch_rejected :
    (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        targetFeatures := none }).identities
        .definitions_sol_create_program_address = [] := by decide +kernel

theorem narrow_pointer_build_rejected :
    (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        target := [⟨"pointer_width", "32"⟩] }).identities
        .definitions_sol_get_clock_sysvar = [] := by decide +kernel

theorem wrong_runtime_origin_rejected :
    (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.1"
        source := ⟨"git", "https://example.invalid/solana-sdk", "unreviewed"⟩ }).identities
        .definitions_sol_get_rent_sysvar = [] := by decide +kernel

theorem reviewed_source_file_is_not_automatic_admission :
    (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
      { selectedBuild with version := "5.1.0" }).identities
        .definitions_sol_memset_ = [] := by decide +kernel

end SolanalibTest.Specs.SolanaDefineSyscall.Runtime

namespace SolanalibTest.Specs.SolanaDefineSyscall.Runtime

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

theorem return_set : RawState.setReturnStep Sample.index Sample.state [6, 4] =
    .ok (.ok0, { Sample.state with ts := { Sample.state.ts with
      returnData := (Sample.state.ts.key Sample.context.frame.programIdx, [6, 4]) } }) := rfl

theorem return_clear : RawState.setReturnStep Sample.index Sample.state [] =
    .ok (.ok0, { Sample.state with ts := { Sample.state.ts with
      returnData := (Sample.state.ts.key Sample.context.frame.programIdx, []) } }) := rfl

theorem return_too_long : RawState.setReturnStep Sample.index Sample.state (List.replicate 1025 1) =
    .error .ProgramFailedToComplete := by
  rw [RawState.setReturn_result, _root_.List.length_replicate]
  rfl

theorem return_protocol : ∃ after,
    RawState.setReturnStep Sample.index Sample.state [6, 4, 2] = .ok (.ok0, after) ∧
    RawState.getReturnStep Sample.index after ⟨0, 0, 0⟩ = .ok (⟨3, []⟩, after) :=
  RawState.set_get_length Sample.index Sample.state [6, 4, 2] (by decide) 0 0

end SolanalibTest.Specs.SolanaDefineSyscall.Runtime

namespace SolanalibTest.Specs.SolanaDefineSyscall.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

abbrev Row := Solanalib.Specs.SolanaDefineSyscall.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def build0 : Build where
  package := "solana-define-syscall"
  version := "5.1.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩]
  targetFeatures := some []

def rows0 : List Row := [
    (.definitions_sol_create_program_address, "raw-runtime-solana-define-syscall-5.1.0-non-\
      bpf",
      "solana_define_syscall::definitions::sol_create_program_address",
        "solana_define_syscall::definitions::sol_create_program_address")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["5.1.0", "5.1.1"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  { build0 with features := some ["unstable-static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 1 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "5.0.999" },
  { build0 with version := "6.0.0" },
  { build0 with version := "5.1.1-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "pointer_width")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"pointer_width", "32"⟩]) },
  { build0 with target := (build0.target.filter (fun fact => fact.field != "arch")) },
  { build0 with target := (build0.target.map (fun fact =>
        if fact.field == "arch" then { fact with value := "bpf" } else fact)) },
  { build0 with target := (build0.target ++ [⟨"arch", "bpf"⟩]) },
  { build0 with targetFeatures := none },
  { build0 with targetFeatures := some ["static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 13 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "solana-define-syscall"
  version := "5.1.0"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩]
  features := some []
  targetFeatures := some []

def rows1 : List Row := [
    (.definitions_sol_create_program_address, "raw-runtime-solana-define-syscall-5.1.0-bpf",
      "solana_define_syscall::definitions::sol_create_program_address",
        "solana_define_syscall::definitions::sol_create_program_address")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 1 ∧
    ["5.1.0", "5.1.1"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "5.0.999" },
  { build1 with version := "6.0.0" },
  { build1 with version := "5.1.1-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "pointer_width")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"pointer_width", "32"⟩]) },
  { build1 with target := (build1.target.filter (fun fact => fact.field != "arch")) },
  { build1 with target := (build1.target.map (fun fact =>
        if fact.field == "arch" then { fact with value := "x86_64" } else fact)) },
  { build1 with target := (build1.target ++ [⟨"arch", "x86_64"⟩]) },
  { build1 with features := none },
  { build1 with features := some ["unstable-static-syscalls"] },
  { build1 with targetFeatures := none },
  { build1 with targetFeatures := some ["static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 15 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

def build2 : Build where
  package := "solana-define-syscall"
  version := "4.0.1"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩]
  targetFeatures := some []

def rows2 : List Row := [
    (.definitions_sol_memcpy_, "raw-runtime-solana-define-syscall-4.0.1-non-bpf",
      "solana_define_syscall::definitions::sol_memcpy_",
        "solana_define_syscall::definitions::sol_memcpy_"),
    (.definitions_sol_memset_, "raw-runtime-solana-define-syscall-4.0.1-non-bpf",
      "solana_define_syscall::definitions::sol_memset_",
        "solana_define_syscall::definitions::sol_memset_"),
    (.definitions_sol_set_return_data, "raw-runtime-solana-define-syscall-4.0.1-non-bpf",
      "solana_define_syscall::definitions::sol_set_return_data",
        "solana_define_syscall::definitions::sol_set_return_data")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_2 :
    rows2.length = 3 ∧
    ["4.0.1", "4.0.2"].all (fun version =>
      rows2.all (identifies { build2 with version := version })) = true := by
  decide +kernel

def accepted2 : List Build := [
  { build2 with features := some ["unstable-static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_2 :
    accepted2.length = 1 ∧
    accepted2.all (fun build => rows2.all (identifies build)) = true := by
  decide +kernel

def rejected2 : List Build := [
  { build2 with version := "4.0.0" },
  { build2 with version := "5.0.0" },
  { build2 with version := "4.0.2-rc.1" },
  { build2 with package := "unrelated-library" },
  { build2 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build2 with target := (build2.target.filter (fun fact => fact.field != "pointer_width")) },
  { build2 with target := (build2.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build2 with target := (build2.target ++ [⟨"pointer_width", "32"⟩]) },
  { build2 with target := (build2.target.filter (fun fact => fact.field != "arch")) },
  { build2 with target := (build2.target.map (fun fact =>
        if fact.field == "arch" then { fact with value := "bpf" } else fact)) },
  { build2 with target := (build2.target ++ [⟨"arch", "bpf"⟩]) },
  { build2 with targetFeatures := none },
  { build2 with targetFeatures := some ["static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_2 :
    rejected2.length = 13 ∧
    rejected2.all (fun build => rows2.all (rejects build)) = true := by
  decide +kernel

def build3 : Build where
  package := "solana-define-syscall"
  version := "4.0.1"
  source := registry
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩]
  features := some []
  targetFeatures := some []

def rows3 : List Row := [
    (.definitions_sol_memcpy_, "raw-runtime-solana-define-syscall-4.0.1-bpf",
      "solana_define_syscall::definitions::sol_memcpy_",
        "solana_define_syscall::definitions::sol_memcpy_"),
    (.definitions_sol_memset_, "raw-runtime-solana-define-syscall-4.0.1-bpf",
      "solana_define_syscall::definitions::sol_memset_",
        "solana_define_syscall::definitions::sol_memset_"),
    (.definitions_sol_set_return_data, "raw-runtime-solana-define-syscall-4.0.1-bpf",
      "solana_define_syscall::definitions::sol_set_return_data",
        "solana_define_syscall::definitions::sol_set_return_data")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_3 :
    rows3.length = 3 ∧
    ["4.0.1", "4.0.2"].all (fun version =>
      rows3.all (identifies { build3 with version := version })) = true := by
  decide +kernel

def rejected3 : List Build := [
  { build3 with version := "4.0.0" },
  { build3 with version := "5.0.0" },
  { build3 with version := "4.0.2-rc.1" },
  { build3 with package := "unrelated-library" },
  { build3 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build3 with target := (build3.target.filter (fun fact => fact.field != "pointer_width")) },
  { build3 with target := (build3.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build3 with target := (build3.target ++ [⟨"pointer_width", "32"⟩]) },
  { build3 with target := (build3.target.filter (fun fact => fact.field != "arch")) },
  { build3 with target := (build3.target.map (fun fact =>
        if fact.field == "arch" then { fact with value := "x86_64" } else fact)) },
  { build3 with target := (build3.target ++ [⟨"arch", "x86_64"⟩]) },
  { build3 with features := none },
  { build3 with features := some ["unstable-static-syscalls"] },
  { build3 with targetFeatures := none },
  { build3 with targetFeatures := some ["static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_3 :
    rejected3.length = 15 ∧
    rejected3.all (fun build => rows3.all (rejects build)) = true := by
  decide +kernel

def build4 : Build where
  package := "solana-define-syscall"
  version := "3.0.0"
  source := registry
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩, ⟨"panic", "ab\
    ort"⟩]
  targetFeatures := some []

def rows4 : List Row := [
    (.definitions_sol_invoke_signed_rust, "raw-cpi-rust-solana-define-syscall-3.0.0",
      "solana_define_syscall::definitions::sol_invoke_signed_rust",
        "solana_define_syscall::definitions::sol_invoke_signed_rust")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_4 :
    rows4.length = 1 ∧
    ["3.0.0", "3.0.1"].all (fun version =>
      rows4.all (identifies { build4 with version := version })) = true := by
  decide +kernel

def rejected4 : List Build := [
  { build4 with version := "2.999.999" },
  { build4 with version := "4.0.0" },
  { build4 with version := "3.0.1-rc.1" },
  { build4 with package := "unrelated-library" },
  { build4 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  { build4 with target := (build4.target.filter (fun fact => fact.field != "os")) },
  { build4 with target := (build4.target.map (fun fact =>
        if fact.field == "os" then { fact with value := "linux" } else fact)) },
  { build4 with target := (build4.target ++ [⟨"os", "linux"⟩]) },
  { build4 with target := (build4.target.filter (fun fact => fact.field != "pointer_width")) },
  { build4 with target := (build4.target.map (fun fact =>
        if fact.field == "pointer_width" then { fact with value := "32" } else fact)) },
  { build4 with target := (build4.target ++ [⟨"pointer_width", "32"⟩]) },
  { build4 with target := (build4.target.filter (fun fact => fact.field != "endian")) },
  { build4 with target := (build4.target.map (fun fact =>
        if fact.field == "endian" then { fact with value := "unsupported" } else fact)) },
  { build4 with target := (build4.target ++ [⟨"endian", "unsupported"⟩]) },
  { build4 with target := (build4.target.filter (fun fact => fact.field != "panic")) },
  { build4 with target := (build4.target.map (fun fact =>
        if fact.field == "panic" then { fact with value := "unwind" } else fact)) },
  { build4 with target := (build4.target ++ [⟨"panic", "unwind"⟩]) },
  { build4 with targetFeatures := none },
  { build4 with targetFeatures := some ["static-syscalls"] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_4 :
    rejected4.length = 19 ∧
    rejected4.all (fun build => rows4.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaDefineSyscall.UpdatedProfiles

namespace SolanalibTest.Specs.SolanaDefineSyscall.Runtime

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime

theorem epoch_bytes : RawState.typedStep .epochSchedule Sample.index Sample.state 256 =
    .ok (⟨0, [Sample.sysvars.epochSchedule.reprC]⟩, Sample.state) := rfl

theorem stack_observation : RawState.stackStep Sample.index Sample.state () =
    .ok (⟨1, []⟩, Sample.state) := rfl

end SolanalibTest.Specs.SolanaDefineSyscall.Runtime

@[expose] public section

namespace SolanalibTest.Specs.SolanaDefineSyscall.RuntimeProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

def build0 : Versioning.Build where
  package := "solana-define-syscall"
  version := "4.0.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩]
  features := none
  targetFeatures := some []
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["4.0.0", "4.0.1", "4.1.0"].all (fun version =>
      decide (((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-non-bpf").forBuild
        { build0 with version := version }).identities .definitions_sol_get_epoch_schedule_sysvar =
          [⟨"solana-define-syscall", version,
            "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar",
            "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"solana-define-syscall", "4.0.1",
      "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar",
            "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
        build0).identities .definitions_sol_get_epoch_schedule_sysvar)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-non-bpf").applicability
      .definitions_sol_get_epoch_schedule_sysvar).length = 1 ∧
    ["3.999.999", "5.0.0", "4.1.0-rc.1"].all (fun version =>
      (((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-non-bpf").forBuild { build0 with
        version := version }).identities
        .definitions_sol_get_epoch_schedule_sysvar).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "solana-define-syscall-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with target := [⟨"arch", "x86_64"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩, ⟨"pointer_width",
        "64"⟩] },
      { build0 with target := [⟨"arch", "x86_64"⟩, ⟨"pointer_width", "unsupported-target-va\
        lue"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩, ⟨"arch", "x86_6\
        4"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩] },
      { build0 with targetFeatures := none },
      { build0 with targetFeatures := some ["static-syscalls"] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-non-bpf").forBuild
        build).identities
        .definitions_sol_get_epoch_schedule_sysvar).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "solana-define-syscall"
  version := "4.0.1"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["4.0.0", "4.0.1", "4.1.0"].all (fun version =>
      decide (((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-bpf").forBuild
        { build1 with version := version }).identities .definitions_sol_get_epoch_schedule_sysvar =
          [⟨"solana-define-syscall", version,
            "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar",
            "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"solana-define-syscall", "4.0.1",
      "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar",
            "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
        build1).identities .definitions_sol_get_epoch_schedule_sysvar)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-bpf").applicability
      .definitions_sol_get_epoch_schedule_sysvar).length = 1 ∧
    ["3.999.999", "5.0.0", "4.1.0-rc.1"].all (fun version =>
      (((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-bpf").forBuild { build1 with
        version := version }).identities
        .definitions_sol_get_epoch_schedule_sysvar).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "solana-define-syscall-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with target := [⟨"arch", "bpf"⟩] },
      { build1 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩, ⟨"pointer_width",
        "64"⟩] },
      { build1 with target := [⟨"arch", "bpf"⟩, ⟨"pointer_width", "unsupported-target-value"⟩] },
      { build1 with target := [⟨"pointer_width", "64"⟩] },
      { build1 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩, ⟨"arch", "bpf"⟩] },
      { build1 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "unsupported-target-value"⟩] },
      { build1 with features := none },
      { build1 with features := some ["unstable-static-syscalls"] },
      { build1 with targetFeatures := none },
      { build1 with targetFeatures := some ["static-syscalls"] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "raw-runtime-solana-define-syscall-4.0.1-bpf").forBuild
        build).identities
        .definitions_sol_get_epoch_schedule_sysvar).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "solana-define-syscall"
  version := "5.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩]
  features := none
  targetFeatures := some []
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["5.0.0", "5.1.0", "5.2.0", "5.3.0", "5.4.0", "5.5.0"].all (fun version =>
      decide (((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-non-bpf").forBuild
        { build2 with version := version }).identities .definitions_sol_get_stack_height =
          [⟨"solana-define-syscall", version,
            "solana_define_syscall::definitions::sol_get_stack_height",
            "solana_define_syscall::definitions::sol_get_stack_height"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"solana-define-syscall", "5.1.0", "solana_define_syscall::definitions::sol_get_stack\
      _height",
            "solana_define_syscall::definitions::sol_get_stack_height"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
        build2).identities .definitions_sol_get_stack_height)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-non-bpf").applicability
      .definitions_sol_get_stack_height).length = 1 ∧
    ["4.999.999", "6.0.0", "5.5.0-rc.1"].all (fun version =>
      (((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-non-bpf").forBuild { build2 with
        version := version }).identities
        .definitions_sol_get_stack_height).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "solana-define-syscall-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build2 with target := [⟨"arch", "x86_64"⟩] },
      { build2 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩, ⟨"pointer_width",
        "64"⟩] },
      { build2 with target := [⟨"arch", "x86_64"⟩, ⟨"pointer_width", "unsupported-target-va\
        lue"⟩] },
      { build2 with target := [⟨"pointer_width", "64"⟩] },
      { build2 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "x86_64"⟩, ⟨"arch", "x86_6\
        4"⟩] },
      { build2 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩] },
      { build2 with targetFeatures := none },
      { build2 with targetFeatures := some ["static-syscalls"] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-non-bpf").forBuild
        build).identities
        .definitions_sol_get_stack_height).isEmpty) = true := by
  decide +kernel

def build3 : Versioning.Build where
  package := "solana-define-syscall"
  version := "5.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩]
  features := some []
  targetFeatures := some []
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile3_literal_identities :
    ["5.0.0", "5.1.0", "5.2.0", "5.3.0", "5.4.0", "5.5.0"].all (fun version =>
      decide (((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-bpf").forBuild
        { build3 with version := version }).identities .definitions_sol_get_stack_height =
          [⟨"solana-define-syscall", version,
            "solana_define_syscall::definitions::sol_get_stack_height",
            "solana_define_syscall::definitions::sol_get_stack_height"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile3_present_in_full_catalog :
    ([⟨"solana-define-syscall", "5.1.0", "solana_define_syscall::definitions::sol_get_stack\
      _height",
            "solana_define_syscall::definitions::sol_get_stack_height"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SolanaDefineSyscall.Capabilities.catalog.forBuild
        build3).identities .definitions_sol_get_stack_height)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile3_range_rejections :
    ((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-bpf").applicability
      .definitions_sol_get_stack_height).length = 1 ∧
    ["4.999.999", "6.0.0", "5.5.0-rc.1"].all (fun version =>
      (((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-bpf").forBuild { build3 with
        version := version }).identities
        .definitions_sol_get_stack_height).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile3_build_rejections :
    ([{ build3 with package := "solana-define-syscall-other" },
      { build3 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build3 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build3 with target := [⟨"arch", "bpf"⟩] },
      { build3 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩, ⟨"pointer_width",
        "64"⟩] },
      { build3 with target := [⟨"arch", "bpf"⟩, ⟨"pointer_width", "unsupported-target-value"⟩] },
      { build3 with target := [⟨"pointer_width", "64"⟩] },
      { build3 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "bpf"⟩, ⟨"arch", "bpf"⟩] },
      { build3 with target := [⟨"pointer_width", "64"⟩, ⟨"arch", "unsupported-target-value"⟩] },
      { build3 with features := none },
      { build3 with features := some ["unstable-static-syscalls"] },
      { build3 with targetFeatures := none },
      { build3 with targetFeatures := some ["static-syscalls"] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "raw-runtime-solana-define-syscall-5.1.0-bpf").forBuild
        build).identities
        .definitions_sol_get_stack_height).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SolanaDefineSyscall.RuntimeProfiles
