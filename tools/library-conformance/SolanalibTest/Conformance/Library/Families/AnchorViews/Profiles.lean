/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Check

/-! Exact native spellings for the selected Anchor 0.32.1, 1.1.2, 1.0.2,
0.29.0 and 0.27.0 profiles. Shared lifetime formatting remains a helper; only the explicit
corpora select calls. No open version range is selected. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (withFrame)

structure Profile where
  sources : Sources
  oldLifetimes : Bool
  infoPath : String
  keyPath : String
  lamports : Bool
  debug : Bool

def profile032 : Profile := ⟨sourcesBorrowed, false, "solana_account_info::AccountInfo",
  "solana_pubkey::Pubkey", true, false⟩
def spell (profile : Profile) (wrapper operation name : String) : String :=
  let n := name.replace "solana_account_info::AccountInfo" profile.infoPath
    |>.replace "solana_address::Address" profile.keyPath
  if profile.oldLifetimes then
    if (["account", "interface_account", "sysvar"].contains wrapper) &&
        (["deref", "deref_mut"].contains operation) then n.replace "<'_, T>" "<'a, T>"
    else n.replace "<'_, T>" "<'info, T>" |>.replace "<'_>" "<'info>"
  else n

def nativeGenerics (wrapper operation : String) : List (String × String) :=
  if wrapper = "lib" && operation = "get_lamports" then
    [("Self", "conformance_anchor_views::cases::Holder")]
  else if ["account", "interface_account"].contains wrapper then [("T",
    "conformance_anchor_views::cases::Payload")]
  else if ["program", "interface"].contains wrapper then [("T",
    "conformance_anchor_views::cases::Tag")]
  else if wrapper = "sysvar" then [("T", "conformance_anchor_views::cases::ProbeSysvar")]
  else []

def checkedItems : List (String × String × String) := [
  ("account", "as_ref_info",
    "<anchor_lang::accounts::account::Account<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("account", "deref_mut",
    "<anchor_lang::accounts::account::Account<'_, T> as \
      core::ops::deref::DerefMut>::deref_mut"),
  ("account", "key", "<anchor_lang::accounts::account::Account<'_, T> as \
    anchor_lang::Key>::key"),
  ("account", "clone",
    "<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone"),
  ("interface_account", "as_ref_info",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("interface_account", "key",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
      anchor_lang::Key>::key"),
  ("interface_account", "clone",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      core::clone::Clone>::clone"),
  ("program", "deref",
    "<anchor_lang::accounts::program::Program<'info, T> as core::ops::deref::Deref>::deref"),
  ("program", "clone",
    "<anchor_lang::accounts::program::Program<'info, T> as core::clone::Clone>::clone"),
  ("signer", "as_ref_info",
    "<anchor_lang::accounts::signer::Signer<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("signer", "deref",
    "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
  ("signer", "clone",
    "<anchor_lang::accounts::signer::Signer<'info> as core::clone::Clone>::clone"),
  ("unchecked_account", "as_ref_info",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("unchecked_account", "deref",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("unchecked_account", "key",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
      anchor_lang::Key>::key"),
  ("unchecked_account", "clone",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::clone::Clone>::clone"),
  ("lib", "key", "<solana_address::Address as anchor_lang::Key>::key"),
  ("lib", "get_lamports", "anchor_lang::Lamports::get_lamports")]

def select (profile : Profile) (wrapper operation name : String) : Option Checker :=
  let function := spell profile wrapper operation name
  let generics := nativeGenerics wrapper operation
  let hasPayload := ["account", "interface_account"].contains wrapper
  let savedOwner := wrapper == "interface_account"
  let chosen := if wrapper = "lib" then
      if operation = "key" then some (pubkeyChecker function)
      else if profile.lamports then some (lamportsChecker function generics) else none
    else match operation with
    | "key" => some (keyChecker function generics hasPayload savedOwner)
    | "as_ref_info" => some (infoChecker profile.sources.storage profile.sources.info function
      generics hasPayload savedOwner)
    | "deref" => some (infoChecker profile.sources.storage profile.sources.info function generics
      false savedOwner)
    | "deref_mut" => some (mutableChecker profile.debug function generics savedOwner)
    | "clone" => if hasPayload then some (cloneChecker profile.sources.storage
      profile.sources.clone function generics savedOwner)
        else some (infoCloneChecker profile.sources.storage profile.sources.infoClone function
          generics)
    | _ => none
  chosen.map (withFrame [("pinned feature profile", profileFrame profile.debug)])

def checkers (profile : Profile) : List Checker :=
  checkedItems.filterMap fun (wrapper, operation, name) => select profile wrapper operation name

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (withFrame)

def profile112 : Profile := ⟨sourcesBorrowed, false, "solana_account_info::AccountInfo",
  "solana_address::Address", true, false⟩

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

/-- Exact recorded 1.1.2 methods selected by the cumulative model registry. -/
def checkedItems112 : List (String × String × String) := [
  ("account", "as_ref_info",
    "<anchor_lang::accounts::account::Account<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("account", "deref_mut",
    "<anchor_lang::accounts::account::Account<'_, T> as \
      core::ops::deref::DerefMut>::deref_mut"),
  ("account", "key", "<anchor_lang::accounts::account::Account<'_, T> as \
    anchor_lang::Key>::key"),
  ("interface_account", "as_ref_info",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("interface_account", "deref_mut",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
      core::ops::deref::DerefMut>::deref_mut"),
  ("interface_account", "key",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
      anchor_lang::Key>::key"),
  ("program", "as_ref_info",
    "<anchor_lang::accounts::program::Program<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("program", "deref",
    "<anchor_lang::accounts::program::Program<'info, T> as core::ops::deref::Deref>::deref"),
  ("program", "key", "<anchor_lang::accounts::program::Program<'_, T> as \
    anchor_lang::Key>::key"),
  ("interface", "as_ref_info",
    "<anchor_lang::accounts::interface::Interface<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("signer", "as_ref_info",
    "<anchor_lang::accounts::signer::Signer<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("signer", "deref",
    "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
  ("signer", "key", "<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key"),
  ("system_account", "deref",
    "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("unchecked_account", "as_ref_info",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("unchecked_account", "deref",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("unchecked_account", "key",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
      anchor_lang::Key>::key"),
  ("lib", "key", "<solana_address::Address as anchor_lang::Key>::key")]

def checkers112 : List Checker :=
  checkedItems112.filterMap fun (wrapper, operation, name) => select profile112 wrapper operation
    name

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (withFrame)

def profile102 : Profile := ⟨sourcesBorrowed, false, "solana_account_info::AccountInfo",
  "solana_address::Address", true, false⟩
end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

/-- Exact recorded 1.0.2 methods selected by the cumulative model registry. -/
def checkedItems102 : List (String × String × String) := [
  ("account", "as_ref_info",
    "<anchor_lang::accounts::account::Account<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("account", "key", "<anchor_lang::accounts::account::Account<'_, T> as \
    anchor_lang::Key>::key"),
  ("interface_account", "as_ref_info",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("interface_account", "key",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
      anchor_lang::Key>::key"),
  ("program", "deref",
    "<anchor_lang::accounts::program::Program<'info, T> as core::ops::deref::Deref>::deref"),
  ("signer", "as_ref_info",
    "<anchor_lang::accounts::signer::Signer<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("signer", "deref",
    "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
  ("system_account", "as_ref_info",
    "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("system_account", "deref",
    "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("system_account", "key",
    "<anchor_lang::accounts::system_account::SystemAccount<'_> as anchor_lang::Key>::key"),
  ("unchecked_account", "as_ref_info",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("unchecked_account", "deref",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("unchecked_account", "key",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
      anchor_lang::Key>::key"),
  ("lib", "key", "<solana_address::Address as anchor_lang::Key>::key")]

def checkers102 : List Checker :=
  checkedItems102.filterMap fun (wrapper, operation, name) => select profile102 wrapper operation
    name

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (withFrame)

def profile029 : Profile := ⟨sourcesBorrowed, true, "solana_program::account_info::AccountI\
  nfo",
  "solana_program::pubkey::Pubkey", true, false⟩
end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open SolanalibTest.Conformance.Library.Families.Anchor (withFrame)

/-- The signed move branch at the borrowed 0.29.0 source profile. -/
def select029 (wrapper operation name : String) : Option Checker :=
  if operation == "into_inner" then
    some (withFrame [("pinned feature profile", profileFrame profile029.debug)]
      (moveChecker moveBindingBorrowed (spell profile029 wrapper operation name)
        (nativeGenerics wrapper operation) (wrapper == "interface_account")))
  else select profile029 wrapper operation name

/-- Exact recorded 0.29.0 methods selected by the cumulative model registry. -/
def checkedItems029 : List (String × String × String) := [
  ("account", "into_inner", "anchor_lang::accounts::account::Account::<'a, T>::into_inner"),
  ("account", "as_ref_info",
    "<anchor_lang::accounts::account::Account<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("account", "deref_mut",
    "<anchor_lang::accounts::account::Account<'_, T> as \
      core::ops::deref::DerefMut>::deref_mut"),
  ("account", "key", "<anchor_lang::accounts::account::Account<'_, T> as \
    anchor_lang::Key>::key"),
  ("account", "clone",
    "<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone"),
  ("interface_account", "as_ref_info",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("interface_account", "deref_mut",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
      core::ops::deref::DerefMut>::deref_mut"),
  ("interface_account", "key",
    "<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
      anchor_lang::Key>::key"),
  ("program", "deref",
    "<anchor_lang::accounts::program::Program<'info, T> as core::ops::deref::Deref>::deref"),
  ("signer", "as_ref_info",
    "<anchor_lang::accounts::signer::Signer<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("signer", "deref",
    "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
  ("lib", "key", "<solana_address::Address as anchor_lang::Key>::key")]

def checkers029 : List Checker :=
  checkedItems029.filterMap fun (wrapper, operation, name) => select029 wrapper operation name

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open SolanalibTest.Conformance.Library.Families.Anchor (withFrame)

/-- The recorded legacy spelling values, independent of storage bindings. -/
def spell027 (wrapper operation name : String) : String :=
  let n := name.replace "solana_account_info::AccountInfo"
    "solana_program::account_info::AccountInfo"
    |>.replace "solana_address::Address" "solana_program::pubkey::Pubkey"
  if (["account", "interface_account", "sysvar"].contains wrapper) &&
      (["deref", "deref_mut"].contains operation) then n.replace "<'_, T>" "<'a, T>"
  else n.replace "<'_, T>" "<'info, T>" |>.replace "<'_>" "<'info>"

theorem spell027_eq (wrapper operation name : String) :
    spell027 wrapper operation name = spell profile029 wrapper operation name := rfl

/-- Exact selected owned-info 0.27.0 branches from the signed native selector. -/
def select027 (wrapper operation name : String) : Option Checker :=
  let function := spell027 wrapper operation name
  let generics := nativeGenerics wrapper operation
  let hasPayload := ["account", "interface_account", "sysvar"].contains wrapper
  let savedOwner := wrapper == "interface_account"
  let chosen := if wrapper = "lib" then
      if operation = "key" then some (pubkeyChecker function) else none
    else match operation with
    | "key" => some (keyChecker function generics hasPayload savedOwner)
    | "as_ref_info" => some (infoChecker .owned infoBindingOwned function generics hasPayload
      savedOwner)
    | "deref" => if hasPayload then some (payloadChecker function generics savedOwner)
        else some (infoChecker .owned infoBindingOwned function generics false savedOwner)
    | "deref_mut" => some (mutableChecker false function generics savedOwner)
    | "set_inner" => some (setChecker function generics savedOwner)
    | _ => none
  chosen.map (withFrame [("pinned feature profile", profileFrame false)])

/-- Exact recorded 0.27.0 methods selected by the cumulative model registry. -/
def checkedItems027 : List (String × String × String) := [
  ("account", "set_inner", "anchor_lang::accounts::account::Account::<'a, T>::set_inner"),
  ("account", "as_ref_info",
    "<anchor_lang::accounts::account::Account<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("account", "deref_mut",
    "<anchor_lang::accounts::account::Account<'_, T> as \
      core::ops::deref::DerefMut>::deref_mut"),
  ("account", "key", "<anchor_lang::accounts::account::Account<'_, T> as \
    anchor_lang::Key>::key"),
  ("program", "deref",
    "<anchor_lang::accounts::program::Program<'info, T> as core::ops::deref::Deref>::deref"),
  ("signer", "as_ref_info",
    "<anchor_lang::accounts::signer::Signer<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("signer", "deref",
    "<anchor_lang::accounts::signer::Signer<'info> as core::ops::deref::Deref>::deref"),
  ("system_account", "deref",
    "<anchor_lang::accounts::system_account::SystemAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("system_account", "key",
    "<anchor_lang::accounts::system_account::SystemAccount<'_> as anchor_lang::Key>::key"),
  ("unchecked_account", "as_ref_info",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"),
  ("unchecked_account", "deref",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as \
      core::ops::deref::Deref>::deref"),
  ("unchecked_account", "key",
    "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'_> as \
      anchor_lang::Key>::key"),
  ("sysvar", "deref",
    "<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::Deref>::deref"),
  ("lib", "key", "<solana_address::Address as anchor_lang::Key>::key")]

def checkers027 : List Checker :=
  checkedItems027.filterMap fun (wrapper, operation, name) => select027 wrapper operation name

end SolanalibTest.Conformance.Library.Families.AnchorViews
