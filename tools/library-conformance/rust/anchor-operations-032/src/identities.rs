//! Actual defining Rust items; reexports do not change these identities.
pub const FROM_CODE: &str = "<anchor_lang::error::Error as core::convert::From<anchor_lang::error::ErrorCode>>::from";
pub const FROM_ANCHOR: &str = "<anchor_lang::error::Error as core::convert::From<anchor_lang::error::AnchorError>>::from";
pub const FROM_PROGRAM: &str = "<anchor_lang::error::Error as core::convert::From<solana_program_error::ProgramError>>::from";
pub const FROM_IO: &str = "<anchor_lang::error::Error as core::convert::From<std::io::error::Error>>::from";
pub const EQUAL: &str = "<anchor_lang::error::Error as core::cmp::PartialEq>::eq";
pub const CONTEXT_NEW: &str = "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new";
pub const CPI_NEW: &str = "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new";
pub const CPI_SIGNED: &str = "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer";
pub const CPI_WITH_SIGNER: &str = "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer";
pub const CPI_WITH_REMAINING: &str = "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_remaining_accounts";

/// Reviewed source functions recorded by this exact versioned driver.
pub const FUNCTIONS: &[&str] = &[
    "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all",
    "<anchor_lang::error::Error as core::cmp::PartialEq>::eq",
    "<anchor_lang::error::Error as core::convert::From<anchor_lang::error::ErrorCode>>::from",
    "<anchor_lang::error::Error as core::convert::From<std::io::error::Error>>::from",
    "anchor_lang::context::Context::<'a, 'b, 'c, 'info, T>::new",
    "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new",
    "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer",
    "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::with_signer",
    "anchor_lang::error::Error::log",
    "anchor_lang::error::Error::with_account_name",
    "anchor_lang::error::Error::with_pubkeys",
    "anchor_lang::error::Error::with_values",
    "anchor_lang::error::ErrorCode::name",
];
