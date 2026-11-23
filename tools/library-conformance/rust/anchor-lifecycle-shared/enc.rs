//! Observable Anchor errors, including the legacy owned Borsh error String.

use anchor_lang::error::{ComparedValues, Error, ErrorOrigin};
use anchor_lang::solana_program::program_error::ProgramError;
use conformance_recorder::{self as rec, Json};

fn tagged(name: &str, value: Json) -> Json {
    Json::Obj(vec![(name.to_string(), value)])
}

pub fn program_error(value: &ProgramError) -> Json {
    let name = match value {
        ProgramError::Custom(code) => return rec::variant("Custom", vec![(*code).into()]),
        ProgramError::InvalidArgument => "InvalidArgument",
        ProgramError::InvalidAccountData => "InvalidAccountData",
        ProgramError::AccountBorrowFailed => "AccountBorrowFailed",
        ProgramError::InvalidRealloc => "InvalidRealloc",
        #[cfg(not(feature = "legacy-anchor"))]
        ProgramError::ArithmeticOverflow => "ArithmeticOverflow",
        #[cfg(feature = "legacy-program-error")]
        ProgramError::BorshIoError(text) => return rec::variant("BorshIoError", vec![text.as_str().into()]),
        #[cfg(not(feature = "legacy-program-error"))]
        ProgramError::BorshIoError => "BorshIoError",
        _ => panic!("unexpected program error in lifecycle corpus"),
    };
    rec::variant(name, vec![])
}

fn origin(value: &Option<ErrorOrigin>) -> Json {
    match value {
        None => Json::Null,
        Some(ErrorOrigin::Source(source)) => tagged("Source", Json::obj([
            ("filename", source.filename.into()), ("line", source.line.into())])),
        Some(ErrorOrigin::AccountName(name)) => tagged("AccountName", name.as_str().into()),
    }
}

fn compared(value: &Option<ComparedValues>) -> Json {
    match value {
        None => Json::Null,
        Some(ComparedValues::Pubkeys((left, right))) => tagged("Pubkeys",
            Json::Arr(vec![rec::bytes(left.as_ref()), rec::bytes(right.as_ref())])),
        Some(ComparedValues::Values((left, right))) => tagged("Values",
            Json::Arr(vec![left.as_str().into(), right.as_str().into()])),
    }
}

pub fn error(value: &Error) -> Json {
    match value {
        Error::AnchorError(error) => tagged("AnchorError", Json::obj([
            ("name", error.error_name.as_str().into()),
            ("code", error.error_code_number.into()),
            ("message", error.error_msg.as_str().into()),
            ("origin", origin(&error.error_origin)),
            ("compared", compared(&error.compared_values)),
        ])),
        Error::ProgramError(error) => tagged("ProgramError", Json::obj([
            ("error", program_error(&error.program_error)),
            ("origin", origin(&error.error_origin)),
            ("compared", compared(&error.compared_values)),
        ])),
    }
}

pub fn result<T>(value: &anchor_lang::Result<T>, ok: impl FnOnce(&T) -> Json) -> Json {
    match value {
        Ok(value) => rec::ok(ok(value)),
        Err(value) => rec::err(error(value)),
    }
}
