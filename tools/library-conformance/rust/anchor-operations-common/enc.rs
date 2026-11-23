//! JSON encodings shared by the Anchor cases (the Lean readers are in
//! the version-specific Anchor operations checker).

use anchor_lang::error::{AnchorError, ComparedValues, Error, ErrorOrigin, ProgramErrorWithOrigin};
use anchor_lang::solana_program::program_error::ProgramError;
use conformance_recorder::{self as rec, Json};

use crate::track;

pub fn key(k: &anchor_lang::prelude::Pubkey) -> Json {
    rec::bytes(k.as_ref())
}

/// solana-program-error 3.0.1 variants by name (exhaustive).
pub fn program_error(e: &ProgramError) -> Json {
    let name = match e {
        ProgramError::Custom(code) => return rec::variant("Custom", vec![(*code).into()]),
        ProgramError::InvalidArgument => "InvalidArgument",
        ProgramError::InvalidInstructionData => "InvalidInstructionData",
        ProgramError::InvalidAccountData => "InvalidAccountData",
        ProgramError::AccountDataTooSmall => "AccountDataTooSmall",
        ProgramError::InsufficientFunds => "InsufficientFunds",
        ProgramError::IncorrectProgramId => "IncorrectProgramId",
        ProgramError::MissingRequiredSignature => "MissingRequiredSignature",
        ProgramError::AccountAlreadyInitialized => "AccountAlreadyInitialized",
        ProgramError::UninitializedAccount => "UninitializedAccount",
        ProgramError::NotEnoughAccountKeys => "NotEnoughAccountKeys",
        ProgramError::AccountBorrowFailed => "AccountBorrowFailed",
        ProgramError::MaxSeedLengthExceeded => "MaxSeedLengthExceeded",
        ProgramError::InvalidSeeds => "InvalidSeeds",
        #[cfg(not(feature = "legacy"))]
        ProgramError::BorshIoError => "BorshIoError",
        #[cfg(feature = "legacy")]
        ProgramError::BorshIoError(message) => {
            return rec::variant("BorshIoError", vec![text(message)])
        }
        ProgramError::AccountNotRentExempt => "AccountNotRentExempt",
        ProgramError::UnsupportedSysvar => "UnsupportedSysvar",
        ProgramError::IllegalOwner => "IllegalOwner",
        ProgramError::MaxAccountsDataAllocationsExceeded => "MaxAccountsDataAllocationsExceeded",
        ProgramError::InvalidRealloc => "InvalidRealloc",
        ProgramError::MaxInstructionTraceLengthExceeded => "MaxInstructionTraceLengthExceeded",
        #[cfg(not(feature = "v027"))]
        ProgramError::BuiltinProgramsMustConsumeComputeUnits => {
            "BuiltinProgramsMustConsumeComputeUnits"
        }
        #[cfg(not(feature = "v027"))]
        ProgramError::InvalidAccountOwner => "InvalidAccountOwner",
        #[cfg(not(feature = "v027"))]
        ProgramError::ArithmeticOverflow => "ArithmeticOverflow",
        #[cfg(not(any(feature = "v027", feature = "v029")))]
        ProgramError::Immutable => "Immutable",
        #[cfg(not(any(feature = "v027", feature = "v029")))]
        ProgramError::IncorrectAuthority => "IncorrectAuthority",
    };
    rec::variant(name, vec![])
}

fn tagged(k: &str, v: Json) -> Json {
    Json::Obj(vec![(k.to_string(), v)])
}

/// How a String field is written: its text (values) or its identity (payloads).
type Str<'a> = &'a dyn Fn(&String) -> Json;

fn origin(o: &Option<ErrorOrigin>, s: Str) -> Json {
    match o {
        None => Json::Null,
        Some(ErrorOrigin::Source(src)) => tagged(
            "Source",
            Json::obj([("filename", src.filename.into()), ("line", src.line.into())]),
        ),
        Some(ErrorOrigin::AccountName(n)) => tagged("AccountName", s(n)),
    }
}

fn compared(c: &Option<ComparedValues>, s: Str) -> Json {
    match c {
        None => Json::Null,
        Some(ComparedValues::Values((l, r))) => tagged("Values", Json::Arr(vec![s(l), s(r)])),
        Some(ComparedValues::Pubkeys((l, r))) => tagged("Pubkeys", Json::Arr(vec![key(l), key(r)])),
    }
}

fn anchor_error(e: &AnchorError, s: Str) -> Json {
    tagged(
        "AnchorError",
        Json::obj([
            ("name", s(&e.error_name)),
            ("code", e.error_code_number.into()),
            ("message", s(&e.error_msg)),
            ("origin", origin(&e.error_origin, s)),
            ("compared", compared(&e.compared_values, s)),
        ]),
    )
}

fn program_error_with_origin(e: &ProgramErrorWithOrigin, s: Str) -> Json {
    tagged(
        "ProgramError",
        Json::obj([
            ("error", {
                #[cfg(feature = "legacy")]
                {
                    if let ProgramError::BorshIoError(message) = &e.program_error {
                        rec::variant("BorshIoError", vec![s(message)])
                    } else {
                        program_error(&e.program_error)
                    }
                }
                #[cfg(not(feature = "legacy"))]
                {
                    program_error(&e.program_error)
                }
            }),
            ("origin", origin(&e.error_origin, s)),
            ("compared", compared(&e.compared_values, s)),
        ]),
    )
}

fn text(s: &String) -> Json {
    s.as_str().into()
}

/// The full value of an `anchor_lang::error::Error`.
pub fn error_value(e: &Error) -> Json {
    match e {
        Error::AnchorError(ae) => anchor_error(ae, &text),
        Error::ProgramError(pe) => program_error_with_origin(pe, &text),
    }
}

/// The Strings an error owns, in declaration order (the `Payload.strings` model field).
pub fn owned_strings(e: &Error) -> Vec<&String> {
    let (head, origin, compared): (Vec<&String>, _, _) = match e {
        Error::AnchorError(ae) => (
            vec![&ae.error_name, &ae.error_msg],
            &ae.error_origin,
            &ae.compared_values,
        ),
        Error::ProgramError(pe) => {
            #[cfg(feature = "legacy")]
            let strings = if let ProgramError::BorshIoError(s) = &pe.program_error {
                vec![s]
            } else {
                vec![]
            };
            #[cfg(not(feature = "legacy"))]
            let strings = vec![];
            (strings, &pe.error_origin, &pe.compared_values)
        }
    };
    let mut out = head;
    if let Some(ErrorOrigin::AccountName(n)) = origin {
        out.push(n);
    }
    if let Some(ComparedValues::Values((l, r))) = compared {
        out.push(l);
        out.push(r);
    }
    out
}

#[cfg(not(feature = "v027"))]
pub fn box_addr(e: &Error) -> usize {
    match e {
        Error::AnchorError(ae) => &**ae as *const AnchorError as usize,
        Error::ProgramError(pe) => &**pe as *const ProgramErrorWithOrigin as usize,
    }
}

#[cfg(feature = "v027")]
pub fn box_addr(_: &Error) -> usize {
    0
}

pub fn string_addr(s: &String) -> usize {
    s.as_ptr() as usize
}

/// Input heap resources of a case: String texts and addresses, Box addresses.
#[derive(Default)]
pub struct Heap {
    pub texts: Vec<String>,
    pub strings: Vec<usize>,
    pub boxes: Vec<usize>,
    pub box_payloads: Vec<Json>,
}

impl Heap {
    /// Register the Strings owned by an error (and, if `boxed`, its Box) as inputs.
    pub fn add_error(&mut self, e: &Error, boxed: bool) -> usize {
        for s in owned_strings(e) {
            assert!(s.capacity() > 0, "input Strings must own an allocation");
            self.texts.push(s.clone());
            self.strings.push(string_addr(s));
        }
        if boxed && !cfg!(feature = "v027") {
            self.box_payloads
                .push(self.payload(e, &track::Log::default()));
            self.boxes.push(box_addr(e));
        }
        self.boxes.len().wrapping_sub(1)
    }

    pub fn add_anchor_error(&mut self, e: &AnchorError) {
        let mut push = |s: &String| {
            assert!(s.capacity() > 0, "input Strings must own an allocation");
            self.texts.push(s.clone());
            self.strings.push(string_addr(s));
        };
        push(&e.error_name);
        push(&e.error_msg);
        if let Some(ErrorOrigin::AccountName(n)) = &e.error_origin {
            push(n);
        }
        if let Some(ComparedValues::Values((l, r))) = &e.compared_values {
            push(l);
            push(r);
        }
    }

    /// An input id, or null for a resource allocated during the call.
    fn id(addr: usize, inputs: &[usize], log: &track::Log, empty: bool) -> Json {
        if empty || log.allocs.contains(&addr) {
            return Json::Null;
        }
        match inputs.iter().position(|a| *a == addr) {
            Some(i) => i.into(),
            None => {
                panic!("resource at {addr:#x} is neither an input nor allocated during the call")
            }
        }
    }

    pub fn string_id(&self, s: &String, log: &track::Log) -> Json {
        Self::id(string_addr(s), &self.strings, log, s.capacity() == 0)
    }

    pub fn box_id(&self, e: &Error, log: &track::Log) -> Json {
        if cfg!(feature = "v027") {
            Json::Null
        } else {
            Self::id(box_addr(e), &self.boxes, log, false)
        }
    }

    /// The error with its Strings written as identities.
    pub fn payload(&self, e: &Error, log: &track::Log) -> Json {
        let id = |s: &String| self.string_id(s, log);
        match e {
            Error::AnchorError(ae) => anchor_error(ae, &id),
            Error::ProgramError(pe) => program_error_with_origin(pe, &id),
        }
    }

    pub fn anchor_payload(&self, e: &AnchorError, log: &track::Log) -> Json {
        let id = |s: &String| self.string_id(s, log);
        anchor_error(e, &id)
    }

    /// `{"strings": [...], "boxes": [...]}` before the call.
    pub fn state_before(&self) -> Vec<(&'static str, Json)> {
        vec![
            (
                "strings",
                Json::arr(self.texts.iter(), |t| t.as_str().into()),
            ),
            ("boxes", Json::Arr(self.box_payloads.clone())),
        ]
    }

    /// Liveness of the input resources after the call.
    pub fn state_after(&self, log: &track::Log) -> Vec<(&'static str, Json)> {
        vec![
            (
                "strings_live",
                Json::arr(self.strings.iter(), |a| (!log.frees.contains(a)).into()),
            ),
            (
                "boxes_live",
                Json::arr(self.boxes.iter(), |a| (!log.frees.contains(a)).into()),
            ),
            ("fresh_live", log.fresh_live.len().into()),
        ]
    }

    /// The observation of a returned owned error.
    pub fn error_obs(&self, e: &Error, log: &track::Log) -> Json {
        Json::obj([
            ("box", self.box_id(e, log)),
            ("value", error_value(e)),
            (
                "strings",
                Json::arr(owned_strings(e), |s| self.string_id(s, log)),
            ),
        ])
    }
}
