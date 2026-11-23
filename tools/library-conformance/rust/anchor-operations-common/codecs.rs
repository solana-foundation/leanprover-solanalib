//! Boundary cases for one-shot writer calls and the exact selected decoders.
#[cfg(any(feature = "v027", feature = "v029"))]
use crate::private_bpf_writer::BpfWriter;
#[cfg(feature = "v112")]
use crate::{enc, errors};
use crate::{errors::record, track};
#[cfg(not(any(feature = "v027", feature = "v029")))]
use anchor_lang::__private::BpfWriter;
#[cfg(feature = "v112")]
use anchor_lang::AccountDeserialize;
#[cfg(feature = "v027")]
use anchor_lang::AnchorDeserialize;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim as shim;
use std::io::Write;

// Read the public derived Debug observation; no private-field transmute or
// inferred cursor is used by the recorder.
fn writer_value(text: &str) -> Json {
    let data = text.split('[').nth(1).unwrap().split(']').next().unwrap();
    let bytes: Vec<u8> = if data.trim().is_empty() {
        vec![]
    } else {
        data.split(',').map(|x| x.trim().parse().unwrap()).collect()
    };
    let position: u64 = text
        .rsplit("pos: ")
        .next()
        .unwrap()
        .trim_end_matches(" }")
        .parse()
        .unwrap();
    Json::obj([("bytes", rec::bytes(&bytes)), ("position", position.into())])
}
fn write_cases(c: &mut Corpus) {
    for (case, (capacity, prefix, input)) in [
        (0, 0, vec![]),
        (0, 0, vec![1]),
        (4, 0, vec![]),
        (4, 0, vec![1, 2, 3, 4]),
        (4, 1, vec![1, 2, 3, 4, 5]),
        (4, 4, vec![1]),
        (4, 4, vec![]),
        (7, 3, vec![9, 8]),
    ]
    .into_iter()
    .enumerate()
    {
        let mut data = vec![0xa5; capacity];
        let mut writer = BpfWriter::new(data.as_mut_slice());
        writer.write_all(&vec![0x2b; prefix]).expect("prime cursor");
        let before = Json::obj([
            ("writer", writer_value(&format!("{writer:?}"))),
            ("syscalls", shim::Script::new(vec![]).state_before()),
        ]);
        let args = Json::obj([("input", rec::bytes(&input))]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            let (result, log) = track::tracked(|| writer.write_all(&input));
            let state = Json::obj([
                ("writer", writer_value(&format!("{writer:?}"))),
                ("fresh_live", log.fresh_live.len().into()),
                ("syscalls", shim::state()),
            ]);
            match result {
                Ok(r) => {
                    let value = rec::io_result(&r, |_| Json::Null);
                    std::mem::forget(r);
                    rec::returned(value, state)
                }
                Err(reason) => rec::unwound(reason, state),
            }
        });
        record(
            c,
            format!("write_all/{case}"),
            "<anchor_lang::bpf_writer::BpfWriter<&mut [u8]> as std::io::Write>::write_all",
            before,
            args,
            output,
        );
    }
}
#[cfg(feature = "v027")]
fn idl_value(value: &anchor_lang::idl::IdlInstruction) -> Json {
    use anchor_lang::idl::IdlInstruction::*;
    match value {
        Create { data_len } => rec::variant("Create", vec![(*data_len).into()]),
        CreateBuffer => rec::variant("CreateBuffer", vec![]),
        Write { data } => rec::variant("Write", vec![rec::bytes(data)]),
        SetBuffer => rec::variant("SetBuffer", vec![]),
        SetAuthority { new_authority } => {
            rec::variant("SetAuthority", vec![rec::bytes(new_authority.as_ref())])
        }
        Close => rec::variant("Close", vec![]),
        Resize { data_len } => rec::variant("Resize", vec![(*data_len).into()]),
    }
}
#[cfg(feature = "v027")]
fn idl_cases(c: &mut Corpus) {
    let mut cases = vec![
        vec![],
        vec![7],
        vec![255],
        vec![0],
        vec![0, 1, 2],
        vec![1],
        vec![3],
        vec![5],
        vec![4, 1],
        vec![2],
        vec![2, 3, 0, 0],
        vec![2, 3, 0, 0, 0, 7, 8],
        vec![2, 0, 0, 0, 0],
        vec![2, 3, 0, 0, 0, 7, 8, 9, 0xaa],
    ];
    for tag in [0, 6] {
        let mut b = vec![tag];
        b.extend_from_slice(&u64::MAX.to_le_bytes());
        b.push(0xaa);
        cases.push(b);
    }
    let mut authority = vec![4];
    authority.extend_from_slice(&[0x37; 32]);
    authority.push(0xaa);
    cases.push(authority);
    for (i, input) in cases.into_iter().enumerate() {
        let before = Json::obj([("remaining", rec::bytes(&input))]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            let mut remaining = input.as_slice();
            let (r, log) =
                track::tracked(|| anchor_lang::idl::IdlInstruction::deserialize(&mut remaining));
            let state = Json::obj([
                ("remaining", rec::bytes(remaining)),
                ("fresh_live", log.fresh_live.len().into()),
            ]);
            match r {
                Ok(value) => {
                    let result = rec::io_result(&value, idl_value);
                    std::mem::forget(value);
                    rec::returned(result, state)
                }
                Err(reason) => rec::unwound(reason, state),
            }
        });
        record(
            c,
            format!("idl/{i}"),
            "<anchor_lang::idl::IdlInstruction as borsh::de::BorshDeserialize>::deserialize",
            before,
            Json::Null,
            output,
        );
    }
}
#[cfg(feature = "v112")]
fn loader_cases(c: &mut Corpus) {
    use anchor_lang::solana_program::bpf_loader_upgradeable::UpgradeableLoaderState as Loader;
    let mut cases = vec![
        vec![],
        vec![0],
        vec![4, 0, 0, 0],
        vec![0, 0, 0, 0, 0xff],
        vec![1, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 2],
        vec![1, 0, 0, 0, 1, 1],
    ];
    let mut buffer = vec![1, 0, 0, 0, 1];
    buffer.extend_from_slice(&[7; 32]);
    buffer.push(0xee);
    cases.push(buffer);
    let mut program = vec![2, 0, 0, 0];
    program.extend_from_slice(&[8; 32]);
    program.push(0xee);
    cases.push(program);
    for present in [false, true] {
        let mut data = vec![3, 0, 0, 0];
        data.extend_from_slice(&u64::MAX.to_le_bytes());
        data.push(present as u8);
        if present {
            data.extend_from_slice(&[9; 32]);
        }
        data.push(0xee);
        cases.push(data);
    }
    for (i, input) in cases.into_iter().enumerate() {
        let before = Json::obj([("remaining", rec::bytes(&input))]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            let mut remaining = input.as_slice();
            let (r, log) = track::tracked(|| Loader::try_deserialize_unchecked(&mut remaining));
            let value = match r {
                Ok(Ok(v)) => rec::ok(match v {
                    Loader::Uninitialized => rec::variant("Uninitialized", vec![]),
                    Loader::Buffer { authority_address } => rec::variant(
                        "Buffer",
                        vec![authority_address.map_or(Json::Null, |k| rec::bytes(k.as_ref()))],
                    ),
                    Loader::Program {
                        programdata_address,
                    } => rec::variant("Program", vec![rec::bytes(programdata_address.as_ref())]),
                    Loader::ProgramData {
                        slot,
                        upgrade_authority_address,
                    } => rec::variant(
                        "ProgramData",
                        vec![
                            slot.into(),
                            upgrade_authority_address
                                .map_or(Json::Null, |k| rec::bytes(k.as_ref())),
                        ],
                    ),
                }),
                Ok(Err(e)) => {
                    let j = rec::err(enc::error_value(&e));
                    std::mem::forget(e);
                    j
                }
                Err(reason) => {
                    return rec::unwound(reason, Json::obj([("remaining", rec::bytes(remaining))]))
                }
            };
            rec::returned(
                value,
                Json::obj([
                    ("remaining", rec::bytes(remaining)),
                    ("fresh_live", log.fresh_live.len().into()),
                ]),
            )
        });
        record(c,format!("loader/{i}"),"anchor_lang::bpf_upgradeable_state::<impl anchor_lang::AccountDeserialize for solana_loader_v3_interface::state::UpgradeableLoaderState>::try_deserialize_unchecked",before,Json::Null,output);
    }
}
#[cfg(feature = "v112")]
#[derive(Debug)]
struct DefaultDecode(u8);
#[cfg(feature = "v112")]
impl AccountDeserialize for DefaultDecode {
    fn try_deserialize_unchecked(buf: &mut &[u8]) -> anchor_lang::Result<Self> {
        errors::event("unchecked");
        let mode = buf.first().copied().unwrap_or(0);
        *buf = &buf[buf.len().min(1)..];
        if mode == 2 {
            panic!("unchecked");
        }
        if mode == 1 {
            return Err(
                anchor_lang::solana_program::program_error::ProgramError::InvalidAccountData.into(),
            );
        }
        Ok(Self(17))
    }
}
#[cfg(feature = "v112")]
fn default_cases(c: &mut Corpus) {
    for mode in 0..3u8 {
        let input = vec![mode, 0x77, 0x88];
        let before = Json::obj([
            ("remaining", rec::bytes(&input)),
            ("callbacks", Json::Arr(vec![])),
        ]);
        let output = shim::case(&shim::Script::new(vec![]), || {
            errors::reset();
            let mut remaining = input.as_slice();
            let (r, log) = track::tracked(|| DefaultDecode::try_deserialize(&mut remaining));
            let state = Json::obj([
                ("remaining", rec::bytes(remaining)),
                ("callbacks", errors::events()),
                ("fresh_live", log.fresh_live.len().into()),
            ]);
            match r {
                Ok(Ok(v)) => rec::returned(rec::ok(v.0.into()), state),
                Ok(Err(e)) => {
                    let value = rec::err(enc::error_value(&e));
                    std::mem::forget(e);
                    rec::returned(value, state)
                }
                Err(reason) => rec::unwound(reason, state),
            }
        });
        record(
            c,
            format!("default_decode/{mode}"),
            "anchor_lang::AccountDeserialize::try_deserialize",
            before,
            Json::Null,
            output,
        );
    }
}
pub fn record_all(c: &mut Corpus) {
    write_cases(c);
    #[cfg(feature = "v027")]
    idl_cases(c);
    #[cfg(feature = "v112")]
    {
        loader_cases(c);
        default_cases(c);
    }
}

#[cfg(all(test, feature = "v032"))]
mod tests {
    use super::*;

    #[test]
    fn short_write_leaves_the_writer_exhausted_for_later_calls() {
        let observed = shim::case(&shim::Script::new(vec![]), || {
            let mut bytes = [0xa5; 2];
            let mut writer = BpfWriter::new(bytes.as_mut_slice());
            let first = writer.write_all(&[0x11, 0x22, 0x33]).unwrap_err();
            assert_eq!(first.kind(), std::io::ErrorKind::WriteZero);
            assert_eq!(first.to_string(), "failed to write whole buffer");
            let after_short = writer_value(&format!("{writer:?}"));
            assert_eq!(
                after_short,
                Json::obj([
                    ("bytes", rec::bytes(&[0x11, 0x22])),
                    ("position", 2u64.into()),
                ])
            );
            let copied = shim::state();

            let second = writer.write_all(&[0x44]).unwrap_err();
            assert_eq!(second.kind(), std::io::ErrorKind::WriteZero);
            writer.write_all(&[]).unwrap();
            assert_eq!(writer_value(&format!("{writer:?}")), after_short);
            assert_eq!(shim::state(), copied);
            drop(writer);
            assert_eq!(bytes, [0x11, 0x22]);
            Json::Bool(true)
        });
        assert_eq!(observed.to_text(), "true");
    }
}
