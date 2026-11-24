//! Hash transport only: the scripted bytes are provider outputs, not SHA vectors.
use crate::{hash, hashv};
use crate::syscall_cases::*;
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim::{Reply, Script};

pub fn record(c: &mut Corpus, single: &'static str, many: Option<&'static str>, initialized: bool) {
    let fields = vec![vec![], vec![vec![]], vec![vec![0,1,255]],
        vec![vec![1,2],vec![],vec![3,4]], vec![pattern(129, 7)]];
    let mut replies = vec![("full", Reply::new("sol_sha256", 0).data(&pattern(32, 9))),
        ("nonzero", Reply::new("sol_sha256", 7).data(&pattern(32, 11))),
        ("max_status", Reply::new("sol_sha256", u64::MAX).data(&pattern(32, 13))),
        ("terminated", Reply::new("sol_sha256", 0).terminate("hash compute exhausted"))];
    if initialized {
        replies.extend([( "unchanged", Reply::new("sol_sha256", 0)),
            ("unchanged_error", Reply::new("sol_sha256", 7)),
            ("one_byte", Reply::new("sol_sha256", 0).data(&[255])),
            ("prefix_error", Reply::new("sol_sha256", 7).data(&pattern(31, 3)))]);
    }
    for (number, data) in fields.iter().enumerate() {
        if let Some(function) = many {
            for (case, reply) in &replies {
                syscall_case(c, format!("hashv/{number}/{case}"), function, hex_fields(data),
                    Script::new(vec![reply.clone()]), || hashv(&data.iter().map(Vec::as_slice).collect::<Vec<_>>()),
                    |value| rec::bytes(&value.to_bytes()));
            }
        }
        let bytes: Vec<u8> = data.concat();
        for (case, reply) in &replies {
            syscall_case(c, format!("hash/{number}/{case}"), single, rec::bytes(&bytes),
                Script::new(vec![reply.clone()]), || hash(&bytes), |value| rec::bytes(&value.to_bytes()));
        }
    }
}

pub fn to_bytes(c: &mut Corpus, function: &'static str, call: impl Fn([u8;32])->[u8;32]) {
    for (case, bytes) in [[0;32],[255;32],core::array::from_fn(|i| i as u8)].into_iter().enumerate() {
        c.push(rec::Record { id: format!("to_bytes/{case}"), function, generics: vec![], layout: None,
            state: Json::Null, args: rec::bytes(&bytes), outcome: rec::returned(rec::bytes(&call(bytes)),Json::Null), observed:None });
    }
}
