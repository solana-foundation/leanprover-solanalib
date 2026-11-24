//! Direct calls of the two published 5.2.0 declarations. All provider results
//! are explicit scripts, not computations of SHA-512 or group arithmetic.

#[path = "../../runtime-common/syscall_cases.rs"]
#[allow(dead_code)]
mod syscall_cases;

use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim::{Reply, Script};
use solana_define_syscall::definitions as syscall;
use syscall_cases::syscall_case;

const HASH: &str = "solana_define_syscall::definitions::sol_sha512";
const MSM: &str = "solana_define_syscall::definitions::sol_curve_multiscalar_mul";

fn initial(width: usize) -> Vec<u8> {
    let mut result = vec![0xa5; width + 16];
    result[..8].fill(0x3c);
    result[width + 8..].fill(0xc3);
    result
}

fn guards(buffer: &[u8]) -> Vec<u8> {
    [buffer[..8].to_vec(), buffer[buffer.len() - 8..].to_vec()].concat()
}

fn returned(status: u64, buffer: &[u8]) -> Json {
    Json::obj([
        ("status", status.into()),
        ("output", rec::bytes(&buffer[8..buffer.len() - 8])),
        ("guards", rec::bytes(&guards(buffer))),
    ])
}

fn hash_cases(corpus: &mut Corpus) {
    let groups: Vec<(&str, Vec<Vec<u8>>)> = vec![
        ("empty", vec![]),
        ("one", vec![vec![0, 1, 0xff, 0x80, 3]]),
        ("segmented", vec![vec![1, 2], vec![], vec![1, 2], vec![3]]),
    ];
    for (name, fields) in groups {
        for (result, reply) in [
            ("success", Reply::new("sol_sha512", 0).data(&(0..64).collect::<Vec<u8>>())),
            ("failure", Reply::new("sol_sha512", 1)),
            ("max_status", Reply::new("sol_sha512", u64::MAX)),
            ("terminal", Reply::new("sol_sha512", 0).terminate("scripted terminal")),
        ] {
            let script = Script::new(vec![reply]);
            let before = initial(64);
            let args = Json::obj([
                ("slices", Json::arr(&fields, |b| rec::bytes(b))),
                ("output", rec::bytes(&before[8..72])),
                ("guards", rec::bytes(&guards(&before))),
            ]);
            syscall_case(corpus, format!("sha512/{name}/{result}"), HASH, args, script, || {
                let mut buffer = before;
                let slices: Vec<&[u8]> = fields.iter().map(Vec::as_slice).collect();
                let status = unsafe {
                    syscall::sol_sha512(slices.as_ptr().cast(), slices.len() as u64,
                                        buffer.as_mut_ptr().add(8))
                };
                (status, buffer)
            }, |(status, buffer)| returned(*status, buffer));
        }
    }
}

fn msm_case(corpus: &mut Corpus, curve: u64, count: usize, name: &str, reply: Option<Reply>) {
    let script = Script::new(reply.into_iter().collect());
    let scalars: Vec<[u8; 32]> = (0..count).map(|i| {
        let mut scalar = [0; 32];
        scalar[0] = (i % 3) as u8;
        scalar
    }).collect();
    let mut identity = [0; 32];
    if curve == 0 { identity[0] = 1; }
    let points = vec![identity; count];
    let before = initial(32);
    let args = Json::obj([
        ("curve_id", curve.into()), ("count", count.into()),
        ("scalars", Json::arr(&scalars, |b| rec::bytes(b))),
        ("points", Json::arr(&points, |b| rec::bytes(b))),
        ("output", rec::bytes(&before[8..40])),
        ("guards", rec::bytes(&guards(&before))),
    ]);
    syscall_case(corpus, format!("msm/{curve}/{count}/{name}"), MSM, args, script, || {
        let mut buffer = before;
        // The count and invalid-curve branches must return/terminate before
        // reading either input pointer. Nulls turn an accidental read into a
        // failed recording, not another scripted outcome.
        let (scalar_ptr, point_ptr) = if count > 512 || curve > 1 || count == 0 {
            (core::ptr::null(), core::ptr::null())
        } else {
            (scalars.as_ptr().cast(), points.as_ptr().cast())
        };
        let result_ptr = if count > 512 || curve > 1 {
            core::ptr::null_mut()
        } else {
            unsafe { buffer.as_mut_ptr().add(8) }
        };
        let status = unsafe {
            syscall::sol_curve_multiscalar_mul(curve, scalar_ptr, point_ptr, count as u64, result_ptr)
        };
        (status, buffer)
    }, |(status, buffer)| returned(*status, buffer));
}

fn main() {
    rec::init();
    let mut corpus = Corpus::new("solana_define_syscall_5_2_0", &[("solana-define-syscall", "5.2.0")]);
    hash_cases(&mut corpus);
    for curve in [0, 1] {
        for count in [0, 1, 3, 512] {
            msm_case(&mut corpus, curve, count, "success",
                Some(Reply::new("sol_curve_multiscalar_mul", 0).data(&[0x5a; 32])));
            msm_case(&mut corpus, curve, count, "failure",
                Some(Reply::new("sol_curve_multiscalar_mul", 1)));
            msm_case(&mut corpus, curve, count, "terminal",
                Some(Reply::new("sol_curve_multiscalar_mul", 0).terminate("scripted terminal")));
        }
    }
    for curve in [2, u64::MAX] {
        for count in [0, 2] {
            msm_case(&mut corpus, curve, count, "invalid",
                Some(Reply::new("sol_curve_multiscalar_mul", 1)));
            msm_case(&mut corpus, curve, count, "invalid_terminal",
                Some(Reply::new("sol_curve_multiscalar_mul", 0).terminate("invalid curve")));
        }
    }
    for curve in [0, 2] {
        msm_case(&mut corpus, curve, 513, "over_limit", None);
    }
    corpus.write(&rec::out_dir()).expect("write corpus");
}
