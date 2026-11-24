//! The shim controls: request logging, replies, script errors and terminal exits.

use conformance_recorder::{self as rec, Json};
use conformance_shim::{self as shim, Reply, Script};

extern "C" {
    fn sol_log_(message: *const u8, len: u64);
    fn sol_get_clock_sysvar(addr: *mut u8) -> u64;
    fn sol_sha256(vals: *const u8, val_len: u64, hash_result: *mut u8) -> u64;
    fn sol_memcmp_(s1: *const u8, s2: *const u8, n: u64, result: *mut i32);
    fn sol_panic_(filename: *const u8, filename_len: u64, line: u64, column: u64) -> !;
    fn sol_invoke_signed_c(instruction_addr: *const u8, account_infos_addr: *const u8, account_infos_len: u64,
                           signers_seeds_addr: *const u8, signers_seeds_len: u64) -> u64;
}

fn text(j: &Json) -> String {
    j.to_text()
}

#[test]
fn logs_requests_and_consumes_replies() {
    rec::init();
    let script = Script::new(vec![
        Reply::new("sol_get_clock_sysvar", 0).data(&[7u8; 40]),
        Reply::new("sol_sha256", 0).data(&[9u8; 32]),
    ]);
    let outcome = shim::case(&script, || unsafe {
        sol_log_(b"hi".as_ptr(), 2);
        let mut clock = [0u8; 40];
        let rc = sol_get_clock_sysvar(clock.as_mut_ptr());
        let fields: [&[u8]; 2] = [b"ab", b"c"];
        let mut hash = [0u8; 32];
        sol_sha256(fields.as_ptr() as *const u8, 2, hash.as_mut_ptr());
        let mut cmp = 0;
        sol_memcmp_(b"ab".as_ptr(), b"ac".as_ptr(), 2, &mut cmp);
        rec::returned(Json::arr([rc as i64, clock[0] as i64, hash[31] as i64, cmp as i64], Json::from),
                      Json::obj([("syscalls", shim::state())]))
    });
    let t = text(&outcome);
    assert!(t.starts_with(r#"{"exit":"returned","result":[0,7,9,-1]"#), "{t}");
    assert!(t.contains(r#"{"syscall":"sol_log_","bytes":"6869"}"#), "{t}");
    assert!(t.contains(r#"{"syscall":"sol_sha256","fields":["6162","63"]}"#), "{t}");
    assert!(t.contains(r#""replies":[]"#), "{t}");
}

#[test]
fn sol_panic_terminates_with_its_arguments_and_the_log() {
    rec::init();
    let outcome = shim::case(&Script::default(), || unsafe {
        sol_log_(b"x".as_ptr(), 1);
        sol_panic_(b"f.rs".as_ptr(), 4, 3, 5)
    });
    let t = text(&outcome);
    assert!(t.starts_with(r#"{"exit":"terminated","reason":"sol_panic_","detail":{"file":"662e7273","line":3,"column":5}"#), "{t}");
    assert!(t.contains(r#""log":[{"syscall":"sol_log_","bytes":"78"}]"#), "{t}");
}

#[test]
fn a_reply_marked_terminate_ends_the_case() {
    rec::init();
    let script = Script::new(vec![Reply::new("sol_get_clock_sysvar", 0).terminate("runtime error")]);
    let outcome = shim::case(&script, || unsafe {
        let mut clock = [0u8; 40];
        sol_get_clock_sysvar(clock.as_mut_ptr());
        rec::returned(Json::Null, Json::Null)
    });
    assert!(text(&outcome).starts_with(r#"{"exit":"terminated","reason":"sol_get_clock_sysvar","detail":"runtime error""#));
}

#[test]
fn rust_panics_are_unwound_with_the_syscall_state() {
    rec::init();
    let outcome = shim::case(&Script::default(), || -> Json { panic!("boom") });
    assert_eq!(text(&outcome), r#"{"exit":"unwound","reason":"boom","state":{"syscalls":{"replies":[],"log":[]}}}"#);
}

#[test]
fn std_abort_is_a_terminated_exit() {
    rec::init();
    let outcome = shim::case(&Script::default(), || -> Json { std::process::abort() });
    assert!(text(&outcome).starts_with(r#"{"exit":"terminated","reason":"abort""#), "{}", text(&outcome));
}

#[test]
#[should_panic(expected = "script error")]
fn a_missing_reply_is_a_recorder_error() {
    rec::init();
    shim::case(&Script::default(), || unsafe {
        let mut clock = [0u8; 40];
        sol_get_clock_sysvar(clock.as_mut_ptr());
        Json::Null
    });
}

#[test]
fn cpi_flags_are_read_as_bytes_and_the_raw_header_is_opt_in() {
    rec::init();
    let key = [7u8; 32];
    let mut lamports = 5u64;
    let mut data = [1u8, 2];
    // SolAccountInfo with noncanonical flag bytes 2, 0, 0xff and padding byte 9.
    let mut info = [0u8; 56];
    info[0..8].copy_from_slice(&(key.as_ptr() as u64).to_le_bytes());
    info[8..16].copy_from_slice(&(&mut lamports as *mut u64 as u64).to_le_bytes());
    info[16..24].copy_from_slice(&2u64.to_le_bytes());
    info[24..32].copy_from_slice(&(data.as_mut_ptr() as u64).to_le_bytes());
    info[32..40].copy_from_slice(&(key.as_ptr() as u64).to_le_bytes());
    info[48..52].copy_from_slice(&[2, 0, 0xff, 9]);
    let mut ix = [0u8; 40];
    ix[0..8].copy_from_slice(&(key.as_ptr() as u64).to_le_bytes());
    let info_words: [u64; 7] = core::array::from_fn(|i| u64::from_le_bytes(info[8 * i..8 * i + 8].try_into().unwrap()));
    let ix_words: [u64; 5] = core::array::from_fn(|i| u64::from_le_bytes(ix[8 * i..8 * i + 8].try_into().unwrap()));
    for raw in [false, true] {
        shim::log_cpi_raw_header(raw);
        let script = Script::new(vec![Reply::new("sol_invoke_signed_c", 0)]);
        let outcome = shim::case(&script, || unsafe {
            sol_invoke_signed_c(ix_words.as_ptr() as *const u8, info_words.as_ptr() as *const u8, 1,
                                core::ptr::null(), 0);
            rec::returned(Json::Null, Json::obj([("syscalls", shim::state())]))
        });
        let t = text(&outcome);
        assert!(t.contains(r#""is_signer":true,"is_writable":false,"executable":true"#), "{t}");
        assert_eq!(t.contains(r#""header":[2,0,255,9]"#), raw, "{t}");
    }
    shim::log_cpi_raw_header(false);
}

extern "C" {
    fn sol_get_return_data(data: *mut u8, length: u64, program_id: *mut u8) -> u64;
}

#[test]
fn sysvar_getters_honour_the_status_and_return_data_follows_agave() {
    rec::init();
    let script = Script::new(vec![
        Reply::new("sol_get_clock_sysvar", 1).data(&[7u8; 40]),
        Reply::new("sol_get_return_data", 3).data(&[1, 2, 3]).program_id([9; 32]),
        Reply::new("sol_get_return_data", 3).data(&[1, 2, 3]).program_id([9; 32]),
    ]);
    let outcome = shim::case(&script, || unsafe {
        let mut clock = [0u8; 40];
        let status = sol_get_clock_sysvar(clock.as_mut_ptr());
        let (mut data, mut id) = ([0u8; 2], [0u8; 32]);
        let full = sol_get_return_data(data.as_mut_ptr(), 0, id.as_mut_ptr());
        let untouched = id[0];
        sol_get_return_data(data.as_mut_ptr(), 2, id.as_mut_ptr());
        rec::returned(Json::arr([status as i64, clock[0] as i64, full as i64, untouched as i64,
                                 data[1] as i64, id[0] as i64], Json::from), Json::Null)
    });
    assert!(text(&outcome).starts_with(r#"{"exit":"returned","result":[1,0,3,0,2,9]"#), "{}", text(&outcome));
}

#[test]
#[should_panic(expected = "sol_get_return_data: the reply's value 5 differs from its data length 3")]
fn a_return_data_reply_whose_value_is_not_its_length_is_a_shim_fault() {
    rec::init();
    let script = Script::new(vec![Reply::new("sol_get_return_data", 5).data(&[1, 2, 3]).program_id([9; 32])]);
    shim::case(&script, || unsafe {
        let (mut data, mut id) = ([0u8; 8], [0u8; 32]);
        sol_get_return_data(data.as_mut_ptr(), 8, id.as_mut_ptr());
        Json::Null
    });
}

#[test]
fn a_long_sysvar_reply_is_bounded_by_the_sysvar_size() {
    rec::init();
    let script = Script::new(vec![Reply::new("sol_get_clock_sysvar", 0).data(&[7u8; 41])]);
    let outcome = shim::case(&script, || unsafe {
        let mut clock = [0u8; 41];
        sol_get_clock_sysvar(clock.as_mut_ptr());
        rec::returned(Json::arr([clock[39] as i64, clock[40] as i64], Json::from), Json::Null)
    });
    assert!(text(&outcome).starts_with(r#"{"exit":"returned","result":[7,0]"#), "{}", text(&outcome));
}

extern "C" fn panics_without_unwinding() {
    panic!("inside an extern C function");
}

#[test]
#[should_panic(expected = "panic without unwinding: inside an extern C function")]
fn a_panic_that_cannot_unwind_is_a_shim_fault() {
    rec::init();
    shim::case(&Script::default(), || {
        panics_without_unwinding();
        Json::Null
    });
}


extern "C" {
    fn sol_sha512(vals: *const u8, count: u64, result: *mut u8) -> u64;
    fn sol_curve_multiscalar_mul(curve: u64, scalars: *const u8, points: *const u8,
                                 count: u64, result: *mut u8) -> u64;
}

#[test]
#[should_panic(expected = "reply outside the output shape")]
fn rejects_sha512_with_sha256_width() {
    rec::init();
    shim::case(&Script::new(vec![Reply::new("sol_sha512", 0).data(&[0; 32])]), || unsafe {
        let mut output = [0; 64];
        sol_sha512(core::ptr::null(), 0, output.as_mut_ptr());
        Json::Null
    });
}

#[test]
#[should_panic(expected = "reply outside the output shape")]
fn rejects_msm_error_reply_with_output() {
    rec::init();
    shim::case(&Script::new(vec![Reply::new("sol_curve_multiscalar_mul", 1).data(&[0; 32])]), || unsafe {
        sol_curve_multiscalar_mul(0, core::ptr::null(), core::ptr::null(), 0, core::ptr::null_mut());
        Json::Null
    });
}

#[test]
#[should_panic(expected = "reply outside the output shape")]
fn rejects_msm_success_for_invalid_curve() {
    rec::init();
    shim::case(&Script::new(vec![Reply::new("sol_curve_multiscalar_mul", 0).data(&[0; 32])]), || unsafe {
        sol_curve_multiscalar_mul(2, core::ptr::null(), core::ptr::null(), 1, core::ptr::null_mut());
        Json::Null
    });
}

#[test]
fn msm_error_does_not_touch_null_result() {
    rec::init();
    let result = shim::case(&Script::new(vec![Reply::new("sol_curve_multiscalar_mul", 1)]), || unsafe {
        let status = sol_curve_multiscalar_mul(0, core::ptr::null(), core::ptr::null(), 0,
                                               core::ptr::null_mut());
        assert_eq!(status, 1);
        Json::Bool(true)
    });
    assert_eq!(text(&result), "true");
}

#[test]
fn msm_output_may_alias_an_input_after_reading_it() {
    rec::init();
    let script = Script::new(vec![Reply::new("sol_curve_multiscalar_mul", 0).data(&[0x5a; 32])]);
    let result = shim::case(&script, || unsafe {
        let mut scalar = [0; 32];
        let point = [1; 32];
        let status = sol_curve_multiscalar_mul(0, scalar.as_ptr(), point.as_ptr(), 1, scalar.as_mut_ptr());
        assert_eq!(status, 0);
        assert_eq!(scalar, [0x5a; 32]);
        Json::Bool(true)
    });
    assert_eq!(text(&result), "true");
}

#[test]
fn old_and_new_syscalls_share_one_queue_and_log() {
    rec::init();
    let script = Script::new(vec![
        Reply::new("sol_sha256", 0).data(&[3; 32]),
        Reply::new("sol_sha512", 0).data(&[9; 64]),
        Reply::new("sol_curve_multiscalar_mul", 0).data(&[5; 32]),
        Reply::new("sol_get_clock_sysvar", 1),
    ]);
    let result = shim::case(&script, || unsafe {
        let fields: [&[u8]; 1] = [b"shared"];
        let (mut hash256, mut hash512, mut product) = ([0; 32], [0; 64], [0; 32]);
        assert_eq!(sol_sha256(fields.as_ptr().cast(), 1, hash256.as_mut_ptr()), 0);
        assert_eq!(sol_sha512(fields.as_ptr().cast(), 1, hash512.as_mut_ptr()), 0);
        assert_eq!(sol_curve_multiscalar_mul(0, hash256.as_ptr(), hash256.as_ptr(), 1,
                                              product.as_mut_ptr()), 0);
        rec::returned(Json::arr([hash256[31], hash512[63], product[31]], Json::from),
                      Json::obj([("syscalls", shim::state())]))
    });
    let t = text(&result);
    assert!(t.starts_with(r#"{"exit":"returned","result":[3,9,5]"#), "{t}");
    assert!(t.contains(r#""replies":[{"syscall":"sol_get_clock_sysvar","return":1,"data":""}]"#), "{t}");
    let sha256 = t.find(r#""syscall":"sol_sha256""#).unwrap();
    let sha512 = t.find(r#""syscall":"sol_sha512""#).unwrap();
    let msm = t.find(r#""syscall":"sol_curve_multiscalar_mul""#).unwrap();
    assert!(sha256 < sha512 && sha512 < msm, "{t}");
    assert_eq!(t.matches(r#""syscall":""#).count(), 4, "{t}");
}
