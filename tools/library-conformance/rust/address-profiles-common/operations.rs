//! Exact SDK calls with deterministic scripted runtime replies.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Reply, Script};
use crate::{Key, KEY_PATH, ZEROED};

pub fn name(method: &str, trait_path: Option<&str>) -> &'static str {
    Box::leak(match trait_path {
        Some(t) => format!("<{KEY_PATH} as {t}>::{method}"),
        None if KEY_PATH == "solana_address::Address" && method.ends_with("program_address") =>
            format!("solana_address::syscalls::<impl solana_address::Address>::{method}"),
        None => format!("{KEY_PATH}::{method}"),
    }.into_boxed_str())
}

pub fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(53).wrapping_add(seed)).collect()
}

pub fn key(seed: u8) -> Key {
    Key::new_from_array(pattern(32, seed).try_into().unwrap())
}

pub fn state(script: &Script) -> Json {
    Json::obj([("syscalls", script.state_before())])
}

pub fn after() -> Json {
    Json::obj([("syscalls", shim::state())])
}

pub fn push(c: &mut Corpus, id: String, function: &'static str, before: Json, args: Json, outcome: Json) {
    c.push(Record { id, function, generics: vec![], layout: None, state: before, args, outcome, observed: None });
}

pub fn record_values(c: &mut Corpus, methods: &[&str]) {
    for &method in methods {
        for (i, a) in [[0u8; 32], [255u8; 32], pattern(32, 17).try_into().unwrap()].iter().enumerate() {
            let k = Key::new_from_array(*a);
            let (function, args, result) = match method {
                "new_from_array" => (name(method, None), Json::obj([("array", rec::bytes(a))]), rec::bytes(&Key::new_from_array(*a).to_bytes())),
                "from" => (name(method, Some("core::convert::From<[u8; 32]>")), Json::obj([("array", rec::bytes(a))]), rec::bytes(&Key::from(*a).to_bytes())),
                "to_bytes" => (name(method, None), Json::obj([("self", rec::bytes(a))]), rec::bytes(&k.to_bytes())),
                "as_ref" => (name(method, Some("core::convert::AsRef<[u8]>")), Json::obj([("self", rec::bytes(a))]), rec::bytes(k.as_ref())),
                "default" => (name(method, Some("core::default::Default")), Json::Null, rec::bytes(&Key::default().to_bytes())),
                "clone" => (name(method, Some("core::clone::Clone")), Json::obj([("self", rec::bytes(a))]), rec::bytes(&k.clone().to_bytes())),
                "eq" | "cmp" => {
                    let mut other = *a;
                    other[if i == 0 { 0 } else { 31 }] = other[if i == 0 { 0 } else { 31 }].wrapping_add(1);
                    for (j, b) in [*a, other].iter().enumerate() {
                        let other_key = Key::new_from_array(*b);
                        let (function, result) = if method == "eq" {
                            (name(method, Some("core::cmp::PartialEq")), Json::from(k == other_key))
                        } else {
                            (name(method, Some("core::cmp::Ord")), Json::from(format!("{:?}", k.cmp(&other_key))))
                        };
                        push(c, format!("{method}/{i}/{j}"), function, Json::Null,
                             Json::obj([("self", rec::bytes(a)), ("other", rec::bytes(b))]), rec::returned(result, Json::Null));
                    }
                    continue;
                }
                _ => panic!("unrecognized method"),
            };
            push(c, format!("{method}/{i}"), function, Json::Null, args, rec::returned(result, Json::Null));
        }
    }
}

fn inputs() -> Vec<(&'static str, Vec<Vec<u8>>)> {
    vec![("empty", vec![]), ("ordered", vec![vec![], b"vault".to_vec(), pattern(32, 3)]),
         ("count17", vec![vec![]; 17]), ("length33", vec![pattern(33, 9)])]
}

fn scripts(syscall: &str) -> Vec<(&'static str, Script)> {
    let bytes = pattern(32, 201);
    let one = |reply| Script::new(vec![reply]);
    let mut all = vec![
        ("ok", one(Reply::new(syscall, 0).data(&bytes).bump(254))),
        ("bump0", one(Reply::new(syscall, 0).data(&bytes).bump(0))),
        ("bump_untouched", one(Reply::new(syscall, 0).data(&bytes))),
        ("status1", one(Reply::new(syscall, 1).data(&bytes[..5]))),
        ("status2", one(Reply::new(syscall, 2))),
        ("status3", one(Reply::new(syscall, 3))),
        ("status_max", one(Reply::new(syscall, u64::MAX))),
        ("terminal", one(Reply::new(syscall, 0).data(&bytes).terminate("chosen terminal reply"))),
    ];
    if ZEROED {
        all.push(("untouched", one(Reply::new(syscall, 0))));
        all.push(("partial", one(Reply::new(syscall, 0).data(&bytes[..5]))));
    }
    all
}

pub fn record_create(c: &mut Corpus) {
    let pid = key(7);
    for (iname, seeds) in inputs() {
        for (sname, script) in scripts("sol_create_program_address") {
            let slices: Vec<&[u8]> = seeds.iter().map(Vec::as_slice).collect();
            let outcome = shim::case(&script, || {
                let result = Key::create_program_address(&slices, &pid);
                rec::returned(match result {
                    Ok(key) => rec::ok(rec::bytes(&key.to_bytes())),
                    Err(error) => rec::err(format!("{error:?}").into()),
                }, after())
            });
            push(c, format!("create/{iname}/{sname}"), name("create_program_address", None), state(&script),
                Json::obj([("seeds", Json::arr(seeds.iter(), |s| rec::bytes(s))), ("program_id", rec::bytes(&pid.to_bytes()))]), outcome);
        }
    }
}

pub fn record_find(c: &mut Corpus) {
    let pid = key(7);
    for (iname, seeds) in inputs() {
        for (sname, script) in scripts("sol_try_find_program_address") {
            let slices: Vec<&[u8]> = seeds.iter().map(Vec::as_slice).collect();
            let outcome = shim::case(&script, || {
                let (key, bump) = Key::find_program_address(&slices, &pid);
                rec::returned(Json::obj([("address", rec::bytes(&key.to_bytes())), ("bump", bump.into())]), after())
            });
            push(c, format!("find/{iname}/{sname}"), name("find_program_address", None), state(&script),
                Json::obj([("seeds", Json::arr(seeds.iter(), |s| rec::bytes(s))), ("program_id", rec::bytes(&pid.to_bytes()))]), outcome);
        }
    }
}

#[cfg(feature = "seed")]
pub fn record_seed(c: &mut Corpus) {
    let mut illegal = [0u8; 32];
    illegal[11..].copy_from_slice(b"ProgramDerivedAddress");
    for (iname, seed, owner) in [
        ("empty", String::new(), key(2)),
        ("length32", "s".repeat(32), key(2)),
        ("length33", "s".repeat(33), key(2)),
        ("utf8_33_bytes", "☉".repeat(11), key(2)),
        ("illegal_owner", "s".to_owned(), Key::new_from_array(illegal)),
        ("both_guards", "s".repeat(33), Key::new_from_array(illegal)),
    ] {
        for terminal in [false, true] {
            let reply = Reply::new("sol_sha256", 0).data(&pattern(32, 99));
            let script = Script::new(vec![if terminal { reply.terminate("chosen hash exit") } else { reply }]);
            let base = key(1);
            let outcome = shim::case(&script, || {
                let result = Key::create_with_seed(&base, &seed, &owner);
                rec::returned(match result {
                    Ok(key) => rec::ok(rec::bytes(&key.to_bytes())),
                    Err(error) => rec::err(format!("{error:?}").into()),
                }, after())
            });
            push(c, format!("seed/{iname}/{terminal}"), name("create_with_seed", None), state(&script),
                Json::obj([("base", rec::bytes(&base.to_bytes())), ("seed", seed.clone().into()), ("owner", rec::bytes(&owner.to_bytes()))]), outcome);
        }
    }
}

pub fn record_derived(c: &mut Corpus, function: &'static str, getter: impl Fn(&Key, &Key, &Key) -> Key) {
    for (sname, script) in scripts("sol_try_find_program_address") {
        let wallet = key(11); let mint = key(47); let token = key(99);
        let outcome = shim::case(&script, || rec::returned(rec::bytes(&getter(&wallet, &mint, &token).to_bytes()), after()));
        push(c, format!("{function}/{sname}"), function, state(&script),
             Json::obj([("wallet", rec::bytes(&wallet.to_bytes())), ("mint", rec::bytes(&mint.to_bytes())), ("token_program", rec::bytes(&token.to_bytes()))]), outcome);
    }
}
