use conformance_recorder::{self as rec, Corpus, Json, Record};
use pinocchio::instruction::{AccountMeta, Seed};
use crate::syscall_cases::*;
const META: [&str; 4] = ["pinocchio::instruction::AccountMeta::<'a>::readonly", "pinocchio::instruction::AccountMeta::<'a>::readonly_signer",
    "pinocchio::instruction::AccountMeta::<'a>::writable", "pinocchio::instruction::AccountMeta::<'a>::writable_signer"];
const SEED: &str = "<pinocchio::instruction::Seed<'a> as core::convert::From<&'a [u8; SIZE]>>::from";
const EQ: &str = "pinocchio::pubkey::pubkey_eq";
fn push(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, args: Json, result: Json) {
    c.push(Record { id, function, generics, layout: None, state: Json::Null, args,
        outcome: rec::returned(result, Json::Null), observed: None });
}
fn seed<const N: usize>(c: &mut Corpus) {
    let a: [u8; N] = core::array::from_fn(|i| (i as u8).wrapping_mul(29).wrapping_add(3));
    let s = Seed::from(&a);
    let ptr = s.as_ptr() as usize; let same = ptr == a.as_ptr() as usize;
    push(c, format!("seed/{N}"), SEED, vec![("SIZE", N.to_string())],
        Json::obj([("reference", 19usize.into()), ("bytes", rec::bytes(&a)), ("size", N.into())]),
        Json::obj([("reference", if same { 19usize.into() } else { Json::Null }), ("length", s.len().into()), ("bytes", rec::bytes(&s))]));
}
pub fn corpus() -> Corpus {
    let mut c = Corpus::new("pinocchio_0_9_2_values", &[("pinocchio", "0.9.2")]);
    for i in 0..4 {
        for fill in [0, 255] {
            let key = [fill; 32]; let value = match i {
                0 => AccountMeta::readonly(&key), 1 => AccountMeta::readonly_signer(&key),
                2 => AccountMeta::writable(&key), _ => AccountMeta::writable_signer(&key)
            };
            let same = core::ptr::eq(value.pubkey, &key);
            push(&mut c, format!("meta/{i}/{fill}"), META[i], vec![],
                Json::obj([("reference", 13usize.into()), ("key", rec::bytes(&key))]),
                Json::obj([("reference", if same { 13usize.into() } else { Json::Null }),
                    ("key", rec::bytes(value.pubkey)), ("is_signer", value.is_signer.into()), ("is_writable", value.is_writable.into())]));
        }
    }
    seed::<0>(&mut c); seed::<1>(&mut c); seed::<2>(&mut c); seed::<9>(&mut c); seed::<32>(&mut c); seed::<64>(&mut c);
    for position in [None, Some(0), Some(7), Some(8), Some(15), Some(16), Some(23), Some(24), Some(31)] {
        let left = [5; 32]; let mut right = left; if let Some(i) = position { right[i] ^= 1; }
        push(&mut c, format!("pubkey_eq/{position:?}"), EQ, vec![], Json::obj([("left", rec::bytes(&left)), ("right", rec::bytes(&right))]), pinocchio::pubkey::pubkey_eq(&left, &right).into());
    }
    use pinocchio::sysvars::{clock::Clock, Sysvar};
    let values: Vec<_> = clocks().into_iter().map(|(n,v)| (n,clock_bytes(v))).collect();
    for (name,script) in getter_scripts("sol_get_clock_sysvar", &values) {
        syscall_case(&mut c, format!("clock_get/{name}"), "<pinocchio::sysvars::clock::Clock as pinocchio::sysvars::Sysvar>::get",
            Json::Null, script, Clock::get, |r| program_error(r, |v: &Clock| clock_json(v.slot, v.epoch_start_timestamp, v.epoch, v.leader_schedule_epoch, v.unix_timestamp)));
    }
    c
}
