//! `CpiContext::new_with_signer` and `solana_program::log::sol_log_data`.

use anchor_lang::prelude::*;
use anchor_spl::token::Transfer;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim as shim;

use crate::accounts::{parse_raw, PROGRAM};
use crate::world::{account, input, pk, World};

fn push(c: &mut Corpus, id: String, function: &'static str, generics: Vec<(&'static str, String)>, state: Json, args: Json, outcome: Json) {
    c.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
}

const NEW_WITH_SIGNER: &str = "anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer";
pub const TRANSFER: &str = "anchor_spl::token::Transfer<'_>";

pub fn seeds_json(seeds: &[&[&[u8]]]) -> Json {
    Json::arr(seeds.iter(), |s| Json::arr(s.iter(), |b| rec::bytes(b)))
}

fn record_new_with_signer(c: &mut Corpus) {
    let seed_sets: Vec<(&str, &'static [&'static [&'static [u8]]])> = vec![
        ("no_signers", &[]),
        ("one_signer", &[&[b"vault", &[7]]]),
        ("two_signers", &[&[b"a", b"", &[255]], &[&[1, 2, 3]]]),
        ("empty_signer", &[&[]]),
    ];
    let worlds: Vec<(&str, Vec<conformance_accounts::Entry>, [usize; 3])> = vec![
        ("distinct", vec![account(pk(1), PROGRAM, 10, vec![1], false, true), account(pk(2), PROGRAM, 20, vec![], false, true), account(pk(3), pk(0), 30, vec![], true, false)], [0, 1, 2]),
        ("aliased", vec![account(pk(4), PROGRAM, 10, vec![1, 2], true, true), conformance_accounts::Entry::Duplicate(0)], [0, 1, 0]),
    ];
    for (wl, entries, [f, t, a]) in worlds {
        for (sl, seeds) in &seed_sets {
            let seeds: &'static [&'static [&'static [u8]]] = seeds;
            let inp = input(entries.clone());
            let inp_ = inp.clone();
            let program_id = Pubkey::new_from_array(pk(0x0c));
            let out = shim::case(&shim::Script::new(vec![]), move || {
                let w: &'static World = Box::leak(Box::new(World::new(&inp_)));
                let accounts = Transfer { from: w.info(f).clone(), to: w.info(t).clone(), authority: w.info(a).clone() };
                let r = rec::catch(|| CpiContext::new_with_signer(program_id, accounts, seeds));
                match r {
                    Ok(ctx) => {
                        let result = Json::obj([
                            ("accounts", Json::obj([("from", w.info_json(&ctx.accounts.from)), ("to", w.info_json(&ctx.accounts.to)),
                                ("authority", w.info_json(&ctx.accounts.authority))])),
                            ("remaining_accounts", Json::arr(ctx.remaining_accounts.iter(), |i| w.info_json(i))),
                            ("program_id", rec::bytes(ctx.program_id.as_ref())),
                            ("signer_seeds", seeds_json(ctx.signer_seeds)),
                        ]);
                        std::mem::forget(ctx);
                        rec::returned(result, w.state(vec![]))
                    }
                    Err(reason) => rec::unwound(reason, w.state(vec![])),
                }
            });
            let state = Json::obj([("input", inp.to_json()), ("borrows", Json::Arr(vec![])), ("syscalls", shim::Script::new(vec![]).state_before())]);
            let args = Json::obj([
                ("program_id", rec::bytes(program_id.as_ref())),
                ("accounts", Json::obj([("from", f.into()), ("to", t.into()), ("authority", a.into())])),
                ("signer_seeds", seeds_json(seeds)),
            ]);
            push(c, format!("new_with_signer/{wl}/{sl}"), NEW_WITH_SIGNER, vec![("T", TRANSFER.to_string())], state, args, parse_raw(&out));
        }
    }
}

const SOL_LOG_DATA: &str = "anchor_lang::solana_program::log::sol_log_data";

fn record_log_data(c: &mut Corpus) {
    let cases: Vec<(&str, Vec<Vec<u8>>)> = vec![
        ("none", vec![]),
        ("one_empty", vec![vec![]]),
        ("one", vec![vec![1, 2, 3]]),
        ("several", vec![vec![0xff], vec![], vec![0; 40], (0..=255u8).collect()]),
    ];
    for (label, fields) in cases {
        let script = shim::Script::new(vec![]);
        let fields_ = fields.clone();
        let out = shim::case(&script, move || {
            let slices: Vec<&[u8]> = fields_.iter().map(|f| f.as_slice()).collect();
            let r = rec::catch(|| anchor_lang::solana_program::log::sol_log_data(&slices));
            let state = Json::obj([("syscalls", shim::state())]);
            match r {
                Ok(()) => rec::returned(Json::Null, state),
                Err(reason) => rec::unwound(reason, state),
            }
        });
        let state = Json::obj([("syscalls", script.state_before())]);
        let args = Json::obj([("fields", Json::arr(fields.iter(), |f| rec::bytes(f)))]);
        push(c, format!("sol_log_data/{label}"), SOL_LOG_DATA, vec![], state, args, parse_raw(&out));
    }
}

pub fn record_all(c: &mut Corpus) {
    record_new_with_signer(c);
    record_log_data(c);
}
