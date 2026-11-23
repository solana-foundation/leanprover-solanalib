//! solana-system-interface 3.2.0 `create_account` and `transfer`. Shared by two drivers: built
//! with the `bincode` feature, `create_instruction` calls `new_with_bincode`; with
//! both `bincode` and `wincode`, it calls `new_with_wincode`.

use crate::common::{address, instruction, key, pure_call};
use conformance_recorder::{Corpus, Json, Record};
use solana_address::Address;
use solana_system_interface::instruction::{create_account, transfer};

const CREATE_ACCOUNT: &str = "solana_system_interface::instruction::create_account";
const TRANSFER: &str = "solana_system_interface::instruction::transfer";

pub fn record(c: &mut Corpus) {
    let a = key(0x10);
    let b = key(0x80);
    let zero = Address::new_from_array([0; 32]);
    let pairs = [("distinct", a, b), ("alias", a, a), ("zero_from", zero, b)];
    let amounts = [("0", 0u64), ("1", 1), ("pattern", 0x0102_0304_0506_0708), ("max", u64::MAX)];
    // Every amount boundary for distinct accounts; the extremes for the alias and the zero key.
    for (pl, from, to) in pairs {
        for (ll, lamports) in amounts {
            if pl != "distinct" && (ll == "1" || ll == "pattern") {
                continue;
            }
            c.push(Record {
                id: format!("transfer/{pl}/{ll}"),
                function: TRANSFER,
                generics: vec![],
                layout: None,
                state: Json::Null,
                args: Json::obj([
                    ("from", address(&from)),
                    ("to", address(&to)),
                    ("lamports", lamports.into()),
                ]),
                outcome: pure_call(|| transfer(&from, &to, lamports), instruction),
                observed: None,
            });
        }
    }
    let spaces = [("0", 0u64), ("10240", 10_240), ("max", u64::MAX)];
    // Every lamports x space boundary for distinct accounts and the zero owner; one case each
    // for the alias, the zero key and a nonzero owner.
    for (pl, from, to) in pairs {
        for (ll, lamports) in [amounts[0], amounts[2], amounts[3]] {
            for (sl, space) in spaces {
                for (ol, owner) in [("owner_zero", zero), ("owner_k40", key(0x40))] {
                    let base = pl == "distinct" && ol == "owner_zero";
                    let single = ll == "pattern" && sl == "10240" && (pl == "distinct" || ol == "owner_zero");
                    if !(base || single) {
                        continue;
                    }
                    c.push(Record {
                        id: format!("create_account/{pl}/{ll}/{sl}/{ol}"),
                        function: CREATE_ACCOUNT,
                        generics: vec![],
                        layout: None,
                        state: Json::Null,
                        args: Json::obj([
                            ("from", address(&from)),
                            ("to", address(&to)),
                            ("lamports", lamports.into()),
                            ("space", space.into()),
                            ("owner", address(&owner)),
                        ]),
                        outcome: pure_call(|| create_account(&from, &to, lamports, space, &owner), instruction),
                        observed: None,
                    });
                }
            }
        }
    }
}
