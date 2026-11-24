//! switchboard-on-demand 0.12.1 (the pinned git revision) `PullFeedAccountData::parse`.
//!
//! The argument is a live shared `Ref<&mut [u8]>` of a `RefCell` over a slice of a 16-aligned
//! buffer. The state is the slice bytes, its address (`0x1000 + offset` inside the buffer, so
//! residues modulo 16 are those of the real address) and the cell borrow state; after the call
//! the borrow state is read back while any returned `Ref` is alive and again after dropping it,
//! with the cell bytes. A returned `Ref` is recorded as its offset from the slice start and its
//! length.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::RefCell;
use std::mem::{align_of, size_of};
use switchboard_on_demand::on_demand::accounts::pull_feed::PullFeedAccountData;

const FUNCTION: &str = "switchboard_on_demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse";
const DISCRIMINATOR: [u8; 8] = [196, 27, 108, 196, 10, 215, 219, 40];
const BASE: usize = 0x1000;

fn borrow_state<T>(cell: &RefCell<T>) -> &'static str {
    if cell.try_borrow_mut().is_ok() {
        "free"
    } else if cell.try_borrow().is_ok() {
        "shared"
    } else {
        "exclusive"
    }
}

/// A payload of zeros with distinct first and last bytes (every bit pattern is a valid feed; the
/// zero run keeps the record compact).
fn payload(n: usize) -> Vec<u8> {
    let mut p = vec![0u8; n];
    p[0] = 0x5a;
    p[n - 1] = 0xa5;
    p
}

fn case(c: &mut Corpus, id: String, data: &[u8], offset: usize) {
    // 16-aligned backing storage.
    let mut storage = vec![0u128; (data.len() + offset) / 16 + 2];
    let base = storage.as_mut_ptr() as *mut u8;
    assert_eq!(base as usize % 16, 0);
    let bytes: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(base.add(offset), data.len()) };
    bytes.copy_from_slice(data);
    let start = bytes.as_ptr() as usize;
    let cell = RefCell::new(bytes);
    let state = Json::obj([
        ("data", rec::bytes(data)),
        ("address", (BASE + offset).into()),
        ("borrow", "shared".into()),
    ]);
    let guard = cell.borrow();
    // After the call: the borrow state while any returned `Ref` is alive, the state once it is
    // dropped (so a free cell shows that the `Ref` held the only share), and the cell bytes.
    let probe = |cell: &RefCell<&mut [u8]>, held: &'static str| {
        let data = cell.try_borrow().map(|b| b.to_vec()).expect("readable after the call");
        Json::obj([("borrow", held.into()), ("after_drop", borrow_state(cell).into()), ("data", rec::bytes(&data))])
    };
    let outcome = match rec::catch(|| PullFeedAccountData::parse(guard)) {
        Ok(Ok(feed)) => {
            let at = &*feed as *const PullFeedAccountData as usize - start;
            let len = size_of::<PullFeedAccountData>();
            let held = borrow_state(&cell);
            let data = cell.try_borrow().map(|b| b.to_vec()).expect("readable while shared");
            drop(feed);
            let after = Json::obj([("borrow", held.into()), ("after_drop", borrow_state(&cell).into()),
                ("data", rec::bytes(&data))]);
            rec::returned(rec::ok(Json::obj([("offset", at.into()), ("len", len.into())])), after)
        }
        Ok(Err(e)) => rec::returned(rec::err(format!("{e:?}").into()), probe(&cell, borrow_state(&cell))),
        Err(reason) => rec::unwound(reason, probe(&cell, borrow_state(&cell))),
    };
    c.push(Record {
        id,
        function: FUNCTION,
        generics: vec![],
        layout: Some(Json::obj([
            ("size", size_of::<PullFeedAccountData>().into()),
            ("align", align_of::<PullFeedAccountData>().into()),
        ])),
        state,
        args: Json::Null,
        outcome,
        observed: None,
    });
    drop(storage);
}

pub fn record(c: &mut Corpus) {
    let size = size_of::<PullFeedAccountData>();
    let full = [DISCRIMINATOR.to_vec(), payload(size)].concat();
    let mut wrong = full.clone();
    wrong[7] ^= 1;
    // Lengths around the discriminator and payload boundaries, at an aligned payload (offset 8).
    case(c, "empty".into(), &[], 8);
    case(c, "disc_short7".into(), &DISCRIMINATOR[..7], 8);
    case(c, "disc_only".into(), &DISCRIMINATOR, 8);
    case(c, "disc_wrong_short".into(), &wrong[..8], 8);
    case(c, "disc_wrong_full".into(), &wrong, 8);
    case(c, "disc+payload_short1".into(), &full[..full.len() - 1], 8);
    case(c, "disc+one_byte".into(), &full[..9], 8);
    case(c, "exact".into(), &full, 8);
    case(c, "trailing2".into(), &rec::with_trailing(&full), 8);
    // Payload address residues modulo 16 (the slice starts at `offset`, the payload 8 later).
    for offset in [0usize, 1, 4, 7, 9, 15, 24] {
        case(c, format!("exact/offset{offset}"), &full, offset);
    }
    // A wrong discriminator at a misaligned address: the discriminator check comes first.
    case(c, "disc_wrong_full/offset1".into(), &wrong, 1);
    // A short payload at a misaligned address: the length check comes first.
    case(c, "disc+payload_short1/offset1".into(), &full[..full.len() - 1], 1);
}
