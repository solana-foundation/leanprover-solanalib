//! Records the pinned library versions: borsh 0.10.4 decoders (with
//! the heap requests of `Vec<T>` decoding and the `hint::cautious` values they
//! show) and bytemuck 1.25.2 `bytes_of` and `Zeroable::zeroed`.

#[allow(dead_code)]
#[path = "../../common/borsh_de.rs"]
mod borsh_de;
#[allow(dead_code)]
#[path = "../../common/bytemuck_cases.rs"]
mod bytemuck_cases;
mod heap;
mod vec_heap;

use borsh_de::*;
use conformance_recorder::{self as rec, Corpus, Json};

/// Logs the heap requests of the tracked `Vec<T>` decodes (`vec_heap.rs`).
#[global_allocator]
static GLOBAL: heap::Tracking = heap::Tracking;

/// The wrappers `deserialize` and `try_from_slice` only: the `Vec<T>` implementation of
/// `deserialize_reader` is recorded with its heap requests by `vec_heap`.
const WRAPPERS: Entries = Entries { deserialize: true, deserialize_reader: false, try_from_slice: true };

fn borsh_corpus() -> Corpus {
    let mut c = Corpus::new("borsh_0_10_4", &[("borsh", "0.10.4")]);
    let p = "borsh_0_10_4";
    decode_cases(&mut c, p, &u8_ty(), ALL, &u8_inputs());
    decode_cases(&mut c, p, &i8_ty(), ALL, &i8_inputs());
    decode_cases(&mut c, p, &bool_ty(), ALL, &bool_inputs());
    decode_cases(&mut c, p, &u32_ty(), ALL, &u32_inputs());
    decode_cases(&mut c, p, &u64_ty(), ALL, &u64_inputs());

    let opt_u8 = option_ty(&u8_ty(), |v| rec::option(v, |x| Json::from(*x)));
    decode_cases(&mut c, p, &opt_u8, ALL, &option_inputs(&[0x7f]));
    let opt_u32 = option_ty(&u32_ty(), |v| rec::option(v, |x| Json::from(*x)));
    decode_cases(&mut c, p, &opt_u32, ALL, &option_inputs(&0x0102_0304u32.to_le_bytes()));
    let opt_u64 = option_ty(&u64_ty(), |v| rec::option(v, |x| Json::from(*x)));
    decode_cases(&mut c, p, &opt_u64, ALL, &option_inputs(&u64::MAX.to_le_bytes()));
    let opt_bool = option_ty(&bool_ty(), |v| rec::option(v, |x| Json::from(*x)));
    let mut ob = option_inputs(&[1]);
    ob.push(("some_invalid_bool".into(), vec![1, 2]));
    decode_cases(&mut c, p, &opt_bool, ALL, &ob);

    // Vec<T>: `deserialize_reader` with its heap requests, on the wrapper
    // inputs and on inputs at the allocation bounds; the wrappers on their own
    // inputs. Elements of sizes 1 (`u8`, `bool`), 4 (`u32`) and 16 (`Option<u64>`).
    let vec_u8 = vec_ty(&u8_ty(), |v| rec::bytes(v));
    let vu8 = vec_inputs(&[vec![0x10], vec![0x20], vec![0x30]]);
    vec_heap::reader_cases(&mut c, p, &vec_u8, false, &[vu8.clone(), vec_heap::byte_resize_inputs()].concat());
    decode_cases(&mut c, p, &vec_u8, WRAPPERS, &vu8);
    let vec_u32 = vec_ty(&u32_ty(), |v| Json::arr(v.iter(), |x| Json::from(*x)));
    let vu32 = vec_inputs(&[1u32.to_le_bytes().to_vec(), u32::MAX.to_le_bytes().to_vec()]);
    let hint_u32 = vec_heap::hint_inputs(1024, &1u32.to_le_bytes(), &[0; 4], 1025);
    let cautious_u32 = vec_heap::reader_cases(&mut c, p, &vec_u32, true, &[vu32.clone(), hint_u32].concat());
    decode_cases(&mut c, p, &vec_u32, WRAPPERS, &vu32);
    let vec_bool = vec_ty(&bool_ty(), |v| Json::arr(v.iter(), |x| Json::from(*x)));
    let mut vb = vec_inputs(&[vec![1], vec![0]]);
    vb.push(("len3/invalid_middle".into(), vec![3, 0, 0, 0, 1, 2, 0]));
    let hint_bool = vec_heap::hint_inputs(4096, &[1], &[0], 5000);
    let cautious_bool = vec_heap::reader_cases(&mut c, p, &vec_bool, true, &[vb.clone(), hint_bool].concat());
    decode_cases(&mut c, p, &vec_bool, WRAPPERS, &vb);
    let opt_u64_ty = option_ty(&u64_ty(), |v| rec::option(v, |x| Json::from(*x)));
    let vec_opt_u64 = vec_ty(&opt_u64_ty, |v| Json::arr(v.iter(), |x| rec::option(x, |y| Json::from(*y))));
    let mut vo: Vec<(String, Vec<u8>)> = vec![
        ("len0".into(), vec_heap::with_len(0, &[])),
        ("len1".into(), vec_heap::with_len(1, &[&[1u8][..], &5u64.to_le_bytes()].concat())),
        ("len2".into(), vec_heap::with_len(2, &[&[0u8, 1][..], &u64::MAX.to_le_bytes()].concat())),
        ("len2/truncated_some".into(), vec_heap::with_len(2, &[0, 1, 1, 2, 3])),
        ("len1/invalid_tag".into(), vec_heap::with_len(1, &[2])),
        ("len_u32max/short".into(), vec_heap::with_len(u32::MAX, &[0])),
    ];
    vo.extend(vec_heap::hint_inputs(256, &[0], &[0], 257));
    let cautious_opt_u64 = vec_heap::reader_cases(&mut c, p, &vec_opt_u64, true, &vo);
    vec_heap::cautious_cases::<u32>(&mut c, p, "u32", &cautious_u32);
    vec_heap::cautious_cases::<bool>(&mut c, p, "bool", &cautious_bool);
    vec_heap::cautious_cases::<Option<u64>>(&mut c, p, &opt_u64_ty.name, &cautious_opt_u64);

    let default_cases: Vec<(u32, Vec<u8>)> = vec![(0, vec![]), (3, vec![1, 2, 3]), (u32::MAX, vec![9])];
    vec_from_reader_default_cases::<u32>(&mut c, p, "u32", &default_cases);
    vec_from_reader_default_cases::<bool>(&mut c, p, "bool", &default_cases);
    c
}

fn bytemuck_corpus() -> Corpus {
    let mut c = Corpus::new("bytemuck_1_25_2", &[("bytemuck", "1.25.2")]);
    bytemuck_cases::bytes_of_cases(&mut c, "bytemuck_1_25_2");
    bytemuck_cases::zeroed_cases(&mut c, "bytemuck_1_25_2");
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    for corpus in [borsh_corpus(), bytemuck_corpus()] {
        corpus.write(&out).expect("write corpus");
    }
}
