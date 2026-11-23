// bytemuck cases shared by the bytemuck 1.25.2 and 1.25.0 drivers.
//
// Included with `#[path]` into each driver, so `bytemuck` resolves to the
// version pinned by that driver. Generic functions are recorded at the
// concrete instantiations listed in `for_each_pod!`; each record names the
// instantiation in `generics` and its `size_of`/`align_of` in `layout`.
//
// Addresses. The model `SliceRef`/`TypedRef` carry `as_ptr() as usize`.
// Values and slices live in one 16-aligned buffer, and an address is recorded
// as `ADDRESS_BASE + (pointer - buffer start)`. `ADDRESS_BASE` is a multiple
// of 16 and every tested alignment divides 16, so a recorded address has the
// same residue as the real one modulo every tested alignment; the corpus is
// deterministic despite address-space randomisation.

use conformance_recorder as rec;
use rec::{Corpus, Json, Record};

pub const BYTES_OF: &str = "bytemuck::bytes_of";
pub const TRY_FROM_BYTES: &str = "bytemuck::try_from_bytes";
pub const ZEROED: &str = "bytemuck::zeroable::Zeroable::zeroed";

pub const ADDRESS_BASE: usize = 0x1000;

#[repr(C, align(16))]
struct Aligned([u8; 96]);

impl Aligned {
    fn new() -> Self {
        Aligned([0u8; 96])
    }

    fn address(&self, p: *const u8) -> usize {
        let start = self.0.as_ptr() as usize;
        let p = p as usize;
        assert!(start % 16 == 0 && p >= start && p <= start + self.0.len());
        let a = ADDRESS_BASE + (p - start);
        assert_eq!(a % 16, p % 16);
        a
    }
}

fn layout<T>() -> Json {
    Json::obj([
        ("size", core::mem::size_of::<T>().into()),
        ("align", core::mem::align_of::<T>().into()),
    ])
}

fn slice_ref(address: usize, bytes: &[u8]) -> Json {
    Json::obj([("address", address.into()), ("bytes", rec::bytes(bytes))])
}

fn typed_ref(address: usize, value: Json) -> Json {
    Json::obj([("address", address.into()), ("value", value)])
}

fn pod_error(e: &bytemuck::PodCastError) -> Json {
    // Display for `PodCastError` is its Debug name.
    Json::from(format!("{e:?}"))
}

fn record(function: &'static str, id: String, param: &'static str, name: &str, layout: Json,
          args: Json, outcome: Json) -> Record {
    Record {
        id,
        function,
        generics: vec![(param, name.to_string())],
        layout: Some(layout),
        state: Json::Null,
        args,
        outcome,
        observed: None,
    }
}

macro_rules! for_each_pod {
    ($m:ident) => {
        $m!(u8, "u8", |v: &u8| Json::from(*v));
        $m!(u16, "u16", |v: &u16| Json::from(*v));
        $m!(u32, "u32", |v: &u32| Json::from(*v));
        $m!(u64, "u64", |v: &u64| Json::from(*v));
        $m!(i64, "i64", |v: &i64| Json::from(*v));
        $m!(f64, "f64", |v: &f64| rec::f64_bits(*v));
        $m!([u8; 32], "[u8; 32]", |v: &[u8; 32]| rec::bytes(v));
        $m!([u64; 4], "[u64; 4]", |v: &[u64; 4]| Json::arr(v.iter(), |x| Json::from(*x)));
    };
}

/// `bytes_of::<T>(t)` with `t` at each multiple of `align_of::<T>()` up to 16
/// in the aligned buffer. State is `()` (`null`).
pub fn bytes_of_cases(corpus: &mut Corpus, prefix: &str) {
    macro_rules! one {
        ($t:ty, $name:expr, $enc:expr) => {{
            let enc = $enc;
            let align = core::mem::align_of::<$t>();
            for (i, value) in samples::<$t>().iter().enumerate() {
                for offset in (0..=16).step_by(align).take(3) {
                    let mut buf = Aligned::new();
                    let p = unsafe { buf.0.as_mut_ptr().add(offset) as *mut $t };
                    unsafe { p.write(*value) };
                    let t: &$t = unsafe { &*p };
                    let address = buf.address(t as *const $t as *const u8);
                    let r = rec::catch(|| {
                        let s = bytemuck::bytes_of(t);
                        (s.as_ptr(), s.to_vec())
                    });
                    let outcome = match r {
                        Ok((ptr, b)) => rec::returned(slice_ref(buf.address(ptr), &b), Json::Null),
                        Err(reason) => rec::unwound(reason, Json::Null),
                    };
                    corpus.push(record(BYTES_OF, format!("{prefix}/bytes_of/{}/{i}/at{offset}", $name),
                        "T", $name, layout::<$t>(), typed_ref(address, enc(value)), outcome));
                }
            }
        }};
    }
    for_each_pod!(one);
    // `bool` is `NoUninit` but not `Pod`; `()` is the zero-sized case.
    one!(bool, "bool", |v: &bool| Json::from(*v));
    one!((), "()", |_: &()| Json::Null);
}

/// `try_from_bytes::<T>(s)`: every length from 0 to `size + 1` (for sizes
/// above 9: 0, 1, size - 1, size, size + 1); the exact size at start offsets
/// 0 to 8 in the aligned buffer, other lengths at offsets 0 and 1. The bytes
/// are a position-dependent pattern.
pub fn try_from_bytes_cases(corpus: &mut Corpus, prefix: &str) {
    macro_rules! one {
        ($t:ty, $name:expr, $enc:expr) => {{
            let enc = $enc;
            let size = core::mem::size_of::<$t>();
            let lengths: Vec<usize> = if size <= 9 {
                (0..=size + 1).collect()
            } else {
                vec![0, 1, size - 1, size, size + 1]
            };
            for len in lengths {
                // The exact size at every start offset 0 to 8 (aligned and
                // misaligned); other lengths at offsets 0 and 1 (the size check
                // comes first, whatever the alignment).
                let offsets: Vec<usize> = if len == size { (0..=8).collect() } else { vec![0, 1] };
                for offset in offsets {
                    let mut buf = Aligned::new();
                    let bytes = pattern(len, 0x11 + offset as u8);
                    buf.0[offset..offset + len].copy_from_slice(&bytes);
                    let s = &buf.0[offset..offset + len];
                    let address = buf.address(s.as_ptr());
                    let r = rec::catch(|| match bytemuck::try_from_bytes::<$t>(s) {
                        Ok(v) => rec::ok(typed_ref(buf.address(v as *const $t as *const u8), enc(v))),
                        Err(e) => rec::err(pod_error(&e)),
                    });
                    let outcome = match r {
                        Ok(result) => rec::returned(result, Json::Null),
                        Err(reason) => rec::unwound(reason, Json::Null),
                    };
                    corpus.push(record(TRY_FROM_BYTES,
                        format!("{prefix}/try_from_bytes/{}/len{len}/at{offset}", $name),
                        "T", $name, layout::<$t>(), slice_ref(address, s), outcome));
                }
            }
        }};
    }
    for_each_pod!(one);
    one!([u64; 0], "[u64; 0]", |_: &[u64; 0]| Json::Arr(vec![]));
}

/// `<T as Zeroable>::zeroed()`. Arguments and state are `()` (`null`).
pub fn zeroed_cases(corpus: &mut Corpus, prefix: &str) {
    macro_rules! one {
        ($t:ty, $name:expr, $enc:expr) => {{
            let enc = $enc;
            let r = rec::catch(|| enc(&<$t as bytemuck::Zeroable>::zeroed()));
            let outcome = match r {
                Ok(v) => rec::returned(v, Json::Null),
                Err(reason) => rec::unwound(reason, Json::Null),
            };
            corpus.push(record(ZEROED, format!("{prefix}/zeroed/{}", $name), "Self", $name,
                layout::<$t>(), Json::Null, outcome));
        }};
    }
    for_each_pod!(one);
    one!(bool, "bool", |v: &bool| Json::from(*v));
}

pub fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(37).wrapping_add(seed)).collect()
}

/// Sample values: zero, one, all-ones, the minimum and a position-dependent
/// pattern; the IEEE-754 patterns for `f64`.
trait Samples: Sized {
    fn samples() -> Vec<Self>;
}

fn samples<T: Samples>() -> Vec<T> {
    T::samples()
}

macro_rules! int_samples {
    ($($t:ty),*) => {$(
        impl Samples for $t {
            fn samples() -> Vec<$t> {
                let mut v = vec![0, 1, <$t>::MAX, (0x0102_0304_0506_0708u64 as $t)];
                if <$t>::MIN != 0 { v.push(<$t>::MIN); }
                v
            }
        }
    )*};
}
int_samples!(u8, u16, u32, u64, i64);

impl Samples for f64 {
    fn samples() -> Vec<f64> {
        rec::F64_PATTERNS.iter().map(|(_, b)| f64::from_bits(*b)).collect()
    }
}

impl Samples for bool {
    fn samples() -> Vec<bool> {
        vec![false, true]
    }
}

impl Samples for () {
    fn samples() -> Vec<()> {
        vec![()]
    }
}

impl Samples for [u8; 32] {
    fn samples() -> Vec<[u8; 32]> {
        let mut p = [0u8; 32];
        p.copy_from_slice(&pattern(32, 0x5a));
        vec![[0; 32], [0xff; 32], p]
    }
}

impl Samples for [u64; 4] {
    fn samples() -> Vec<[u64; 4]> {
        vec![[0; 4], [u64::MAX; 4], [1, 0x0102_0304_0506_0708, u64::MAX - 1, 1 << 63]]
    }
}
