//! Little-endian wrappers, including single-byte significance and word limits.
use conformance_recorder::{self as rec, Corpus, Json, Record};
fn values16() -> Vec<[u8;2]> {vec![[0,0],[255,255],[1,0],[0,1],[0,128],[255,127],[0x12,0x34],[0xff,0]]}
fn push(c: &mut Corpus, id: String, function: &'static str, bytes: &[u8], value: u64) {
    c.push(Record{id,function,generics:vec![],layout:None,state:Json::Null,args:Json::obj([("value",rec::bytes(bytes))]),outcome:rec::returned(value.into(),Json::Null),observed:None});
}
pub fn record_zero(version: &'static str, corpus: &'static str) {
    let mut c=Corpus::new(corpus,&[("solana-zero-copy",version)]);
    for (i,bytes) in values16().into_iter().enumerate() {
        let value=u16::from(solana_zero_copy::unaligned::U16(bytes));
        push(&mut c,format!("into_u16/{i}"),"solana_zero_copy::unaligned::<impl core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from",&bytes,value as u64);
    }
    c.write(&rec::out_dir()).expect("write U16 corpus");
}
pub fn record_pod() {
    let mut c=Corpus::new("sdk_values_spl_pod_0_5_1",&[("spl-pod","0.5.1")]);
    for (i,bytes) in values16().into_iter().enumerate() {
        let value=u16::from(spl_pod::primitives::PodU16(bytes));
        push(&mut c,format!("into_u16/{i}"),"spl_pod::primitives::<impl core::convert::From<spl_pod::primitives::PodU16> for u16>::from",&bytes,value as u64);
    }
    let mut cases=vec![[0;8],[255;8],[1,2,3,4,5,6,7,8]];
    for i in 0..8 {let mut bytes=[0;8];bytes[i]=128;cases.push(bytes);}
    for (i,bytes) in cases.into_iter().enumerate() {
        let value=u64::from(spl_pod::primitives::PodU64(bytes));
        push(&mut c,format!("into_u64/{i}"),"spl_pod::primitives::<impl core::convert::From<spl_pod::primitives::PodU64> for u64>::from",&bytes,value);
    }
    c.write(&rec::out_dir()).expect("write Pod corpus");
}
