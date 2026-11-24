//! Modern SDK key and nullable calls at the exact manifest pins.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use crate::support::{self as s,Tracked,Plan};
impl solana_nullable::Nullable for Tracked {
    const NONE: Self = Self {id:1,value:0,drop_mode:0};
    fn is_none(&self)->bool {self.query()}
}
fn push(c:&mut Corpus,id:String,function:&'static str,args:Json,result:Json) {
    c.push(Record{id,function,generics:vec![],layout:None,state:Json::Null,args,outcome:rec::returned(result,Json::Null),observed:None});
}
fn ids() {
    let mut c=Corpus::new("sdk_values_solana_sdk_ids_3_1_0",&[("solana-sdk-ids","3.1.0")]);
    for (name,f) in [
        ("solana_sdk_ids::bpf_loader_upgradeable::id",solana_sdk_ids::bpf_loader_upgradeable::id as fn()->solana_address::Address),
        ("solana_sdk_ids::ed25519_program::id",solana_sdk_ids::ed25519_program::id),
        ("solana_sdk_ids::sysvar::instructions::id",solana_sdk_ids::sysvar::instructions::id),
        ("solana_sdk_ids::vote::id",solana_sdk_ids::vote::id),
    ] {
        push(&mut c,name.into(),name,Json::Null,rec::bytes(&f().to_bytes()));
    }
    c.write(&rec::out_dir()).expect("write ID corpus");
}
fn optional_keys() {
    let mut c=Corpus::new("sdk_values_spl_pod_0_7_3",&[("spl-pod","0.7.3")]);
    let mut cases=vec![[0;32],[255;32]];
    for i in 0..32 {let mut key=[0;32];key[i]=1;cases.push(key);}
    for (i,bytes) in cases.into_iter().enumerate() {
        let key=solana_pubkey::Pubkey::new_from_array(bytes);
        let value:Option<solana_pubkey::Pubkey>=spl_pod::optional_keys::OptionalNonZeroPubkey(key).into();
        push(&mut c,format!("into_option/{i}"),"spl_pod::optional_keys::<impl core::convert::From<spl_pod::optional_keys::OptionalNonZeroPubkey> for core::option::Option<solana_address::Address>>::from",Json::obj([("key",rec::bytes(&bytes))]),rec::option(&value,|v|rec::bytes(&v.to_bytes())));
    }
    c.write(&rec::out_dir()).expect("write optional key corpus");
}
fn nullable() {
    let mut c=Corpus::new("sdk_values_solana_nullable_1_3_0",&[("solana-nullable","1.3.0")]);
    for is_null in [false,true] {for query_mode in 0..3 {for drop_mode in 0..3 {
        let args=Json::obj([("value",s::tracked_json(1,7,drop_mode)),("mode",(query_mode as u64).into()),("is_null",is_null.into())]);
        let outcome=s::case(|| {
            s::reset(Plan {query:query_mode,is_null,..Plan::NORMAL});
            let x=solana_nullable::MaybeNull::from(Tracked::new(1,7,drop_mode));s::assert_initial(&[1]);
            s::finish(rec::catch(||x.get()),|v|rec::option(v,Tracked::json))
        });
        c.push(Record{id:format!("get/{is_null}_{query_mode}_{drop_mode}"),function:"solana_nullable::maybe_null::MaybeNull::<T>::get",generics:vec![("T","Tracked".into())],layout:None,state:s::initial(&[1]),args,outcome,observed:None});
    }}}
    c.write(&rec::out_dir()).expect("write nullable corpus");
}
pub fn record() {ids();optional_keys();nullable();}
