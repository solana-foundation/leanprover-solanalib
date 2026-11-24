//! Native calls at the exact released versions. Allocations are measured only
//! inside each SDK call; creation of input strings and signer arrays is outside.
mod common;
use common::{counted,heap,k,key,result,opt};
use conformance_recorder::{bytes,catch,returned,unwound,Corpus,Json,Record};
use solana_pubkey::Pubkey;
use solana_instruction::Instruction;
use solana_program_error::ProgramError;
#[global_allocator]
static ALLOCATOR: common::Counting = common::Counting;
fn pk(seed:u8)->Pubkey { Pubkey::new_from_array(k(seed)) }
fn ix(i:&Instruction)->Json { Json::obj([
 ("program_id",key(i.program_id.as_ref())),
 ("accounts",Json::arr(i.accounts.iter(),|m|Json::obj([("pubkey",key(m.pubkey.as_ref())),("is_signer",m.is_signer.into()),("is_writable",m.is_writable.into())]))),
 ("data",bytes(&i.data))]) }
fn construct(f:impl FnOnce()->Result<Instruction,ProgramError>)->Json {
 let (r,a,d)=counted(||catch(f)); match r {
 Ok(v)=>returned(result(&v,ix),heap(a,d)),Err(e)=>unwound(e,heap(a,d)) }
}
fn record(c:&mut Corpus,id:String,function:&'static str,args:Json,outcome:Json) {
 c.push(Record{id,function,generics:vec![],layout:None,state:Json::Null,args,outcome,observed:None});
}
fn programs()->Vec<Pubkey> { let mut near=spl_token_2022::id().to_bytes();near[31]^=1;
 vec![spl_token::id(),spl_token_2022::id(),Pubkey::default(),Pubkey::new_from_array(near)] }
fn signer_sets()->Vec<Vec<Pubkey>> {vec![vec![],vec![pk(4)],vec![pk(4),pk(4)],(30..42).map(pk).collect()]}
fn auth_args(p:Pubkey,s:Pubkey,d:Pubkey,a:Pubkey,signers:&[Pubkey],amount:u64,decimals:u8)->Json {
 Json::obj([("program_id",key(p.as_ref())),("source",key(s.as_ref())),("destination",key(d.as_ref())),("authority",key(a.as_ref())),
 ("signers",Json::arr(signers.iter(),|x|key(x.as_ref()))),("amount",amount.into()),("decimals",decimals.into()),("mint",key(pk(7).as_ref()))])
}
fn standard(c:&mut Corpus,legacy:bool) {
 for (pi,p) in programs().into_iter().enumerate() { for (si,signers) in signer_sets().into_iter().enumerate() {
 let refs:Vec<&Pubkey>=signers.iter().collect();let s=pk(1);let d=if si==2 {s} else {pk(2)};let a=pk(3);
 let amount=[0,513,u64::MAX,1<<32][si];let decimals=[0,6,255,9][si];let args=auth_args(p,s,d,a,&signers,amount,decimals);
 if legacy {
 record(c,format!("mint_to/{pi}/{si}"),"spl_token::instruction::mint_to",args.clone(),construct(||spl_token::instruction::mint_to(&p,&s,&d,&a,&refs,amount)));
 record(c,format!("burn_checked/{pi}/{si}"),"spl_token::instruction::burn_checked",args.clone(),construct(||spl_token::instruction::burn_checked(&p,&s,&d,&a,&refs,amount,decimals)));
 record(c,format!("close_account/{pi}/{si}"),"spl_token::instruction::close_account",args.clone(),construct(||spl_token::instruction::close_account(&p,&s,&d,&a,&refs)));
 }
 if !legacy {
 record(c,format!("mint_to/{pi}/{si}"),"spl_token_2022::instruction::mint_to",args.clone(),construct(||spl_token_2022::instruction::mint_to(&p,&s,&d,&a,&refs,amount)));
 record(c,format!("burn_checked/{pi}/{si}"),"spl_token_2022::instruction::burn_checked",args.clone(),construct(||spl_token_2022::instruction::burn_checked(&p,&s,&d,&a,&refs,amount,decimals)));
 record(c,format!("close_account/{pi}/{si}"),"spl_token_2022::instruction::close_account",args.clone(),construct(||spl_token_2022::instruction::close_account(&p,&s,&d,&a,&refs)));
 record(c,format!("freeze_account/{pi}/{si}"),"spl_token_2022::instruction::freeze_account",args.clone(),construct(||spl_token_2022::instruction::freeze_account(&p,&s,&d,&a,&refs)));
 record(c,format!("thaw_account/{pi}/{si}"),"spl_token_2022::instruction::thaw_account",args.clone(),construct(||spl_token_2022::instruction::thaw_account(&p,&s,&d,&a,&refs)));
 record(c,format!("transfer_checked/{pi}/{si}"),"spl_token_2022::instruction::transfer_checked",args.clone(),construct(||spl_token_2022::instruction::transfer_checked(&p,&s,&pk(7),&d,&a,&refs,amount,decimals)));
 }
 }}
 for (pi,p) in programs().into_iter().enumerate() {
 let count=if legacy {4} else {17}; for code in 0..count { for (oi,replacement) in [None,Some(Pubkey::default()),Some(pk(9))].into_iter().enumerate() {
 let signers=if oi==2 {vec![pk(5),pk(5)]}else{vec![]};let refs:Vec<&Pubkey>=signers.iter().collect();
 let args=Json::obj([("program_id",key(p.as_ref())),("owned",key(pk(1).as_ref())),("owner",key(pk(2).as_ref())),("authority_type",Json::from(code as u64)),("new_authority",opt(replacement,|k|key(k.as_ref()))),("signers",Json::arr(signers.iter(),|k|key(k.as_ref()))) ]);
 if legacy {use spl_token::instruction::AuthorityType as T;let t=match code {0=>T::MintTokens,1=>T::FreezeAccount,2=>T::AccountOwner,3=>T::CloseAccount,_=>unreachable!()};
 record(c,format!("set_authority/{pi}/{code}/{oi}"),"spl_token::instruction::set_authority",args,construct(||spl_token::instruction::set_authority(&p,&pk(1),replacement.as_ref(),t,&pk(2),&refs)));
 }else{use spl_token_2022::instruction::AuthorityType as T;let t=match code {0=>T::MintTokens,1=>T::FreezeAccount,2=>T::AccountOwner,3=>T::CloseAccount,4=>T::TransferFeeConfig,5=>T::WithheldWithdraw,6=>T::CloseMint,7=>T::InterestRate,8=>T::PermanentDelegate,9=>T::ConfidentialTransferMint,10=>T::TransferHookProgramId,11=>T::ConfidentialTransferFeeConfig,12=>T::MetadataPointer,13=>T::GroupPointer,14=>T::GroupMemberPointer,15=>T::ScaledUiAmount,16=>T::Pause,_=>unreachable!()};
 record(c,format!("set_authority/{pi}/{code}/{oi}"),"spl_token_2022::instruction::set_authority",args,construct(||spl_token_2022::instruction::set_authority(&p,&pk(1),replacement.as_ref(),t,&pk(2),&refs)));
 }
 }}}
}
fn token_extra(c:&mut Corpus) {
 for (pi,p) in programs().into_iter().enumerate() {
 let one=Json::obj([("program_id",key(p.as_ref())),("account",key(pk(1).as_ref()))]);
 record(c,format!("initialize_immutable_owner/{pi}"),"spl_token_2022::instruction::initialize_immutable_owner",one.clone(),construct(||spl_token_2022::instruction::initialize_immutable_owner(&p,&pk(1))));
 record(c,format!("initialize_non_transferable_mint/{pi}"),"spl_token_2022::instruction::initialize_non_transferable_mint",one.clone(),construct(||spl_token_2022::instruction::initialize_non_transferable_mint(&p,&pk(1))));
 let init=Json::obj([("program_id",key(p.as_ref())),("account",key(pk(1).as_ref())),("mint",key(pk(2).as_ref())),("owner",key(pk(3).as_ref()))]);
 record(c,format!("initialize_account3/{pi}"),"spl_token_2022::instruction::initialize_account3",init,construct(||spl_token_2022::instruction::initialize_account3(&p,&pk(1),&pk(2),&pk(3))));
 for (oi,authority) in [None,Some(Pubkey::default()),Some(pk(3))].into_iter().enumerate() {
 let args=Json::obj([("program_id",key(p.as_ref())),("account",key(pk(1).as_ref())),("close_authority",opt(authority,|k|key(k.as_ref())))]);
 record(c,format!("initialize_mint_close_authority/{pi}/{oi}"),"spl_token_2022::instruction::initialize_mint_close_authority",args,construct(||spl_token_2022::instruction::initialize_mint_close_authority(&p,&pk(1),authority.as_ref())));
 let decimals=if oi==2 {255}else{0};let args=Json::obj([("program_id",key(p.as_ref())),("mint",key(pk(1).as_ref())),("decimals",decimals.into()),("authority",key(pk(2).as_ref())),("freeze_authority",opt(authority,|k|key(k.as_ref())))]);
 record(c,format!("initialize_mint2/{pi}/{oi}"),"spl_token_2022::instruction::initialize_mint2",args,construct(||spl_token_2022::instruction::initialize_mint2(&p,&pk(1),&pk(2),authority.as_ref(),decimals)));
 for (mi,metadata) in [None,Some(Pubkey::default()),Some(pk(4))].into_iter().enumerate() {
 let args=Json::obj([("program_id",key(p.as_ref())),("mint",key(pk(1).as_ref())),("authority",opt(authority,|k|key(k.as_ref()))),("metadata_address",opt(metadata,|k|key(k.as_ref())))]);
 record(c,format!("metadata_pointer/{pi}/{oi}/{mi}"),"spl_token_2022::extension::metadata_pointer::instruction::initialize",args,construct(||spl_token_2022::extension::metadata_pointer::instruction::initialize(&p,&pk(1),authority,metadata)));
 }
 }
 }
}
fn ids(c:&mut Corpus,legacy:bool){
 let actual=if legacy{spl_token::native_mint::id()}else{spl_token_2022::native_mint::id()};
 let name=if legacy{"spl_token::native_mint::id"}else{"spl_token_2022::native_mint::id"};
 record(c,"native_id".into(),name,Json::Null,returned(key(actual.as_ref()),Json::Null));
 for (i,value) in [actual,Pubkey::default(),spl_token::native_mint::id(),spl_token_2022::native_mint::id(),pk(8)].into_iter().enumerate(){
 let (name,result)=if legacy{("spl_token::native_mint::check_id",spl_token::native_mint::check_id(&value))}else{("spl_token_2022::native_mint::check_id",spl_token_2022::native_mint::check_id(&value))};
 record(c,format!("native_check/{i}"),name,key(value.as_ref()),returned(result.into(),Json::Null));
 }
 if !legacy{record(c,"id".into(),"spl_token_2022::id",Json::Null,returned(key(spl_token_2022::id().as_ref()),Json::Null));}
}
fn metadata(c:&mut Corpus){
 for (i,(name,symbol,uri)) in [("","",""),("Token","SYM","https://example.invalid/x"),("λ😀","Σ",""),("a\\0b","\\0","雪")].into_iter().enumerate(){
 let (name,symbol,uri)=(name.to_owned(),symbol.to_owned(),uri.to_owned());
 let p=if i==1{spl_token_2022::id()}else{Pubkey::default()}; let m=pk(1); let u=if i==2{m}else{pk(2)};
 let args=Json::obj([("program_id",key(p.as_ref())),("metadata",key(m.as_ref())),("update_authority",key(u.as_ref())),("mint",key(pk(3).as_ref())),("mint_authority",key(pk(4).as_ref())),("name",name.clone().into()),("symbol",symbol.clone().into()),("uri",uri.clone().into())]);
 record(c,format!("initialize/{i}"),"spl_token_metadata_interface::instruction::initialize",args,construct(||Ok(spl_token_metadata_interface::instruction::initialize(&p,&m,&u,&pk(3),&pk(4),name,symbol,uri))));
 }
}
fn main(){conformance_recorder::init();let out=conformance_recorder::out_dir();
 let mut a=Corpus::new("spl_token_8_0_0_instructions",&[("spl-token","8.0.0")]);standard(&mut a,true);ids(&mut a,true);a.write(&out).unwrap();
 let mut b=Corpus::new("spl_token_2022_8_0_1_instructions",&[("spl-token-2022","8.0.1")]);standard(&mut b,false);token_extra(&mut b);ids(&mut b,false);b.write(&out).unwrap();
 let mut m=Corpus::new("spl_token_metadata_interface_0_7_0_initialize",&[("spl-token-metadata-interface","0.7.0")]);metadata(&mut m);m.write(&out).unwrap();
 let mut memo=Corpus::new("spl_memo_6_0_0_id",&[("spl-memo","6.0.0")]);record(&mut memo,"id".into(),"spl_memo::id",Json::Null,returned(key(spl_memo::id().as_ref()),Json::Null));memo.write(&out).unwrap();
}
