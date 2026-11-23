//! Checked SDK loaders over real Rc<RefCell> aliases and tracked owned Vecs.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use crate::{AccountInfo, Pubkey, Instruction, instructions_sysvar, track};

fn borrow_flags(account: &AccountInfo) -> (bool,bool) {
    let read = account.try_borrow_data().is_ok();
    let write = account.try_borrow_mut_data().is_ok();
    (read,write)
}
fn state(data: &[u8], flags: (bool,bool), allocations: &[usize], frees: &[usize], live: &[usize]) -> Json {
    Json::obj([("data",rec::bytes(data)), ("read_ok",flags.0.into()), ("write_ok",flags.1.into()),
        ("allocations",Json::arr(allocations, |i| (*i).into())),
        ("frees",Json::arr(frees, |i| (*i).into())), ("live",Json::arr(live, |i| (*i).into()))])
}
fn instruction(value: &Instruction, log: &track::Log) -> Json {
    let index = |pointer: usize, capacity: usize| {
        if capacity == 0 { Json::Null } else {
            let position = log.allocs.iter().position(|p| *p == pointer).expect("returned vector allocation was tracked");
            assert!(log.fresh_live.contains(&pointer), "returned vector allocation remains live");
            position.into()
        }
    };
    Json::obj([("program_id",rec::bytes(value.program_id.as_ref())),
        ("accounts",Json::arr(&value.accounts, |a| Json::obj([("pubkey",rec::bytes(a.pubkey.as_ref())),
            ("is_signer",a.is_signer.into()), ("is_writable",a.is_writable.into())]))),
        ("data",rec::bytes(&value.data)), ("account_capacity",value.accounts.capacity().into()),
        ("data_capacity",value.data.capacity().into()),
        ("account_allocation",index(value.accounts.as_ptr() as usize,value.accounts.capacity())),
        ("data_allocation",index(value.data.as_ptr() as usize,value.data.capacity()))])
}

fn call(c: &mut Corpus, id: String, bytes: Vec<u8>, right_key: bool, held: u8, index: Option<usize>) {
    let key = if right_key { instructions_sysvar::id() } else { Pubkey::new_from_array([7;32]) };
    let function = if index.is_some() { "solana_instructions_sysvar::load_instruction_at_checked" }
        else { "solana_instructions_sysvar::load_current_index_checked" };
    let before = state(&bytes,(held != 2,held == 0),&[],&[],&[]);
    let args = Json::obj([("key",rec::bytes(key.as_ref())), ("held",held.into()),
        ("index",index.map_or(Json::Null,Json::from)),
        ("overflow_checks",crate::rent_cases::overflow_checks().into()), ("panic","unwind".into())]);
    let outcome = shim::case(&Script::new(vec![]), || {
        let mut data = bytes.clone(); let owner = Pubkey::new_from_array([9;32]); let mut lamports = 73;
        let account = AccountInfo::new(&key,false,false,&mut lamports,&mut data,&owner,false);
        let alias = account.clone();
        assert!(std::rc::Rc::ptr_eq(&account.data,&alias.data));
        let shared = if held == 1 { Some(alias.try_borrow_data().unwrap()) } else { None };
        let exclusive = if held == 2 { Some(alias.try_borrow_mut_data().unwrap()) } else { None };
        let data_after = || -> Vec<u8> {
            if let Some(guard) = &exclusive { guard.to_vec() }
            else if let Some(guard) = &shared { guard.to_vec() }
            else { account.try_borrow_data().unwrap().to_vec() }
        };
        if let Some(index) = index {
            let (result, log) = track::tracked(|| instructions_sysvar::load_instruction_at_checked(index,&account));
            let ids: Vec<usize> = (0..log.allocs.len()).collect();
            let ordinal = |pointer: &usize| log.allocs.iter().position(|p| p == pointer).expect("only local vectors freed");
            let frees: Vec<usize> = log.frees.iter().map(ordinal).collect();
            let live: Vec<usize> = log.fresh_live.iter().map(ordinal).collect();
            let after = state(&data_after(),borrow_flags(&account),&ids,&frees,&live);
            match result {
                Ok(value) => rec::returned(crate::syscall_cases::program_error(&value, |v| instruction(v,&log)),after),
                Err(reason) => rec::unwound(reason,after),
            }
        } else {
            let result = rec::catch(|| instructions_sysvar::load_current_index_checked(&account));
            let after = state(&data_after(),borrow_flags(&account),&[],&[],&[]);
            match result {
                Ok(value) => rec::returned(crate::syscall_cases::program_error(&value, |v| (*v).into()),after),
                Err(reason) => rec::unwound(reason,after),
            }
        }
    });
    c.push(Record {id,function,generics:vec![],layout:None,state:before,args,outcome,observed:None});
}

fn encoded(flags: &[u8], payload: &[u8]) -> Vec<u8> {
    let mut bytes = vec![1,0,4,0];
    bytes.extend_from_slice(&(flags.len() as u16).to_le_bytes());
    for (number,flag) in flags.iter().enumerate() {
        bytes.push(*flag); bytes.extend_from_slice(&crate::syscall_cases::pattern(32,number as u8 + 17));
    }
    bytes.extend_from_slice(&crate::syscall_cases::pattern(32,91));
    bytes.extend_from_slice(&(payload.len() as u16).to_le_bytes());bytes.extend_from_slice(payload);
    bytes.extend_from_slice(&[0xFE,0xFF]);bytes
}

pub fn record(c: &mut Corpus) {
    for (n,bytes) in [vec![],vec![7],vec![0,0],vec![0xFE,0xFF],vec![7,8,9,1,2]].into_iter().enumerate() {
        for held in 0..3 { call(c,format!("current/{n}/{held}"),bytes.clone(),true,held,None); }
        call(c,format!("current_wrong/{n}"),bytes,false,2,None);
    }
    let valid = encoded(&[3],&[7,8,9]);
    for length in 0..=valid.len() {
        call(c,format!("truncated/{length}"),valid[..length].to_vec(),true,0,Some(0));
    }
    for (n,bytes) in [encoded(&[],&[]),encoded(&[0,1,2,3,255],&[]),encoded(&[],&[0,1,255]),
                     vec![1,0,255,255],vec![1,0,4,0,255,255]].into_iter().enumerate() {
        for held in 0..3 { call(c,format!("instruction/{n}/{held}"),bytes.clone(),true,held,Some(0)); }
        call(c,format!("instruction_wrong/{n}"),bytes.clone(),false,2,Some(0));
        call(c,format!("index_end/{n}"),bytes.clone(),true,0,Some(1));
        call(c,format!("index_max/{n}"),bytes,true,0,Some(usize::MAX));
    }
    // Offsets are read from the table; they need not be sorted or point past it.
    let mut two = encoded(&[],&[1,2]);
    two[0] = 2;two.splice(4..4,[6,0]);two[2] = 6;
    call(c,"two_same_offset/0".into(),two.clone(),true,0,Some(0));
    call(c,"two_same_offset/1".into(),two,true,0,Some(1));
}
