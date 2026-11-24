//! The exact typed SDK getter and old status-conversion boundaries.
use crate::{Clock, Rent, Sysvar, ProgramError, track};
use crate::syscall_cases::*;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use crate::sysvar_scripts::scripts;

/// The allocator also observes shim bookkeeping. Project only the allocation
/// identified by the actual returned BorshIoError String pointer. Its freshness,
/// live ownership, current contents and capacity are independently inspected;
/// pointer addresses are normalized to the ordinal of the sole returned resource.
fn getter_case<T>(c: &mut Corpus, id: String, function: &'static str, args: Json,
    script: Script, f: impl FnOnce() -> Result<T, ProgramError>, enc: impl Fn(&Result<T, ProgramError>) -> Json) {
    let state = Json::obj([("syscalls",script.state_before()), ("strings",Json::Arr(vec![]))]);
    let outcome = shim::case(&script, || {
        let (result, log) = track::tracked(f);
        let strings = match &result {
            Ok(Err(ProgramError::BorshIoError(message))) => {
                let pointer = message.as_ptr() as usize;
                assert!(message.capacity() > 0);
                assert!(log.allocs.contains(&pointer), "the returned String was allocated during the getter");
                assert!(log.fresh_live.contains(&pointer), "the returned String remains owned and live");
                vec![Json::obj([("text",message.as_str().into()), ("capacity",message.capacity().into()),
                    ("fresh",true.into()), ("live",true.into())])]
            },
            _ => vec![],
        };
        let after = Json::obj([("syscalls",shim::state()), ("strings",Json::Arr(strings))]);
        match result {
            Ok(value) => rec::returned(enc(&value),after),
            Err(reason) => rec::unwound(reason,after),
        }
    });
    c.push(Record { id,function,generics:vec![],layout:None,state,args,outcome,observed:None });
}

pub fn record(c: &mut Corpus, clock: Option<&'static str>, rent: Option<&'static str>) {
    if let Some(function) = clock {
        let mut values: Vec<(&'static str, Vec<u8>)> = clocks().into_iter().map(|(n, f)| (n, clock_bytes(f))).collect();
        values.push(("no_bytes", vec![]));
        values.push(("slot_only", 77u64.to_le_bytes().to_vec()));
        for (name, script) in scripts("sol_get_clock_sysvar", &values) {
            getter_case(c, format!("clock/{name}"), function, Json::Null, script,
                Clock::get, |r| program_error(r, |v: &Clock|
                    clock_json(v.slot, v.epoch_start_timestamp, v.epoch, v.leader_schedule_epoch, v.unix_timestamp)));
        }
    }
    if let Some(function) = rent {
        let bytes = |rate: u64, bits: u64, burn: u8| {
            let mut b = [rate.to_le_bytes(), bits.to_le_bytes()].concat(); b.push(burn); b
        };
        let values = vec![("default", bytes(3480, 0x4000000000000000, 50)),
            ("extremes", bytes(u64::MAX, 0xfff8000000000001, 255)),
            ("no_bytes", vec![]), ("rate_only", 17u64.to_le_bytes().to_vec())];
        for (name, script) in scripts("sol_get_rent_sysvar", &values) {
            getter_case(c, format!("rent/{name}"), function, Json::Null, script, Rent::get,
                |r| program_error(r, crate::rent_cases_native::json));
        }
    }
}
