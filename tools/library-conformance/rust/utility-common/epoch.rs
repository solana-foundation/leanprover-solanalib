//! Arbitrary public fields, cast and saturation boundaries; typed default getter.
use crate::{EpochSchedule, Sysvar};
use crate::syscall_cases::*;
use conformance_recorder::{self as rec, Corpus, Json, Record};

pub fn json(v: &EpochSchedule) -> Json {
    Json::obj([("slots_per_epoch", v.slots_per_epoch.into()),
        ("leader_schedule_slot_offset", v.leader_schedule_slot_offset.into()), ("warmup", v.warmup.into()),
        ("first_normal_epoch", v.first_normal_epoch.into()), ("first_normal_slot", v.first_normal_slot.into())])
}

pub fn queries(c: &mut Corpus, first: Option<&'static str>, last: Option<&'static str>) {
    let schedules = [EpochSchedule::default(),
        EpochSchedule { slots_per_epoch: 0, leader_schedule_slot_offset: u64::MAX, warmup: false,
            first_normal_epoch: 0, first_normal_slot: 0 },
        EpochSchedule { slots_per_epoch: u64::MAX, leader_schedule_slot_offset: 7, warmup: true,
            first_normal_epoch: 2, first_normal_slot: u64::MAX },
        EpochSchedule { slots_per_epoch: 3, leader_schedule_slot_offset: 0, warmup: false,
            first_normal_epoch: u64::MAX, first_normal_slot: 5 }];
    for (schedule, value) in schedules.iter().enumerate() {
        for epoch in [0, 1, 2, 13, 14, 15, 58, 59, 63, 64, u32::MAX as u64, 1 << 32, (1 << 32) + 1, u64::MAX] {
            for (function, method) in [(first, EpochSchedule::get_first_slot_in_epoch as fn(&EpochSchedule,u64)->u64),
                                      (last, EpochSchedule::get_last_slot_in_epoch as fn(&EpochSchedule,u64)->u64)] {
                if let Some(function) = function {
                    let args = Json::obj([("schedule", json(value)), ("epoch", epoch.into())]);
                    c.push(Record { id: format!("{function}/{schedule}/{epoch}"), function,
                        generics: vec![], layout: None, state: Json::Null, args,
                        outcome: rec::returned(method(value, epoch).into(), Json::Null), observed: None });
                }
            }
        }
    }
}

pub fn getter(c: &mut Corpus, function: &'static str) {
    let encode = |slots: u64, offset: u64, warmup: bool, first_epoch: u64, first_slot: u64| {
        let mut bytes = [slots.to_le_bytes(), offset.to_le_bytes()].concat();
        bytes.push(warmup as u8); bytes.extend_from_slice(&[0xA5; 7]);
        bytes.extend_from_slice(&first_epoch.to_le_bytes()); bytes.extend_from_slice(&first_slot.to_le_bytes()); bytes
    };
    let values = vec![("default", encode(432000,432000,true,14,524256)),
        ("arbitrary", encode(u64::MAX,7,false,u64::MAX,0)),
        ("no_bytes", vec![]), ("slots_only", 32u64.to_le_bytes().to_vec()),
        ("warmup_only_prefix", encode(1,2,false,0,0)[..17].to_vec())];
    for (name, script) in crate::sysvar_scripts::scripts("sol_get_epoch_schedule_sysvar", &values) {
        syscall_case(c, format!("epoch_get/{name}"), function, Json::Null, script, EpochSchedule::get,
            |r| program_error(r, json));
    }
}
