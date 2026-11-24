use conformance_recorder::{self as rec, Corpus, Json, Record};
use crate::{alloc_trace, AddressLookupTable, LookupTableMeta, ProgramState, Pubkey, LOOKUP_FUNCTION};
use std::borrow::Cow;

fn one(c: &mut Corpus, id: String, data: Vec<u8>, base: usize) {
    let mut backing = vec![0xf1; base];
    backing.extend_from_slice(&data);
    let input = &backing[base..];
    // Independently observe the selected bincode primitive and its owned-error
    // destructor. The SDK result below is a separate actual invocation.
    let (decoded, decode_events) = alloc_trace::measure(|| bincode::deserialize::<ProgramState>(input));
    let decoded_ok = decoded.is_ok();
    let (_, drop_events) = alloc_trace::measure(|| drop(decoded));
    if decoded_ok {
        assert!(decode_events.is_empty() && drop_events.is_empty());
    } else {
        assert!(!decode_events.is_empty() && !drop_events.is_empty());
    }
    let (result, actual_events) = alloc_trace::measure(|| AddressLookupTable::deserialize(input));
    let mut composed_events = decode_events.clone();
    composed_events.extend(drop_events.iter().cloned());
    assert_eq!(actual_events, composed_events, "SDK decode/map_err allocation order");
    let observed = match result {
        Err(e) => rec::err(format!("{e:?}").into()),
        Ok(t) => {
            assert!(matches!(t.addresses, Cow::Borrowed(_)));
            let offset = (t.addresses.as_ptr() as usize).checked_sub(input.as_ptr() as usize).unwrap();
            Json::obj([("ok", Json::obj([
                ("meta", Json::obj([("deactivation_slot", t.meta.deactivation_slot.into()),
                    ("last_extended_slot", t.meta.last_extended_slot.into()),
                    ("last_extended_slot_start_index", t.meta.last_extended_slot_start_index.into()),
                    ("authority", t.meta.authority.map(|p| rec::bytes(p.as_ref())).unwrap_or(Json::Null)),
                    ("padding", t.meta._padding.into())])),
                ("addresses", Json::obj([("address", (base + offset).into()),
                    ("bytes", rec::bytes(&t.addresses.iter().flat_map(|p| p.to_bytes()).collect::<Vec<_>>()))])),
            ]))])
        }
    };
    assert_eq!(input, data.as_slice());
    c.push(Record { id, function: LOOKUP_FUNCTION, generics: vec![], layout: None, state: Json::Arr(vec![]),
        args: Json::obj([("address", base.into()), ("bytes", rec::bytes(input)),
            ("codec_probe", Json::obj([("ok", decoded_ok.into()),
                ("decode", alloc_trace::json(&decode_events)), ("drop", alloc_trace::json(&drop_events))]))]),
        outcome: rec::returned(observed, alloc_trace::json(&actual_events)), observed: None });
}
pub fn record(c: &mut Corpus) {
    for (i, bytes) in [vec![], vec![0], vec![0; 3], vec![0; 4], vec![0; 87], vec![2, 0, 0, 0], vec![255; 56]].into_iter().enumerate() {
        one(c, format!("lookup-enum-{i}"), bytes, i);
    }
    for has_authority in [false, true] {
        let meta = LookupTableMeta { deactivation_slot: u64::MAX, last_extended_slot: 123,
            last_extended_slot_start_index: 255, authority: has_authority.then_some(Pubkey::new_from_array([7; 32])), _padding: 0xabcd };
        let encoded = bincode::serialize(&ProgramState::LookupTable(meta)).unwrap();
        for prefix in 4..encoded.len() { one(c, format!("lookup-prefix-{has_authority}-{prefix}"), encoded[..prefix].to_vec(), 1); }
        one(c, format!("lookup-exact-meta-{has_authority}"), encoded.clone(), 3);
        let mut full = encoded;
        full.resize(56, 0x91);
        for count in [0, 1, 2, 256, 257] {
            for base in [0, 1, 7] {
                let mut bytes = full.clone();
                bytes.extend((0..count * 32).map(|i| (i % 251) as u8));
                one(c, format!("lookup-addresses-{has_authority}-{count}-{base}"), bytes, base);
            }
        }
        for slop in [1, 31, 33] {
            let mut bytes = full.clone(); bytes.extend(vec![0; slop]);
            one(c, format!("lookup-slop-{has_authority}-{slop}"), bytes, 0);
        }
        full[21] = 2;
        one(c, format!("lookup-option-invalid-{has_authority}"), full, 0);
    }
}
