//! Published Mint::clone, observed through the SDK Pack encoding.
//! The separate repr(C) layout observation is not the packed account encoding.
use conformance_recorder::{bytes, returned, Corpus, Json, Record};
use solana_program_pack::Pack;
use token_api::state::Mint;
#[path = "../../common/token_state_versions_alloc.rs"]
mod allocation;
#[global_allocator]
static ALLOCATOR: allocation::Counter = allocation::Counter;

fn mint(supply: u64, flags: u8) -> Mint {
    Mint {
        mint_authority: if flags & 1 != 0 { Some([3u8; 32].into()).into() } else { None.into() },
        supply,
        decimals: if flags & 2 != 0 { 255 } else { 9 },
        is_initialized: flags & 2 != 0,
        freeze_authority: if flags & 2 != 0 { Some([7u8; 32].into()).into() } else { None.into() },
    }
}
fn packed(value: &Mint) -> [u8; Mint::LEN] {
    let mut output = [0; Mint::LEN];
    value.pack_into_slice(&mut output);
    output
}
fn layout() -> Json {
    Json::obj([
        ("size", std::mem::size_of::<Mint>().into()),
        ("alignment", std::mem::align_of::<Mint>().into()),
        ("offsets", Json::arr([
            std::mem::offset_of!(Mint, mint_authority), std::mem::offset_of!(Mint, supply),
            std::mem::offset_of!(Mint, decimals), std::mem::offset_of!(Mint, is_initialized),
            std::mem::offset_of!(Mint, freeze_authority),
        ], Json::from)),
    ])
}
fn main() {
    conformance_recorder::init();
    let mut corpus = Corpus::new("token_state_interface_3_1_1", &[("spl-token-2022-interface", "3.1.1")]);
    for supply in [0, 1, u64::MAX] {
        for flags in 0..4 {
            let input = mint(supply, flags);
            let before = packed(&input);
            let (output, counts) = allocation::counted(|| input.clone());
            assert_eq!(counts, [0, 0, 0], "this concrete Clone has no allocation dependency");
            assert_eq!(output, input);
            corpus.push(Record {
                id: format!("clone/{supply}/{flags}"),
                function: "<spl_token_2022_interface::state::Mint as core::clone::Clone>::clone",
                generics: vec![], layout: Some(layout()), state: bytes(&before), args: Json::empty(),
                outcome: returned(bytes(&packed(&output)), bytes(&packed(&input))),
                observed: Some(Json::obj([("heap_counts", Json::arr(counts, Json::from))])),
            });
        }
    }
    corpus.write(&conformance_recorder::out_dir()).unwrap();
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn clone_needs_no_allocator() {
        assert!(!allocation::aborts_on_next_allocation(|| {
            let input = mint(u64::MAX, 3);
            assert_eq!(input.clone(), input);
        }));
    }
    #[test]
    fn source_layout_is_distinct_from_packed_account_bytes() {
        assert_eq!(std::mem::size_of::<Mint>(), 88);
        assert_eq!(std::mem::align_of::<Mint>(), 8);
        assert_eq!([std::mem::offset_of!(Mint, mint_authority), std::mem::offset_of!(Mint, supply),
                    std::mem::offset_of!(Mint, decimals), std::mem::offset_of!(Mint, is_initialized),
                    std::mem::offset_of!(Mint, freeze_authority)], [0, 40, 48, 49, 52]);
        assert_eq!(Mint::LEN, 82);
    }
}
