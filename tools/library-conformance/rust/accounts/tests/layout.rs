use conformance_accounts::{Account, Entry, Input, MAX_PERMITTED_DATA_INCREASE};

fn sample() -> Input {
    Input {
        entries: vec![
            Entry::Account(Account { key: [1; 32], owner: [2; 32], lamports: 5, data: vec![9, 8, 7],
                                     is_signer: true, is_writable: true, executable: false, rent_epoch: u64::MAX }),
            Entry::Duplicate(0),
            Entry::Account(Account { key: [3; 32], owner: [4; 32], lamports: 0, data: vec![],
                                     is_signer: false, is_writable: false, executable: true, rent_epoch: 7 }),
        ],
        instruction_data: vec![0xaa, 0xbb],
        program_id: [6; 32],
    }
}

#[test]
fn layout_matches_the_aligned_loader_format() {
    let mut region = sample().serialize();
    assert_eq!(region.as_mut_ptr() as usize % 16, 0);
    let b = region.bytes().to_vec();
    assert_eq!(&b[0..8], &3u64.to_le_bytes());
    assert_eq!(&b[8..16], &[0xff, 1, 1, 0, 0, 0, 0, 0]);
    assert_eq!(&b[16..48], &[1; 32]);
    assert_eq!(&b[80..88], &5u64.to_le_bytes());
    assert_eq!(&b[88..96], &3u64.to_le_bytes());
    assert_eq!(&b[96..99], &[9, 8, 7]);
    let rent = 96 + 3 + MAX_PERMITTED_DATA_INCREASE + 5;
    assert_eq!(&b[rent..rent + 8], &u64::MAX.to_le_bytes());
    let dup = rent + 8;
    assert_eq!(region.account_offset(1), dup);
    assert_eq!(&b[dup..dup + 8], &[0, 0, 0, 0, 0, 0, 0, 0]);
    let third = dup + 8;
    assert_eq!(region.account_offset(2), third);
    assert_eq!(third % 8, 0);
    let end = third + 88 + MAX_PERMITTED_DATA_INCREASE + 8;
    assert_eq!(&b[end..end + 8], &2u64.to_le_bytes());
    assert_eq!(&b[end + 8..end + 10], &[0xaa, 0xbb]);
    assert_eq!(&b[end + 10..], &[6; 32]);
}

#[test]
fn read_back_reports_changes_at_the_original_offsets() {
    let input = sample();
    let mut region = input.serialize();
    let p = region.account_ptr(0);
    unsafe {
        *p = 0; // mutably borrowed
        *(p.add(80) as *mut u64) = 5; // data_len 3 -> 5
        *p.add(88 + 4) = 1; // a spare byte written beyond the new length? no: within it
        *p.add(88 + 20) = 2; // a byte beyond the new length
    }
    let text = region.read_back().to_text();
    assert!(text.starts_with(r#"{"accounts":[{"marker":0,"is_signer":1,"is_writable":1,"executable":0,"padding":0,"#), "{text}");
    assert!(text.contains(r#""data_len":5,"data":"0908070001","rent_epoch":18446744073709551615,"spare_nonzero_at":20,"spare":"00000000000000000000000000000002[10222]","alignment_padding":"0000000000"}"#), "{text}");
    assert!(text.contains(r#"{"duplicate_of":0,"padding":"00000000000000"}"#), "{text}");
    assert!(text.ends_with(r#""count":3,"instruction_data":"aabb","program_id":"0606060606060606060606060606060606060606060606060606060606060606"}"#), "{text}");
    assert!(input.to_json().to_text().contains(r#"{"duplicate_of":0}"#));
}
