//! Serialized program input for the loader (BPF loader ABI v1, aligned), built
//! from an account list and read back after a call.
//!
//! Layout, as `agave` `serialize_parameters_aligned` writes it (all integers
//! little-endian, every offset a multiple of 8):
//!
//! ```text
//! u64 number of accounts
//! per account, either a duplicate: u8 index of the first occurrence, 7 zero bytes
//!   or: u8 0xff (NON_DUP_MARKER; account-view reuses it as the borrow state),
//!       u8 is_signer, u8 is_writable, u8 executable,
//!       4 zero bytes (account-view resize delta; the solana-program deserialize function
//!                     stores the original data length there),
//!       [u8; 32] key, [u8; 32] owner, u64 lamports, u64 data length, data,
//!       10 KiB of zeros (MAX_PERMITTED_DATA_INCREASE) plus padding to a multiple of 8,
//!       u64 rent epoch
//! u64 instruction data length, instruction data, [u8; 32] program id
//! ```
//!
//! The region lives in a 16-aligned buffer, as the runtime input region is
//! aligned. `Input::to_json` is the account list of the record state;
//! `Region::read_back` is the region after the call, at the offsets fixed by
//! the original layout.

use conformance_recorder::{self as rec, Json};

pub const NON_DUP_MARKER: u8 = 0xff;
pub const MAX_PERMITTED_DATA_INCREASE: usize = 10 * 1024;
pub const BPF_ALIGN_OF_U128: usize = 8;
/// Size of the fixed part of a non-duplicate account before its data.
pub const ACCOUNT_HEADER: usize = 8 + 32 + 32 + 8 + 8;

#[derive(Clone, Debug, Default)]
pub struct Account {
    pub key: [u8; 32],
    pub owner: [u8; 32],
    pub lamports: u64,
    pub data: Vec<u8>,
    pub is_signer: bool,
    pub is_writable: bool,
    pub executable: bool,
    pub rent_epoch: u64,
}

#[derive(Clone, Debug)]
pub enum Entry {
    Account(Account),
    /// A repeated account: the index of its first occurrence.
    Duplicate(u8),
}

#[derive(Clone, Debug, Default)]
pub struct Input {
    pub entries: Vec<Entry>,
    pub instruction_data: Vec<u8>,
    pub program_id: [u8; 32],
}

impl Account {
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("key", rec::bytes(&self.key)),
            ("owner", rec::bytes(&self.owner)),
            ("lamports", self.lamports.into()),
            ("data", rec::bytes(&self.data)),
            ("is_signer", self.is_signer.into()),
            ("is_writable", self.is_writable.into()),
            ("executable", self.executable.into()),
            ("rent_epoch", self.rent_epoch.into()),
        ])
    }
}

impl Input {
    /// `{"accounts": [account | {"duplicate_of": i}], "instruction_data", "program_id"}`.
    pub fn to_json(&self) -> Json {
        Json::obj([
            ("accounts", Json::arr(self.entries.iter(), |e| match e {
                Entry::Account(a) => a.to_json(),
                Entry::Duplicate(i) => Json::obj([("duplicate_of", Json::from(*i))]),
            })),
            ("instruction_data", rec::bytes(&self.instruction_data)),
            ("program_id", rec::bytes(&self.program_id)),
        ])
    }

    pub fn serialize(&self) -> Region {
        let mut bytes: Vec<u8> = Vec::new();
        let mut slots = Vec::new();
        bytes.extend_from_slice(&(self.entries.len() as u64).to_le_bytes());
        for (position, entry) in self.entries.iter().enumerate() {
            let offset = bytes.len();
            match entry {
                Entry::Duplicate(of) => {
                    assert!((*of as usize) < position, "duplicate {position} refers to a later account {of}");
                    bytes.push(*of);
                    bytes.extend_from_slice(&[0u8; 7]);
                    slots.push(Slot::Duplicate { offset });
                }
                Entry::Account(a) => {
                    bytes.extend_from_slice(&[NON_DUP_MARKER, a.is_signer as u8, a.is_writable as u8, a.executable as u8]);
                    bytes.extend_from_slice(&[0u8; 4]);
                    bytes.extend_from_slice(&a.key);
                    bytes.extend_from_slice(&a.owner);
                    bytes.extend_from_slice(&a.lamports.to_le_bytes());
                    bytes.extend_from_slice(&(a.data.len() as u64).to_le_bytes());
                    bytes.extend_from_slice(&a.data);
                    let pad = (BPF_ALIGN_OF_U128 - a.data.len() % BPF_ALIGN_OF_U128) % BPF_ALIGN_OF_U128;
                    bytes.resize(bytes.len() + MAX_PERMITTED_DATA_INCREASE + pad, 0);
                    bytes.extend_from_slice(&a.rent_epoch.to_le_bytes());
                    slots.push(Slot::Account { offset, original_len: a.data.len() });
                }
            }
        }
        let instruction_offset = bytes.len();
        bytes.extend_from_slice(&(self.instruction_data.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&self.instruction_data);
        bytes.extend_from_slice(&self.program_id);
        let len = bytes.len();
        let mut words = vec![0u128; len.div_ceil(16)];
        unsafe { core::ptr::copy_nonoverlapping(bytes.as_ptr(), words.as_mut_ptr() as *mut u8, len) };
        Region { words, len, slots, instruction_offset }
    }
}

#[derive(Clone, Copy, Debug)]
enum Slot {
    Account { offset: usize, original_len: usize },
    Duplicate { offset: usize },
}

/// A serialized input region in a 16-aligned buffer.
pub struct Region {
    words: Vec<u128>,
    len: usize,
    slots: Vec<Slot>,
    instruction_offset: usize,
}

impl Region {
    /// The region start, as the loader passes it to the entrypoint.
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.words.as_mut_ptr() as *mut u8
    }

    pub fn bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.words.as_ptr() as *const u8, self.len) }
    }

    /// Offset of the first byte of account `i` (its marker), the address that
    /// account-view `AccountView` and the C account structs point to.
    pub fn account_offset(&self, i: usize) -> usize {
        match self.slots[i] {
            Slot::Account { offset, .. } | Slot::Duplicate { offset } => offset,
        }
    }

    pub fn account_ptr(&mut self, i: usize) -> *mut u8 {
        let offset = self.account_offset(i);
        unsafe { self.as_mut_ptr().add(offset) }
    }

    fn u64_at(&self, at: usize) -> u64 {
        u64::from_le_bytes(self.bytes()[at..at + 8].try_into().unwrap())
    }

    /// The region now, read at the initial layout offsets, every byte:
    /// `{"accounts": [...], "count", "instruction_data", "program_id"}`. A
    /// non-duplicate account gives `marker` (the borrow state for
    /// account-view), `is_signer`, `is_writable`, `executable` (raw bytes),
    /// `padding` (the 4-byte field, unsigned), `key`, `owner`, `lamports`,
    /// `data_len`, `data` (the first `data_len` bytes, at most the original
    /// length plus 10 KiB), `rent_epoch` and `spare_nonzero_at` (the first
    /// nonzero byte offset after `data_len` within the original length plus
    /// 10 KiB, or `null`), `spare` (every byte from `data_len` to the original
    /// length plus 10 KiB) and `alignment_padding` (the bytes between that and
    /// the rent epoch). A duplicate gives `{"duplicate_of": byte, "padding"}`
    /// (its 7 padding bytes). `count` is the account-count word.
    pub fn read_back(&self) -> Json {
        let b = self.bytes();
        let accounts = Json::arr(self.slots.iter(), |slot| match *slot {
            Slot::Duplicate { offset } => Json::obj([
                ("duplicate_of", Json::from(b[offset])),
                ("padding", rec::bytes(&b[offset + 1..offset + 8])),
            ]),
            Slot::Account { offset, original_len } => {
                let data_len = self.u64_at(offset + 80) as usize;
                let capacity = original_len + MAX_PERMITTED_DATA_INCREASE;
                let start = offset + ACCOUNT_HEADER;
                let shown = data_len.min(capacity);
                let spare = (shown..capacity).find(|i| b[start + i] != 0);
                let pad = (BPF_ALIGN_OF_U128 - original_len % BPF_ALIGN_OF_U128) % BPF_ALIGN_OF_U128;
                let rent_at = start + original_len + MAX_PERMITTED_DATA_INCREASE + pad;
                Json::obj([
                    ("marker", Json::from(b[offset])),
                    ("is_signer", Json::from(b[offset + 1])),
                    ("is_writable", Json::from(b[offset + 2])),
                    ("executable", Json::from(b[offset + 3])),
                    ("padding", Json::from(u32::from_le_bytes(b[offset + 4..offset + 8].try_into().unwrap()))),
                    ("key", rec::bytes(&b[offset + 8..offset + 40])),
                    ("owner", rec::bytes(&b[offset + 40..offset + 72])),
                    ("lamports", Json::from(self.u64_at(offset + 72))),
                    ("data_len", Json::from(data_len as u64)),
                    ("data", rec::bytes(&b[start..start + shown])),
                    ("rent_epoch", Json::from(self.u64_at(rent_at))),
                    ("spare_nonzero_at", spare.map_or(Json::Null, Json::from)),
                    ("spare", rec::bytes(&b[start + shown..start + capacity])),
                    ("alignment_padding", rec::bytes(&b[start + capacity..rent_at])),
                ])
            }
        });
        let at = self.instruction_offset;
        let n = self.u64_at(at) as usize;
        Json::obj([
            ("accounts", accounts),
            ("count", Json::from(self.u64_at(0))),
            ("instruction_data", rec::bytes(&b[at + 8..at + 8 + n])),
            ("program_id", rec::bytes(&b[at + 8 + n..at + 8 + n + 32])),
        ])
    }
}
