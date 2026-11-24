//! The program input region, built by the suite `conformance-accounts`
//! (the loader ABI v1 aligned serialization), and the raw reads of it that
//! the projection for this family needs.
//!
//! The driver takes the region base pointer once, hands it to the client
//! own deserializers and afterwards reads the region only through that raw
//! pointer, never through a Rust reference to the buffer, so the libraries'
//! raw pointers and references into it stay valid. The projection needs the
//! whole allocated data area (entry length plus the 10 KiB realloc reserve)
//! and the signed `resize_delta`, which `Region::read_back` does not give.

pub use conformance_accounts::{Account, Entry, Input, MAX_PERMITTED_DATA_INCREASE};

/// `size_of::<RuntimeAccount>()` of solana-account-view 1.0.0, the header before the data.
pub const HEADER: usize = conformance_accounts::ACCOUNT_HEADER;

/// One non-duplicate account (a cell).
#[derive(Clone, Copy, Debug)]
pub struct Cell {
    /// Offset of its first byte (the duplicate marker, account-view borrow state).
    pub header: usize,
    /// Its data length as serialized (the entry length).
    pub entry_len: usize,
}

pub struct Region {
    /// Owns the buffer; never accessed again after `base` is taken.
    _region: conformance_accounts::Region,
    base: *mut u8,
    len: usize,
    pub cells: Vec<Cell>,
}

pub fn key(seed: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    for (i, b) in k.iter_mut().enumerate() {
        *b = seed.wrapping_mul(31).wrapping_add(i as u8);
    }
    k
}

/// Nonzero bytes, so that hidden and zeroed data are visible.
pub fn pattern(len: usize, start: u8) -> Vec<u8> {
    (0..len).map(|i| start.wrapping_add(i as u8) | 1).collect()
}

pub fn account(seed: u8, lamports: u64, len: usize) -> Account {
    Account {
        key: key(seed),
        owner: key(seed.wrapping_add(100)),
        lamports,
        data: pattern(len, seed),
        is_signer: false,
        is_writable: true,
        executable: false,
        rent_epoch: u64::MAX,
    }
}

pub fn input(entries: Vec<Entry>) -> Input {
    Input { entries, instruction_data: vec![7, 1, 2], program_id: key(250) }
}

impl Region {
    pub fn new(input: &Input) -> Region {
        let mut region = input.serialize();
        let len = region.bytes().len();
        let base = region.as_mut_ptr();
        let cells = input
            .entries
            .iter()
            .enumerate()
            .filter_map(|(i, e)| match e {
                Entry::Account(a) => Some(Cell { header: region.account_offset(i), entry_len: a.data.len() }),
                Entry::Duplicate(_) => None,
            })
            .collect();
        Region { _region: region, base, len, cells }
    }

    pub fn base(&self) -> *mut u8 {
        self.base
    }

    /// Copy `len` bytes at `offset` out of the region, through the base pointer.
    pub fn read(&self, offset: usize, len: usize) -> Vec<u8> {
        assert!(offset + len <= self.len);
        let mut out = vec![0u8; len];
        // SAFETY: in bounds; a raw copy, no reference to the buffer is formed.
        unsafe { std::ptr::copy_nonoverlapping(self.base.add(offset), out.as_mut_ptr(), len) };
        out
    }

    /// Overwrite bytes of the region (forged headers only).
    pub fn write(&self, offset: usize, bytes: &[u8]) {
        assert!(offset + bytes.len() <= self.len);
        // SAFETY: in bounds; a raw copy.
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.base.add(offset), bytes.len()) };
    }

    /// The region bytes outside the given (offset, length) ranges, in order:
    /// the frame of a projection, which a call must leave unchanged.
    pub fn frame(&self, projected: &[(usize, usize)]) -> Vec<u8> {
        let all = self.read(0, self.len);
        all.iter()
            .enumerate()
            .filter(|(i, _)| !projected.iter().any(|(o, l)| *i >= *o && *i < o + l))
            .map(|(_, b)| *b)
            .collect()
    }

    /// The cell whose first byte is at `address`, if any.
    pub fn cell_at_header(&self, address: usize) -> Option<usize> {
        self.cells.iter().position(|c| self.base as usize + c.header == address)
    }

    /// Address of the first data byte of a cell.
    pub fn data_start(&self, cell: usize) -> usize {
        self.base as usize + self.cells[cell].header + HEADER
    }

    /// The allocated data area of a cell: entry length plus the realloc reserve.
    pub fn capacity(&self, cell: usize) -> usize {
        self.cells[cell].entry_len + MAX_PERMITTED_DATA_INCREASE
    }

    /// The cell whose allocated data area contains `address` (one past its end
    /// included, for empty ranges), and the offset of `address` in it.
    pub fn locate_data(&self, address: usize) -> Option<(usize, usize)> {
        (0..self.cells.len()).find_map(|k| {
            let start = self.data_start(k);
            (address >= start && address <= start + self.capacity(k)).then(|| (k, address - start))
        })
    }

    /// The cell whose header contains `address`, and the offset of `address` in it.
    pub fn locate_header(&self, address: usize) -> Option<(usize, usize)> {
        (0..self.cells.len()).find_map(|k| {
            let start = self.base as usize + self.cells[k].header;
            (address >= start && address < start + HEADER).then(|| (k, address - start))
        })
    }
}
