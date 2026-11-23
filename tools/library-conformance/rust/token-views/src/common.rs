//! Worlds of accounts in a loader input region, pointer resolution and record helpers.

use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Json, Record};
use conformance_shim::{self as shim, Reply, Script};
use solana_account_view::{AccountView, RuntimeAccount};

/// Offsets inside a non-duplicate account of the region (the `RuntimeAccount` header).
pub const ADDRESS_AT: usize = 8;
pub const OWNER_AT: usize = 40;
pub const LAMPORTS_AT: usize = 72;
pub const DATA_AT: usize = 88;

/// A loader input region and one `AccountView` per account (account `j` is the
/// model handle `j`). The region buffer does not move with the struct.
pub struct World {
    pub region: Region,
    pub views: Vec<AccountView>,
    bases: Vec<usize>,
    lens: Vec<usize>,
}

impl World {
    pub fn new(accounts: Vec<Account>) -> World {
        let lens = accounts.iter().map(|a| a.data.len()).collect::<Vec<_>>();
        let input = Input {
            entries: accounts.into_iter().map(Entry::Account).collect(),
            // Nonzero frame values, so that no copy of them can pass for the model constants.
            instruction_data: vec![0xd0, 0xd1],
            program_id: key(0xee),
        };
        let mut region = input.serialize();
        let n = lens.len();
        let bases = (0..n).map(|i| region.account_ptr(i) as usize).collect::<Vec<_>>();
        let views = bases
            .iter()
            .map(|&b| unsafe { AccountView::new_unchecked(b as *mut RuntimeAccount) })
            .collect();
        World { region, views, bases, lens }
    }

    /// Overwrite the raw header bytes of account `j` in the region: `is_signer`,
    /// `is_writable`, `executable` and the first padding byte (the loader writes
    /// 0/1 flags and zero padding; account-view keeps them as raw bytes).
    pub fn set_raw_header(&mut self, j: usize, header: [u8; 4]) {
        let base = self.bases[j] as *mut u8;
        unsafe {
            for (k, b) in header.iter().enumerate() {
                *base.add(1 + k) = *b;
            }
        }
    }

    pub fn read_back(&self) -> Json {
        self.region.read_back()
    }

    /// The account whose header field at `field` (one of the `*_AT` offsets) is at `p`.
    pub fn field_of(&self, p: usize, field: usize) -> Option<usize> {
        self.bases.iter().position(|&b| b + field == p)
    }

    /// The account and data offset of a pointer into the data area of an account
    /// (within its original length plus the realloc area).
    pub fn data_offset(&self, p: usize) -> Option<(usize, usize)> {
        self.bases.iter().zip(&self.lens).position(|(&b, &n)| p >= b + DATA_AT && p <= b + DATA_AT + n + 10 * 1024)
            .map(|j| (j, p - (self.bases[j] + DATA_AT)))
    }

    /// The account a `&AccountView` points to.
    pub fn view_index(&self, v: &AccountView) -> usize {
        let p = v as *const AccountView;
        // An AccountView is one pointer to its RuntimeAccount.
        let raw = unsafe { *(p as *const usize) };
        self.bases.iter().position(|&b| b == raw).expect("AccountView of this world")
    }
}

/// A distinct, low-entropy address: the seed byte, then zeros up to a last byte 1
/// (both ends of the 32 bytes are observed).
pub fn key(seed: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = seed;
    k[31] = 1;
    k
}

/// Bytes `0, 1, 2, ...` (mod 256) shifted by `seed`: distinct contents for a few accounts.
pub fn bytes(seed: u64, n: usize) -> Vec<u8> {
    (0..n).map(|i| (i as u64).wrapping_add(seed) as u8).collect()
}

pub fn account(seed: u8, owner: [u8; 32], data: Vec<u8>) -> Account {
    Account {
        key: key(seed),
        owner,
        lamports: 1000 + seed as u64,
        data,
        is_signer: false,
        is_writable: true,
        executable: false,
        // Nonzero, so the zero rent epoch set by the CPI initializer is told apart from a copy.
        rent_epoch: 500 + seed as u64,
    }
}

pub fn program_error(e: &solana_program_error::ProgramError) -> Json {
    Json::from(format!("{e:?}"))
}

pub fn result_json<T>(r: &Result<T, solana_program_error::ProgramError>, f: impl Fn(&T) -> Json) -> Json {
    match r {
        Ok(v) => rec::ok(f(v)),
        Err(e) => rec::err(program_error(e)),
    }
}

/// A state: the region read back, the syscall state and extra fields.
pub fn state(world: &World, syscalls: Json, extra: Vec<(&str, Json)>) -> Json {
    let mut fields = vec![("region".to_string(), world.read_back()), ("syscalls".to_string(), syscalls)];
    fields.extend(extra.into_iter().map(|(k, v)| (k.to_string(), v)));
    Json::Obj(fields)
}

pub fn no_script() -> Script {
    Script::new(vec![])
}

pub fn invoke_reply(ret: u64) -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", ret)])
}

pub fn invoke_terminates() -> Script {
    Script::new(vec![Reply::new("sol_invoke_signed_c", 0).terminate("callee failed")])
}

/// The state after the call, inside the shim child: region, syscalls, extras.
pub fn after(world: &World, extra: Vec<(&str, Json)>) -> Json {
    state(world, shim::state(), extra)
}

pub fn record(id: String, function: &'static str, generics: Vec<(&'static str, String)>, state: Json, args: Json,
              outcome: Json) -> Record {
    Record { id, function, generics, layout: None, state, args, outcome, observed: None }
}
