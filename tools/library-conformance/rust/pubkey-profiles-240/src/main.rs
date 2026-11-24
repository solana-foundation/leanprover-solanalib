use conformance_recorder::{self as rec, Corpus};
use solana_pubkey::Pubkey as Key;
const KEY_PATH: &str = "solana_pubkey::Pubkey";
const ZEROED: bool = true;
#[path = "../../address-profiles-common/operations.rs"]
mod operations;
#[path = "../../address-profiles-common/io.rs"]
mod io;

fn main() {
    rec::init();
    let mut c = Corpus::new("pubkey_profiles_240", &[("solana-pubkey", "2.4.0"), ("borsh", "0.10.4"), ("spl-associated-token-account-client", "2.0.0")]);
    operations::record_values(&mut c, &["new_from_array", "from", "to_bytes", "as_ref", "default", "eq", "clone", "cmp"]);
    operations::record_create(&mut c);
    operations::record_find(&mut c);
    operations::record_seed(&mut c);
    io::record_serialize(&mut c);
    io::record_reader(&mut c);
    record_eof_payloads(&mut c);
    operations::record_derived(&mut c, "spl_associated_token_account_client::address::get_associated_token_address_with_program_id", |wallet, mint, token| spl_associated_token_account_client::address::get_associated_token_address_with_program_id(wallet, mint, token));
    c.write(&rec::out_dir()).expect("write corpus");
}

// Keep the two owned-error probes in this existing pinned driver. The shared
// address drivers retain their prior source and observation bytes.
#[derive(Debug)]
struct EofPayload {
    drops: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    unwind: bool,
}

impl std::fmt::Display for EofPayload {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("owned EOF payload")
    }
}

impl std::error::Error for EofPayload {}

impl Drop for EofPayload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if self.unwind {
            panic!("EOF payload drop");
        }
    }
}

struct EofReader {
    input: Vec<u8>,
    position: usize,
    exact_calls: usize,
    read_calls: usize,
    initial: Vec<u8>,
    mode: &'static str,
    drops: std::sync::Arc<std::sync::atomic::AtomicUsize>,
}

impl EofReader {
    fn state(&self) -> rec::Json {
        rec::Json::obj([
            ("input", rec::bytes(&self.input)),
            ("position", self.position.into()),
            ("exact_calls", self.exact_calls.into()),
            ("read_calls", self.read_calls.into()),
            ("initial", rec::bytes(&self.initial)),
            ("mode", self.mode.into()),
            ("drops", self.drops.load(std::sync::atomic::Ordering::SeqCst).into()),
        ])
    }
}

impl std::io::Read for EofReader {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        self.read_calls += 1;
        Err(std::io::Error::other("unexpected default read loop"))
    }

    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        self.exact_calls += 1;
        self.initial = buf.to_vec();
        buf[..7].copy_from_slice(&self.input[self.position..self.position + 7]);
        self.position += 7;
        Err(std::io::Error::new(
            std::io::ErrorKind::UnexpectedEof,
            EofPayload {
                drops: self.drops.clone(),
                unwind: self.mode == "eof_drop_unwind",
            },
        ))
    }
}

fn record_eof_payloads(c: &mut Corpus) {
    use borsh_selected::BorshDeserialize;
    for mode in ["eof_drop", "eof_drop_unwind"] {
        let mut reader = EofReader {
            input: operations::pattern(40, 23),
            position: 1,
            exact_calls: 0,
            read_calls: 0,
            initial: vec![],
            mode,
            drops: std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0)),
        };
        let before = reader.state();
        let result = rec::catch(|| <Key as BorshDeserialize>::deserialize_reader(&mut reader));
        let outcome = match result {
            Ok(r) => rec::returned(rec::io_result(&r, |v| rec::bytes(&v.to_bytes())), reader.state()),
            Err(reason) => rec::unwound(reason, reader.state()),
        };
        operations::push(
            c,
            format!("deserialize_reader/{mode}"),
            operations::name("deserialize_reader", Some("borsh::de::BorshDeserialize")),
            before,
            rec::Json::Null,
            outcome,
        );
    }
}
