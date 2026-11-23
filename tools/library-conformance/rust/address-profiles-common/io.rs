//! Override-aware Borsh callbacks; state is observed after success or unwind.
use borsh_selected::{BorshDeserialize, BorshSerialize};
use conformance_recorder::{self as rec, Corpus, Json};
use crate::{Key, operations::{key, name, pattern, push}};
use std::io::{self, Read, Write};

struct Reader {
    input: Vec<u8>, position: usize, exact_calls: usize, read_calls: usize,
    initial: Vec<u8>, mode: &'static str,
}
impl Reader {
    fn state(&self) -> Json {
        Json::obj([("input", rec::bytes(&self.input)), ("position", self.position.into()),
                   ("exact_calls", self.exact_calls.into()), ("read_calls", self.read_calls.into()),
                   ("initial", rec::bytes(&self.initial)), ("mode", self.mode.into())])
    }
}
impl Read for Reader {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        self.read_calls += 1;
        Err(io::Error::other("unexpected default read loop"))
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
        self.exact_calls += 1;
        self.initial = buf.to_vec();
        let count = match self.mode { "ok" => 32, "short_ok" => 5, "eof" => 7, "other" => 3, "unwind" => 4, _ => unreachable!() };
        buf[..count].copy_from_slice(&self.input[self.position..self.position + count]);
        self.position += count;
        match self.mode {
            "ok" | "short_ok" => Ok(()),
            "eof" => Err(io::Error::new(io::ErrorKind::UnexpectedEof, "reader stopped")),
            "other" => Err(io::Error::other("chosen read error")),
            "unwind" => panic!("chosen read unwind"),
            _ => unreachable!(),
        }
    }
}

struct Writer { written: Vec<u8>, calls: Vec<Vec<u8>>, write_calls: usize, mode: &'static str }
impl Writer {
    fn state(&self) -> Json {
        Json::obj([("written", rec::bytes(&self.written)), ("calls", Json::arr(self.calls.iter(), |b| rec::bytes(b))),
                   ("write_calls", self.write_calls.into()), ("mode", self.mode.into())])
    }
}
impl Write for Writer {
    fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
        self.write_calls += 1;
        Err(io::Error::other("unexpected default write loop"))
    }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.calls.push(buf.to_vec());
        let count = if self.mode == "ok" { buf.len() } else { 3 };
        self.written.extend_from_slice(&buf[..count]);
        match self.mode {
            "ok" => Ok(()),
            "error" => Err(io::Error::new(io::ErrorKind::WriteZero, "chosen partial write")),
            "unwind" => panic!("chosen write unwind"),
            _ => unreachable!(),
        }
    }
}

pub fn record_serialize(c: &mut Corpus) {
    for mode in ["ok", "error", "unwind"] {
        let value = key(17);
        let mut writer = Writer { written: vec![9], calls: vec![], write_calls: 0, mode };
        let before = writer.state();
        let result = rec::catch(|| <Key as BorshSerialize>::serialize(&value, &mut writer));
        let outcome = match result { Ok(r) => rec::returned(rec::io_result(&r, |_| Json::Null), writer.state()), Err(reason) => rec::unwound(reason, writer.state()) };
        push(c, format!("serialize/{mode}"), name("serialize", Some("borsh::ser::BorshSerialize")), before,
             Json::obj([("self", rec::bytes(&value.to_bytes()))]), outcome);
    }
}

#[cfg(not(feature = "legacy_io"))]
pub fn record_reader(c: &mut Corpus) {
    for mode in ["ok", "short_ok", "eof", "other", "unwind"] {
        let mut reader = Reader { input: pattern(40, 23), position: 1, exact_calls: 0, read_calls: 0, initial: vec![], mode };
        let before = reader.state();
        let result = rec::catch(|| <Key as BorshDeserialize>::deserialize_reader(&mut reader));
        let outcome = match result { Ok(r) => rec::returned(rec::io_result(&r, |v| rec::bytes(&v.to_bytes())), reader.state()), Err(reason) => rec::unwound(reason, reader.state()) };
        push(c, format!("deserialize_reader/{mode}"), name("deserialize_reader", Some("borsh::de::BorshDeserialize")), before, Json::Null, outcome);
    }
}

#[cfg(feature = "legacy_io")]
pub fn record_reader(c: &mut Corpus) {
    for n in [0, 1, 31, 32, 40] {
        let input = pattern(n, 23);
        let mut slice = input.as_slice();
        let result = <Key as BorshDeserialize>::deserialize(&mut slice);
        // The cursor is an observable output of this older trait method.
        let value = Json::arr([rec::io_result(&result, |v| rec::bytes(&v.to_bytes())), rec::bytes(slice)], |x| x);
        push(c, format!("deserialize/{n}"), name("deserialize", Some("borsh::de::BorshDeserialize")), Json::Null,
             rec::bytes(&input), rec::returned(value, Json::Null));
    }
}
