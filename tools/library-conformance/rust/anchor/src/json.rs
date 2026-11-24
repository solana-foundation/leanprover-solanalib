//! A reader for the JSON that the child process for a case sends back (`shim::case` returns it
//! as raw text), so that one child can report its arguments and the state
//! before the call along with the outcome.

use conformance_recorder::Json;

pub fn parse(text: &str) -> Json {
    let mut p = Parser { s: text.as_bytes(), i: 0 };
    let v = p.value();
    p.ws();
    assert_eq!(p.i, p.s.len(), "trailing JSON text");
    v
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl Parser<'_> {
    fn ws(&mut self) {
        while self.i < self.s.len() && (self.s[self.i] as char).is_ascii_whitespace() {
            self.i += 1;
        }
    }

    fn eat(&mut self, c: u8) {
        self.ws();
        assert_eq!(self.s[self.i], c, "JSON: expected {}", c as char);
        self.i += 1;
    }

    fn value(&mut self) -> Json {
        self.ws();
        match self.s[self.i] {
            b'{' => {
                self.i += 1;
                let mut fields = vec![];
                self.ws();
                if self.s[self.i] == b'}' {
                    self.i += 1;
                    return Json::Obj(fields);
                }
                loop {
                    self.ws();
                    let k = self.string();
                    self.eat(b':');
                    let v = self.value();
                    fields.push((k, v));
                    self.ws();
                    if self.s[self.i] == b',' {
                        self.i += 1;
                    } else {
                        self.eat(b'}');
                        return Json::Obj(fields);
                    }
                }
            }
            b'[' => {
                self.i += 1;
                let mut items = vec![];
                self.ws();
                if self.s[self.i] == b']' {
                    self.i += 1;
                    return Json::Arr(items);
                }
                loop {
                    items.push(self.value());
                    self.ws();
                    if self.s[self.i] == b',' {
                        self.i += 1;
                    } else {
                        self.eat(b']');
                        return Json::Arr(items);
                    }
                }
            }
            b'"' => Json::Str(self.string()),
            b't' => { self.i += 4; Json::Bool(true) }
            b'f' => { self.i += 5; Json::Bool(false) }
            b'n' => { self.i += 4; Json::Null }
            _ => {
                let start = self.i;
                while self.i < self.s.len() && (self.s[self.i] == b'-' || self.s[self.i].is_ascii_digit()) {
                    self.i += 1;
                }
                Json::Int(std::str::from_utf8(&self.s[start..self.i]).unwrap().parse().expect("JSON integer"))
            }
        }
    }

    fn string(&mut self) -> String {
        self.eat(b'"');
        let mut out = String::new();
        loop {
            let c = self.s[self.i];
            self.i += 1;
            match c {
                b'"' => return out,
                b'\\' => {
                    let e = self.s[self.i];
                    self.i += 1;
                    match e {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let h = std::str::from_utf8(&self.s[self.i..self.i + 4]).unwrap();
                            self.i += 4;
                            out.push(char::from_u32(u32::from_str_radix(h, 16).unwrap()).unwrap());
                        }
                        _ => panic!("JSON escape"),
                    }
                }
                _ => {
                    // Copy a UTF-8 sequence.
                    let start = self.i - 1;
                    let len = if c < 0x80 { 1 } else if c >> 5 == 0b110 { 2 } else if c >> 4 == 0b1110 { 3 } else { 4 };
                    out.push_str(std::str::from_utf8(&self.s[start..start + len]).unwrap());
                    self.i = start + len;
                }
            }
        }
    }
}
