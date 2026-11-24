//! Reusable calls and observations for versioned raw declaration drivers.
//! The actual published crate supplies every declaration; `provider` supplies
//! only the native test environment. No invocation implementation is traversed.

pub mod provider;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use provider::Script;

pub type Copy = unsafe fn(*mut u8, *const u8, u64);
pub type Set = unsafe fn(*mut u8, u8, u64);
pub type Create = unsafe fn(*const u8, u64, *const u8, *mut u8) -> u64;
pub type Find = unsafe fn(*const u8, u64, *const u8, *mut u8, *mut u8) -> u64;
pub type Hash = unsafe fn(*const u8, u64, *mut u8) -> u64;
pub type Typed = unsafe fn(*mut u8) -> u64;
pub type Stack = unsafe fn() -> u64;
pub type SetReturn = unsafe fn(*const u8, u64);
pub type GetReturn = unsafe fn(*mut u8, u64, *mut u8) -> u64;
#[derive(Default)]
pub struct Calls {
    pub copy: Option<Copy>, pub set: Option<Set>, pub create: Option<Create>, pub find: Option<Find>,
    pub hash: Option<Hash>, pub clock: Option<Typed>, pub rent: Option<Typed>, pub epoch: Option<Typed>,
    pub stack_wrapper: bool, pub setter_slice: bool,
    pub stack: Option<Stack>, pub set_return: Option<SetReturn>, pub get_return: Option<GetReturn>,
}
fn initial(width: usize) -> Vec<u8> {
    let mut result = vec![0xa5; width + 16];
    result[..8].fill(0x3c); result[width + 8..].fill(0xc3); result
}
fn body(buffer: &[u8]) -> &[u8] { &buffer[8..buffer.len() - 8] }
fn guards(buffer: &[u8]) -> Vec<u8> { [buffer[..8].to_vec(), buffer[buffer.len() - 8..].to_vec()].concat() }
#[derive(Clone)]
struct Case {
    name: &'static str, op: &'static str, input: Vec<u8>, seeds: Vec<Vec<u8>>, count: usize,
    byte: u8, capacity: usize, overlap: bool, input_region: bool, script: Script,
}
impl Case {
    fn new(name: &'static str, op: &'static str) -> Self {
        Self { name, op, input: vec![0, 1, 255, 128, 3], seeds: vec![vec![1, 2], vec![], vec![1, 2]],
            count: 5, byte: 255, capacity: 5, overlap: false, input_region: false, script: Script::default() }
    }
    fn width(&self) -> usize {
        match self.op { "copy" | "set" => self.count, "create" | "find" | "sha256" => 32,
            "clock" | "epoch" => 40, "rent" => 24, "get-return" => self.capacity, _ => 0 }
    }
    fn args(&self, buffer: &[u8], pid: &[u8]) -> Json {
        let mut program = [0; 32]; program[0] = 7;
        Json::obj([
            ("input", rec::bytes(&self.input)), ("seeds", Json::arr(&self.seeds, |s| rec::bytes(s))),
            ("program", rec::bytes(&program)), ("count", self.count.into()),
            ("byte", self.byte.into()), ("capacity", self.capacity.into()),
            ("on_curve", self.script.on_curve.into()), ("overlap", self.overlap.into()),
            ("input_region", self.input_region.into()),
            ("output", rec::bytes(body(buffer))), ("guards", rec::bytes(&guards(buffer))),
            ("program_output", rec::bytes(body(pid))), ("program_guards", rec::bytes(&guards(pid))),
            ("bump", 94u8.into()),
        ])
    }
}
#[repr(C)]
struct Slice { pointer: *const u8, length: u64 }
fn invoke(case: &Case, calls: &Calls, mut buffer: Vec<u8>, mut pid: Vec<u8>) -> Json {
    let mut bump = 94u8;
    let destination = unsafe { buffer.as_mut_ptr().add(8) };
    let null = core::ptr::null_mut();
    let program = { let mut p = [0u8; 32]; p[0] = 7; p };
    // A rejected seed has no valid data pointer, so premature reads cause a harness failure.
    let descriptors: Vec<Slice> = case.seeds.iter().map(|s| Slice {
        pointer: if s.len() > 32 && case.op != "sha256" { core::ptr::null() } else { s.as_ptr() },
        length: s.len() as u64,
    }).collect();
    let vals = if descriptors.is_empty() { core::ptr::null() } else { descriptors.as_ptr().cast() };
    let status = unsafe { match case.op {
        "copy" => {
            let src = if case.count == 0 { null } else if case.overlap { destination } else { case.input.as_ptr() };
            (calls.copy.unwrap())(if case.count == 0 { null } else { destination }, src, case.count as u64); 0
        }
        "set" => { (calls.set.unwrap())(if case.count == 0 { null } else { destination }, case.byte, case.count as u64); 0 }
        "create" => (calls.create.unwrap())(vals, descriptors.len() as u64, program.as_ptr(),
            if case.script.on_curve { null } else { destination }),
        "find" => (calls.find.unwrap())(vals, descriptors.len() as u64, program.as_ptr(),
            if case.script.on_curve { null } else { destination },
            if case.overlap { destination } else if case.script.on_curve { null } else { &mut bump }),
        "sha256" => (calls.hash.unwrap())(vals, descriptors.len() as u64, destination),
        "clock" => (calls.clock.unwrap())(destination), "rent" => (calls.rent.unwrap())(destination),
        "epoch" => (calls.epoch.unwrap())(destination), "stack" => (calls.stack.unwrap())(),
        "set-return" => { (calls.set_return.unwrap())(
            if !calls.setter_slice && (case.input.is_empty() || case.input.len() > 1024) { core::ptr::null() } else { case.input.as_ptr() },
            case.input.len() as u64); 0 },
        "get-return" => {
            let copied = case.capacity.min(case.script.return_data.len());
            (calls.get_return.unwrap())(if copied == 0 { null } else { destination }, case.capacity as u64,
                if copied == 0 { null } else if case.overlap { destination } else { pid.as_mut_ptr().add(8) })
        }
        _ => unreachable!(),
    }};
    // In mapped cases this same live allocation is the fixture serialized
    // input region. Observe its actual bytes after the external call; do not
    // reconstruct them from the output requested by the provider.
    let after_state = if case.input_region { provider::state_with_input(&buffer) }
        else { provider::state() };
    Json::obj([("exit", "returned".into()), ("result", Json::obj([
        ("status", status.into()), ("output", rec::bytes(body(&buffer))),
        ("guards", rec::bytes(&guards(&buffer))), ("program_output", rec::bytes(body(&pid))),
        ("program_guards", rec::bytes(&guards(&pid))), ("bump", bump.into()),
    ])), ("state", after_state), ("trace", provider::trace())])
}
fn symbol(op: &str) -> &str {
    match op { "copy" => "sol_memcpy_", "set" => "sol_memset_", "create" => "sol_create_program_address",
        "find" => "sol_try_find_program_address", "sha256" => "sol_sha256", "clock" => "sol_get_clock_sysvar",
        "rent" => "sol_get_rent_sysvar", "epoch" => "sol_get_epoch_schedule_sysvar", "stack" => "sol_get_stack_height",
        "set-return" => "sol_set_return_data", "get-return" => "sol_get_return_data", _ => unreachable!() }
}
pub fn record(name: &'static str, package: &'static str, version: &'static str,
              prefix: &'static str, calls: Calls) {
    let mut corpus = Corpus::new(name, &[(package, version)]);
    let mut cases = vec![];
    if calls.copy.is_some() {
        cases.push(Case::new("copy/nonempty", "copy"));
        let mut c = Case::new("copy/zero-null", "copy"); c.count = 0; c.input.clear(); cases.push(c);
        let mut c = Case::new("copy/overlap", "copy"); c.overlap = true; cases.push(c);
    }
    if calls.set.is_some() {
        cases.push(Case::new("set/high-byte", "set"));
        let mut c = Case::new("set/zero-null", "set"); c.count = 0; cases.push(c);
        let mut c = Case::new("set/zero-byte", "set"); c.byte = 0; cases.push(c);
    }
    for op in ["create", "find"] {
        if (op == "create" && calls.create.is_none()) || (op == "find" && calls.find.is_none()) { continue; }
        for (suffix, mode) in [("success", 0), ("on-curve-null", 1), ("empty-seeds", 2),
            ("count-17", 3), ("seed-33", 4), ("seed-32", 5)] {
            let name = Box::leak(format!("{op}/{suffix}").into_boxed_str());
            let mut c = Case::new(name, op);
            match mode { 1 => c.script.on_curve = true, 2 => c.seeds.clear(),
                3 => c.seeds = vec![vec![]; 17], 4 => c.seeds = vec![vec![1; 33]],
                5 => c.seeds = vec![vec![1; 32]], _ => {} }
            cases.push(c);
        }
        if op == "find" {
            let mut c = Case::new("find/overlap-success", op); c.overlap = true; cases.push(c);
            let mut c = Case::new("find/overlap-failure", op); c.overlap = true; c.script.on_curve = true; cases.push(c);
            let mut c = Case::new("find/count-16", op); c.seeds = vec![vec![]; 16]; cases.push(c);
        }
    }
    if calls.hash.is_some() {
        cases.push(Case::new("sha256/segmented", "sha256"));
        let mut c = Case::new("sha256/empty", "sha256"); c.seeds.clear(); cases.push(c);
    }
    for (op, available) in [("clock", calls.clock.is_some()), ("rent", calls.rent.is_some()), ("epoch", calls.epoch.is_some())] {
        if available { cases.push(Case::new(op, op)); }
    }
    if calls.stack.is_some() {
        for height in [0, 1, 5] {
            let mut c = Case::new(Box::leak(format!("stack/{height}").into_boxed_str()), "stack");
            c.script.height = height; cases.push(c);
        }
    }
    if calls.set_return.is_some() {
        for length in [0, 1, 1024, 1025] {
            let mut c = Case::new(Box::leak(format!("set-return/{length}").into_boxed_str()), "set-return");
            c.input = vec![0x2a; length]; cases.push(c);
        }
    }
    if calls.get_return.is_some() {
        for capacity in [0, 1, 2, 5] {
            let mut c = Case::new(Box::leak(format!("get-return/{capacity}").into_boxed_str()), "get-return");
            c.capacity = capacity; cases.push(c);
        }
        let mut c = Case::new("get-return/empty", "get-return"); c.script.return_data.clear(); cases.push(c);
        let mut c = Case::new("get-return/overlap", "get-return"); c.overlap = true; cases.push(c);
    }
    let mapped: Vec<Case> = cases.iter().filter(|c| matches!(c.name,
        "copy/nonempty" | "copy/zero-null" | "set/high-byte" | "set/zero-null" |
        "create/success" | "find/success" | "find/count-16" |
        "get-return/0" | "get-return/5"
    )).map(|c| {
        let mut c = c.clone();
        c.name = Box::leak(format!("input-region/{}", c.name).into_boxed_str());
        c.input_region = true;
        c
    }).collect();
    cases.extend(mapped);
    for c in cases {
        let buffer = initial(c.width()); let pid = initial(32);
        let before_state = if c.input_region { c.script.state_with_input(&buffer) }
            else { c.script.state() };
        let args = c.args(&buffer, &pid);
        let outcome = provider::case(&c.script, || invoke(&c, &calls, buffer, pid));
        assert!(!outcome.to_text().contains("shim-fault"), "harness fault in {}", c.name);
        let leaf = if calls.setter_slice && c.op == "set-return" { "set_return_data" }
            else if calls.stack_wrapper && c.op == "stack" { "get_stack_height" } else { symbol(c.op) };
        let function = Box::leak(format!("{prefix}::{leaf}").into_boxed_str());
        corpus.push(Record { id: c.name.into(), function, generics: vec![], layout: None,
            state: before_state, args, outcome, observed: None });
    }
    corpus.write(&rec::out_dir()).expect("write raw runtime corpus");
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn return_data_is_shared_between_calls() {
        let outcome = provider::case(&Script::default(), || {
            unsafe { provider::sol_set_return_data([4u8, 5, 6].as_ptr(), 3); }
            let mut output = [0xa5; 5]; let mut program = [0xa5; 32];
            let length = unsafe { provider::sol_get_return_data(output.as_mut_ptr(), 2, program.as_mut_ptr()) };
            assert_eq!(length, 3); assert_eq!(output, [4, 5, 0xa5, 0xa5, 0xa5]);
            assert_eq!(program[31], 7); assert!(program[..31].iter().all(|b| *b == 0));
            Json::Bool(true)
        });
        assert_eq!(outcome.to_text(), "true");
    }
    #[test]
    fn zero_memory_calls_accept_null_pointers() {
        let outcome = provider::case(&Script::default(), || {
            unsafe { provider::sol_memcpy_(core::ptr::null_mut(), core::ptr::null(), 0);
                provider::sol_memset_(core::ptr::null_mut(), 255, 0); }
            Json::Bool(true)
        });
        assert_eq!(outcome.to_text(), "true");
    }
}
