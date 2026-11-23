//! Capture the actual private extern calls made by the published public Log API.
//! No copied extern declaration and no replacement pinocchio-log crate is used.
use conformance_raw_runtime_common::provider;
use conformance_recorder::Json;
use pinocchio_log::logger::{Argument, Log};
use core::mem::MaybeUninit;

fn main() {
    let result = provider::case(&provider::Script::default(), || {
        provider::capture_memory_calls();
        let mut storage = [MaybeUninit::new(0xa5); 96];
        let buffer = &mut storage[8..88];
        assert_eq!("hello".write(buffer), 5);
        assert_eq!(123u64.write(buffer), 3);
        assert_eq!(12u64.write_with_args(buffer, &[Argument::Precision(6)]), 8);
        assert_eq!(1u64.write_with_args(buffer, &[Argument::Precision(3)]), 5);
        provider::write_memory_corpus();
        Json::Bool(true)
    });
    assert_eq!(result.to_text(), "true");
}
