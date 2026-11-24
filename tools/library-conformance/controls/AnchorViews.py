"""Corrupt actual wrapper observations, reference identities, and callback effects.

These controls run the same executable source-relation graphs as the retained
native profiles. Missing source loans are covered by AdmissionControls.lean.
"""

from common import on_record

OLD = "anchor_views_0_27_0"
NEW = "anchor_views_1_0_2"
DEBUG = "anchor_views_1_0_2_debug"


def result_field(name, value):
    def change(record): record["outcome"]["result"][name] = value
    return change


def post_field(name, value):
    def change(record): record["outcome"]["state"][name] = value
    return change


def result(value):
    def change(record): record["outcome"]["result"] = value
    return change


def reason(value):
    def change(record): record["outcome"]["reason"] = value
    return change


def account_field(name, value):
    def change(record): record["outcome"]["state"]["account"][name] = value
    return change


def phantom_clone(record):
    record["outcome"]["state"]["trace"].append("tag clone")


def log_removed(record):
    record["outcome"]["state"]["syscalls"]["log"] = []


def log_changed(record):
    record["outcome"]["state"]["syscalls"]["log"][0]["bytes"] = "62"


def terminal_detail(record):
    record["outcome"]["detail"] = 1


def terminal_log(record):
    record["outcome"]["syscalls"]["log"].append({"syscall": "sol_log_", "bytes": "78"})


def profile_changed(record):
    record["args"]["debug"] = not record["args"]["debug"]


CONTROLS = [
    ("owned info reference points outside receiver", OLD,
     on_record("account/as_ref_info/true-0", result_field("in_receiver", False))),
    ("borrowed info reference becomes receiver field", NEW,
     on_record("account/as_ref_info/true-0", result_field("in_receiver", True))),
    ("borrowed info identity changes", NEW,
     on_record("program/deref/normal", result_field("same_input", False))),
    ("payload reference is a copy", NEW,
     on_record("account/as_ref_payload/true-0", result_field("same_field", False))),
    ("Deref returns a mutable reference", NEW,
     on_record("interface_account/deref/true-0", result_field("mutable", True))),
    ("DerefMut loses mutability", NEW,
     on_record("account/deref_mut/true-0", result_field("mutable", False))),
    ("Sysvar mutable dereference copies payload", NEW,
     on_record("sysvar/deref_mut/0", result_field("same_field", False))),
    ("payload reference reads a stale value", NEW,
     on_record("sysvar/deref/0", result_field("value", 23))),
    ("wrapper key value changes", NEW,
     on_record("signer/key/normal", result("00" * 32))),
    ("defining key implementation changes bytes", NEW,
     on_record("lib/key/" + "ff" * 32, result("00" * 32))),
    ("clone reuses payload field", NEW,
     on_record("account/clone/true-0", result_field("payload_distinct", False))),
    ("clone bypasses T clone", NEW,
     on_record("interface_account/clone/true-0", result_field("value", 7))),
    ("owned clone loses Rc aliases", OLD,
     on_record("account/clone/true-0", result_field("info_aliases", False))),
    ("owned clone reuses source info record", OLD,
     on_record("program/clone/normal", result_field("info_same", True))),
    ("owned clone does not retain lamports Rc", OLD,
     on_record("account/clone/true-0", post_field("counts", [2, 3]))),
    ("payload clone receives another field", OLD,
     on_record("account/clone/true-0", post_field("trace", ["clone:7:false"]))),
    ("payload clone panic retains info early", OLD,
     on_record("account/clone/true-1", post_field("counts", [3, 3]))),
    ("borrowed clone increments Rc counts", NEW,
     on_record("system_account/clone/normal", post_field("counts", [2, 2]))),
    ("PhantomData clone calls T clone", NEW,
     on_record("interface/clone/normal", phantom_clone)),
    ("move leaves payload owned by source", NEW,
     on_record("account/into_inner/true-0", post_field("payload", 7))),
    ("move changes transferred payload", OLD,
     on_record("interface_account/into_inner/true-0", result(17))),
    ("owned move leaks its info Rc", OLD,
     on_record("account/into_inner/true-0", post_field("counts", [2, 2]))),
    ("set_inner bypasses old value drop", NEW,
     on_record("account/set_inner/true-0", post_field("trace", []))),
    ("drop unwind leaves old payload in field", NEW,
     on_record("interface_account/set_inner/true-1", post_field("payload", 7))),
    ("drop callback receives another field", OLD,
     on_record("account/set_inner/true-1", post_field("trace", ["drop:7:false"]))),
    ("sysvar clone copies cached value", NEW,
     on_record("sysvar/clone/0", result_field("value", 7))),
    ("sysvar decoder runs before owned info retain", OLD,
     on_record("sysvar/clone/0", post_field("trace", ["from_info:2:2:true"]))),
    ("sysvar decoder receives cloned info record", OLD,
     on_record("sysvar/clone/0", post_field("trace", ["from_info:3:3:false"]))),
    ("sysvar decode unwind leaks retained info", OLD,
     on_record("sysvar/clone/2", post_field("counts", [3, 3]))),
    ("sysvar unwrap changes error code", NEW,
     on_record("sysvar/clone/1", reason("called `Result::unwrap()` on an `Err` value: Custom(82)"))),
    ("old ProgramError loses Borsh string", OLD,
     on_record("sysvar/clone/4", reason("called `Result::unwrap()` on an `Err` value: BorshIoError"))),
    ("0.29 Borsh string changes", "anchor_views_0_29_0",
     on_record("sysvar/clone/4", reason("called `Result::unwrap()` on an `Err` value: BorshIoError(\"changed\")"))),
    ("0.32 borrowed info identity changes", "anchor_views_0_32_1",
     on_record("unchecked_account/as_ref_info/normal", result_field("same_input", False))),
    ("1.1.2 cloned info no longer aliases", "anchor_views_1_1_2",
     on_record("unchecked_account/clone/normal", result_field("info_aliases", False))),
    ("debug readonly mutation omits log", DEBUG,
     on_record("account/deref_mut/false-0", log_removed)),
    ("debug readonly mutation changes log bytes", DEBUG,
     on_record("interface_account/deref_mut/false-0", log_changed)),
    ("debug readonly panic reason changes", DEBUG,
     on_record("account/deref_mut/false-0", reason("not mutable"))),
    ("feature profile silently changes", DEBUG,
     on_record("account/deref_mut/false-0", profile_changed)),
    ("Lamports skips actual AsRef callback", NEW,
     on_record("lib/get_lamports/normal", post_field("trace", []))),
    ("Lamports returns balance before AsRef mutation", NEW,
     on_record("lib/get_lamports/mutates", result(40))),
    ("AsRef panic loses prior mutation", NEW,
     on_record("lib/get_lamports/panics", account_field("lamports", 40))),
    ("borrow conflict changes panic reason", NEW,
     on_record("lib/get_lamports/conflict", reason("RefCell already borrowed"))),
    ("key observation changes framed owner", NEW,
     on_record("program/key/normal", account_field("owner", "04" * 32))),
    ("reference observation changes framed bytes", NEW,
     on_record("account/deref/true-0", account_field("data", "0800000000000000"))),
    ("terminal observation invents detail", OLD,
     on_record("account/clone/true-2", terminal_detail)),
    ("terminal observation invents log", NEW,
     on_record("sysvar/clone/3", terminal_log)),
    ("terminal reason changes", NEW,
     on_record("account/set_inner/true-2", reason("unreachable"))),
]


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('anchor_views_0_27_0', 'anchor_views_0_29_0', 'anchor_views_0_32_1', 'anchor_views_1_0_2', 'anchor_views_1_1_2')]
