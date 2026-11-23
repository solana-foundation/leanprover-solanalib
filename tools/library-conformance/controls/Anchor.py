"""Family Anchor: semantic corruptions of `anchor_lang_1_0_2` and `anchor_spl_1_0_2` records.

Each mutation changes one observable of one record (resource identity or liveness, callback order, a
lease, an error field, a value) and must be rejected as a MISMATCH of that record.
"""

from common import flip_spare, hex_bytes, hex_text, on_record, outside_precondition

RECORDS = []


def capture(mutate):
    """Give a mutation access to the whole corpus (`RECORDS`)."""
    def wrapped(records):
        RECORDS[:] = records
        mutate(records)
    wrapped.record_id = mutate.record_id
    return wrapped

LANG = "anchor_lang_1_0_2"
SPL = "anchor_spl_1_0_2"


def out(r):
    return r["outcome"]


def result(r):
    return out(r)["result"]


def state(r):
    return out(r)["state"]


def anchor_err(r):
    return result(r)["err"]["AnchorError"]


# Owned errors: identity and liveness of Strings and Boxes.
def box_not_fresh(r): result(r)["box"] = 0
def string_copied(r): result(r)["strings"][2] = None
def old_string_kept(r): state(r)["strings_live"][2] = True
def receiver_not_dropped(r): state(r)["boxes_live"][0] = True
def receiver_replaced(r): result(r)["box"] = None
def swap_drops(r):
    log = state(r)["log"]
    log[-1], log[-2] = log[-2], log[-1]
def compared_value(r): result(r)["value"]["AnchorError"]["compared"]["Values"][0] += "!"

# Constructors and loaders.
def second_pubkey(r): anchor_err(r)["compared"]["Pubkeys"][1] = "00" * 32
def error_code(r): anchor_err(r)["code"] += 1
def guard_kept(r): state(r)["leases"][1] = "shared"
def owner_not_assigned(r): state(r)["input"]["accounts"][0]["owner"] = "55" * 32
def callback_order(r): state(r)["log"].reverse()
def program_error_variant(r): result(r)["err"]["ProgramError"]["error"]["variant"] = "InvalidArgument"
def discriminator_error(r): anchor_err(r)["name"] = "AccountDiscriminatorNotFound"
def decoded_value(r): result(r)["ok"]["value"] += 1
def info_cell(r): result(r)["ok"]["info"]["data"] = 0
def view_offset(r): result(r)["ok"]["offset"] = 0
def lease_kind(r): state(r)["leases"][1] = "shared"
def panic_kind(r): out(r)["reason"] = "from_bytes>TargetAlignmentGreaterAndInputNotAligned"
def lamports_store(r): state(r)["input"]["accounts"][0]["lamports"] += 1

# Others.
def counts_unchanged(r): state(r)["counts"] = [c - 1 for c in state(r)["counts"]]
def seed_changed(r): result(r)["signer_seeds"][0][0] = "00"
def remaining_nonempty(r): result(r)["remaining_accounts"] = [result(r)["accounts"]["from"]]
def key_changed(r): out(r)["result"] = "00" * 32
def log_fields_merged(r):
    req = state(r)["syscalls"]["log"][0]
    req["fields"] = ["".join(req["fields"])]
def amount_plus_one(r): result(r)["ok"] += 1
def unwind_to_return(r):
    o = out(r)
    o["exit"] = "returned"
    o["result"] = {"ok": 0}
    del o["reason"]
def instruction_tag(r):
    call = state(r)["syscalls"]["log"][0]["call"]
    call["instruction"]["data"] = "0c" + call["instruction"]["data"][2:]
def custom_code(r): result(r)["err"]["ProgramError"]["error"]["fields"] = [2]
def supply_changed(r): result(r)["supply"] += 1
def precheck_passes(r):
    # The pre-check let the CPI through: the reply is consumed and the request logged.
    ok = [x for x in RECORDS if x["id"] == "transfer/borrowed/authority_data_shared"][0]
    out(r)["result"] = {"ok": None}
    state(r)["syscalls"] = ok["outcome"]["state"]["syscalls"]
def precheck_fails(r):
    o = out(r)
    o["result"] = {"err": {"ProgramError": {"error": {"variant": "AccountBorrowFailed", "fields": []},
                                            "origin": None, "compared": None}}}
    state(r)["syscalls"] = {"replies": r["state"]["syscalls"]["replies"], "log": []}
def precheck_other_error(r): result(r)["err"]["ProgramError"]["error"]["variant"] = "InvalidArgument"


# Frames: region parts no model represents, and the syscall state.
def region_account(r, k=0):
    accts = [a for a in state(r)["input"]["accounts"] if "duplicate_of" not in a]
    return accts[k]
def lamports_777(r): region_account(r)["lamports"] += 777
def data_byte(r):
    a = region_account(r)
    b = bytearray(hex_bytes(a["data"]))
    b[0] ^= 0xff
    a["data"] = hex_text(bytes(b))
def key_byte(r): region_account(r)["key"] = "ee" + region_account(r)["key"][2:]
def signer_flag(r): region_account(r)["is_signer"] ^= 1
def rent_epoch(r): region_account(r)["rent_epoch"] -= 1
def marker(r): region_account(r)["marker"] = 254
def padding(r): region_account(r)["padding"] += 1
def spare(r): flip_spare(region_account(r), 3)
def instruction_data(r): state(r)["input"]["instruction_data"] = "01"
def program_id(r): state(r)["input"]["program_id"] = "00" * 32
def duplicate_target(r):
    for a in state(r)["input"]["accounts"]:
        if "duplicate_of" in a:
            a["duplicate_of"] += 1
            return
    raise ValueError("no duplicate entry")
def syscall_logged(r): state(r)["syscalls"]["log"].append({"syscall": "sol_log_", "bytes": "68"})
def cpi_repeated(r):
    log = state(r)["syscalls"]["log"]
    log.append(log[0])
def fresh_leak(r): state(r)["fresh_live"] += 1
def fresh_freed(r): state(r)["fresh_live"] -= 1
def name_string_freed(r): state(r)["strings_live"][0] = False
def receiver_box_freed(r): state(r)["boxes_live"][0] = False
def reply_consumed(r): state(r)["syscalls"]["replies"] = []
def reply_added(r): state(r)["syscalls"]["replies"].append(
    {"syscall": "sol_log_data", "return": 0, "data": ""})
def lease_after(r): state(r)["leases"][0] = "shared"
def lease_freed(r): state(r)["leases"][0] = "free"
def projection_region(r): out(r)["state"]["region"]["accounts"][0]["lamports"] += 1
def unchecked_decoder(r):
    log = state(r)["log"]
    for i, e in enumerate(log):
        if "deserialize" in e:
            log[i] = {"deserialize_unchecked": e["deserialize"]}
            return
    raise ValueError("no deserialize event")


# Preconditions (`requires`, decided by `RequiresCheck`): a record outside one is rejected by that model,
# whose report names it under "requires_violated".
def requires_violated(*models):
    return '"requires_violated":[' + ",".join(f'"{m}"' for m in models) + "]"


def stray_borrow(r):
    """A held borrow of a cell that does not exist: the borrow state is not `Valid`."""
    r["state"]["borrows"].append({"cell": 99, "mode": "shared"})


def duplicate_payload_string(r, receiver_in_state):
    """The message of the payload is its name String: the Strings of the payload are not distinct (`Nodup`)."""
    if receiver_in_state:
        r["state"]["boxes"][0]["AnchorError"]["message"] = 0
    else:
        r["args"]["error"]["AnchorError"]["message"] = 0
    value = result(r)["value"]["AnchorError"]
    value["message"] = value["name"]
    result(r)["strings"][1] = 0


A = "Solanalib.Specs.AnchorLang.accounts."
E = "Solanalib.Specs.AnchorLang.error.Error."


# Check leftover replies, slice-bounds messages and the two copies of the input.
def leftover_reply_renamed(r):
    state(r)["syscalls"]["replies"][0] = {"syscall": "sol_log_data", "return": 1, "data": ""}


def scripted_reply_return(r):
    r["state"]["syscalls"]["replies"][0]["return"] = 77


def reason(text):
    def change(r):
        out(r)["reason"] = text
    return change


def input_owner(r):
    a = r["state"]["input"]["accounts"][0]
    a["owner"] = "66" * 32


def before_count(r):
    r["state"]["before"]["region"]["count"] += 1


def before_spare(r):
    flip_spare(r["state"]["before"]["region"]["accounts"][0], 5)


BEFORE = '"frame_violated":["before agrees with input"]'


CONTROLS = [
    ("From<AnchorError> Box reported as an input", LANG, on_record("from_anchor/plain", box_not_fresh)),
    ("From<AnchorError> copies an account-name String", LANG, on_record("from_anchor/account_name+values", string_copied)),
    ("with_pubkeys keeps the old compared String", LANG, on_record("with_pubkeys/anchor+values/8_9", old_string_kept)),
    ("with_pubkeys allocates a new Box", LANG, on_record("with_pubkeys/program/0_0", receiver_replaced)),
    ("with_values drops R before L", LANG, on_record("with_values/anchor/ok", swap_drops)),
    ("with_values keeps the receiver on a display panic", LANG, on_record("with_values/anchor/left_display_panics", receiver_not_dropped)),
    ("with_values compared text", LANG, on_record("with_values/anchor+pubkeys/ok", compared_value)),
    ("wrong-owner diagnostic key", LANG, on_record("account_try_from/wrong_owner", second_pubkey)),
    ("AccountNotInitialized code", LANG, on_record("account_try_from/system_zero_lamports", error_code)),
    ("decoder panic leaves the data guard", LANG, on_record("account_try_from/decode_panics", guard_kept)),
    ("assignment of the second Owner call lost", LANG, on_record("account_try_from/second_owner_assigns", owner_not_assigned)),
    ("decoder lamports store lost", LANG, on_record("account_try_from/decode_effects", lamports_store)),
    ("callback order", LANG, on_record("interface_try_from/ok", callback_order)),
    ("CheckOwner error variant", LANG, on_record("interface_try_from/check_error", program_error_variant)),
    ("decoded value", LANG, on_record("interface_try_from/decode_assigns", decoded_value)),
    ("returned AccountInfo cell", LANG, on_record("account_try_from/duplicate", info_cell)),
    ("discriminator error kind", LANG, on_record("loader_try_from/wrong_discriminator", discriminator_error)),
    ("load view offset", LANG, on_record("load/ok", view_offset)),
    ("load_mut guard mode", LANG, on_record("load_mut/ok", lease_kind)),
    ("load panic kind", LANG, on_record("load/short_payload", panic_kind)),
    ("to_account_info without Rc clones", LANG, on_record("to_account_info/plain/ok", counts_unchanged)),
    ("new_with_signer seeds", LANG, on_record("new_with_signer/distinct/one_signer", seed_changed)),
    ("new_with_signer remaining accounts", LANG, on_record("new_with_signer/aliased/no_signers", remaining_nonempty)),
    ("AccountInfo key", LANG, on_record("info_key/plain", key_changed)),
    ("sol_log_data field boundaries", LANG, on_record("sol_log_data/several", log_fields_merged)),
    ("amount value", SPL, on_record("amount/token_account", amount_plus_one)),
    ("short amount slice returns", SPL, on_record("amount/short_71", unwind_to_return)),
    ("transfer instruction tag", SPL, on_record("transfer/unsigned/ok/1000000", instruction_tag)),
    ("transfer error code", SPL, on_record("transfer/signed/custom/1000000", custom_code)),
    ("Mint supply", SPL, on_record("mint_deref/both_authorities", supply_changed)),
    ("transfer pre-check passes a mutably borrowed writable account", SPL,
     capture(on_record("transfer/borrowed/from_data_exclusive", precheck_passes))),
    ("transfer pre-check passes a shared-borrowed writable account", SPL,
     capture(on_record("transfer/borrowed/from_lamports_shared", precheck_passes))),
    ("transfer pre-check rejects a shared-borrowed readonly authority", SPL,
     on_record("transfer/borrowed/authority_data_shared", precheck_fails)),
    ("transfer pre-check error kind", SPL, on_record("transfer/borrowed/authority_lamports_exclusive", precheck_other_error)),
    # Region frame (several records and functions).
    ("transfer lamports +777 after the call", SPL, on_record("transfer/unsigned/ok/0", lamports_777)),
    ("transfer lamports +777, borrowed case", SPL, on_record("transfer/borrowed/authority_data_shared", lamports_777)),
    ("transfer data byte after the call", SPL, on_record("transfer/signed/custom/1000000", data_byte)),
    ("transfer held lease released", SPL, on_record("transfer/borrowed/from_lamports_shared", lease_freed)),
    ("try_from key after the call", LANG, on_record("account_try_from/decode_effects", key_byte)),
    ("load_mut is_signer after the call", LANG, on_record("load_mut/ok", signer_flag)),
    ("loader try_from rent epoch", LANG, on_record("loader_try_from/ok", rent_epoch),
     "FAIL anchor_lang_1_0_2/loader_try_from/ok: region bytes no model represents changed"),
    ("interface try_from marker", LANG, on_record("interface_try_from/ok", marker)),
    ("amount padding", SPL, on_record("amount/token_account", padding)),
    ("try_from spare bytes", LANG, on_record("account_try_from/data_shared", spare),
     "FAIL anchor_lang_1_0_2/account_try_from/data_shared: region bytes no model represents changed"),
    ("load instruction data", LANG, on_record("load/ok", instruction_data),
     "FAIL anchor_lang_1_0_2/load/ok: region bytes no model represents changed"),
    ("load program id", LANG, on_record("load_mut/readonly", program_id),
     "FAIL anchor_lang_1_0_2/load_mut/readonly: region bytes no model represents changed"),
    ("duplicate marker target", LANG, on_record("account_try_from/duplicate", duplicate_target)),
    ("to_account_info region after", LANG, on_record("to_account_info/plain/ok", lamports_777)),
    ("to_account_info lease after", LANG, on_record("to_account_info/second/as_ref_panics", lease_after)),
    ("new_with_signer region after", LANG, on_record("new_with_signer/distinct/two_signers", data_byte)),
    ("new_with_signer key after", LANG, on_record("new_with_signer/aliased/empty_signer", key_byte)),
    ("projection region after", LANG, on_record("signer_key/second", projection_region)),
    # Syscall frame (several records and functions).
    ("syscall during with_values", LANG, on_record("with_values/program/ok", syscall_logged)),
    ("syscall during From<AnchorError>", LANG, on_record("from_anchor/plain", syscall_logged)),
    ("syscall during with_pubkeys", LANG, on_record("with_pubkeys/anchor/8_9", syscall_logged)),
    ("syscall during Account::try_from", LANG, on_record("account_try_from/ok", syscall_logged)),
    ("syscall during load", LANG, on_record("load/data_shared", syscall_logged)),
    ("syscall during Key::key", LANG, on_record("info_key/second", syscall_logged)),
    ("syscall during to_account_info", LANG, on_record("to_account_info/duplicate/ok", syscall_logged)),
    ("syscall during new_with_signer", LANG, on_record("new_with_signer/aliased/one_signer", syscall_logged)),
    ("syscall during amount", SPL, on_record("amount/max", syscall_logged)),
    ("syscall during Mint deref", SPL, on_record("mint_deref/no_authorities", syscall_logged)),
    ("second CPI during transfer", SPL, on_record("transfer/unsigned/custom/1000000", cpi_repeated)),
    # Liveness of allocations made during the call.
    ("From<AnchorError> Box freed", LANG, on_record("from_anchor/code_max", fresh_freed)),
    ("with_values leaks a converted String", LANG, on_record("with_values/anchor+values/right_display_panics", fresh_leak)),
    ("with_values loses a converted String", LANG, on_record("with_values/program/ok_long", fresh_freed)),
    ("with_pubkeys allocates", LANG, on_record("with_pubkeys/program+account_name+pubkeys/0_0", fresh_leak)),
    # rust-lang/rust#47949 alternative: only on the operand-drop path, and only whole.
    ("with_values leaks the receiver on a right display panic", LANG,
     on_record("with_values/program_custom+source+values/right_display_panics", receiver_not_dropped)),
    ("with_values return-place leak with a freed receiver String", LANG,
     on_record("with_values/anchor+values/left_drop_panics", name_string_freed)),
    ("with_values return-place leak without the new Strings", LANG,
     on_record("with_values/program+account_name+pubkeys/right_drop_panics", fresh_freed)),
    ("with_values return-place: Box freed, Strings kept", LANG,
     on_record("with_values/anchor/right_drop_panics", receiver_box_freed)),
    ("transfer reply consumed without a CPI", SPL, on_record("transfer/borrowed/from_data_shared", reply_consumed)),
    ("sol_log_data reply appears", LANG, on_record("sol_log_data/one", reply_added)),
    # The constructors must call try_deserialize, not try_deserialize_unchecked.
    ("Account::try_from uses the unchecked decoder", LANG, on_record("account_try_from/decode_effects", unchecked_decoder)),
    ("InterfaceAccount::try_from uses the unchecked decoder", LANG, on_record("interface_try_from/decode_error", unchecked_decoder)),
    # Preconditions.
    ("Account::try_from outside Valid", LANG, outside_precondition("account_try_from/ok", stray_borrow),
     requires_violated(A + "account.Account.try_from_run", A + "account.Account.try_from_observation_run")),
    ("InterfaceAccount::try_from outside Valid", LANG, outside_precondition("interface_try_from/ok", stray_borrow),
     requires_violated(A + "interface_account.InterfaceAccount.try_from_run",
                       A + "interface_account.InterfaceAccount.try_from_observation_run")),
    ("AccountLoader::try_from outside Valid", LANG, outside_precondition("loader_try_from/ok", stray_borrow),
     requires_violated(A + "account_loader.AccountLoader.try_from_run")),
    ("From<AnchorError> payload Strings not distinct", LANG,
     outside_precondition("from_anchor/plain", lambda r: duplicate_payload_string(r, False)),
     requires_violated(E + "from_anchor_error_run")),
    ("with_pubkeys payload Strings not distinct", LANG,
     outside_precondition("with_pubkeys/anchor/8_9", lambda r: duplicate_payload_string(r, True)),
     requires_violated(E + "with_pubkeys_run")),
    ("with_values payload Strings not distinct", LANG,
     outside_precondition("with_values/anchor/ok", lambda r: duplicate_payload_string(r, True)),
     requires_violated(E + "with_values_run")),
    # No record leaves the preconditions of load, load_mut, their observations, the observation of the loader,
    # amount, new_with_signer and transfer (the parser types every cell; the checkers fix the ledger and
    # builder states): the `*_rejects_illTyped`, `new_with_signer_decider_rejects` and
    # `transfer_decider_rejects` theorems of `RequiresCheck` (requires-theorems.toml) show that
    # their deciders reject an input outside.
    ("transfer leftover reply renamed", SPL, on_record("transfer/borrowed/from_data_shared", leftover_reply_renamed)),
    ("transfer return of the unused reply changed", SPL,
     on_record("transfer/borrowed/authority_lamports_exclusive", scripted_reply_return)),
    ("load slice end index", LANG,
     on_record("load/short_payload", reason("range end index 25 out of range for slice of length 23"))),
    ("load_mut slice length", LANG,
     on_record("load_mut/misaligned_short", reason("range end index 40 out of range for slice of length 17"))),
    ("amount slice start reported as end", SPL,
     on_record("amount/empty", reason("range end index 72 out of range for slice of length 0"))),
    ("key projection input owner differs from before", LANG, on_record("info_key/plain", input_owner), BEFORE),
    ("deref projection before count", LANG, on_record("account_deref/second", before_count), BEFORE),
    ("key projection before spare byte", LANG, on_record("signer_key/plain", before_spare), BEFORE),
]
