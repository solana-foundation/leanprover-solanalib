"""Corrupt whole-signature mock observations without executing an invocation."""

from common import on_record


CORPORA = [
    "cpi_program_1_15_2", "cpi_program_1_18_26", "cpi_program_2_2_1", "cpi_program_2_3_0",
    "cpi_invoke_0_4_0_i2_2_1", "cpi_invoke_0_4_0_i2_3_3",
    "cpi_invoke_0_5_0_s3_0_0", "cpi_invoke_0_5_0_s3_0_1",
]


def request(record):
    return record["outcome"]["state"]["requests"][0]


def alias(record):
    request(record)["accounts"][2]["lamports_cell"] = 1


def account_order(record):
    accounts = request(record)["accounts"]
    accounts[0], accounts[1] = accounts[1], accounts[0]


def empty_signer_group(record):
    request(record)["signers"].pop(0)


def returned_borrow_error(record):
    record["outcome"]["result"] = {"ok": None}


def vec_layout(record):
    record["layout"]["vec_words"][0:2] = ["pointer", "capacity"]


def fresh_borrow_observation(record):
    record["outcome"]["state"]["source"]["borrow_observations"][0][0] = False


def terminal_order(record):
    record["outcome"]["reason"] = "MissingAccount"


def version(record):
    record["state"]["profile"] = "unreviewed-version"


def unsigned_seeds(record):
    record["args"]["signers"] = [[]]


CONTROLS = []
for corpus in CORPORA:
    for label, record, mutation in [
        ("repeated alias", "signed_aliases", alias),
        ("account order", "signed_aliases", account_order),
        ("empty signer group", "signed_aliases", empty_signer_group),
        ("lamports borrow error", "first_duplicate_lamports_error", returned_borrow_error),
        ("data borrow error", "first_duplicate_data_error", returned_borrow_error),
        ("Vec word order", "signed_aliases", vec_layout),
        ("fresh borrow observation", "signed_aliases", fresh_borrow_observation),
        ("runtime failure order", "too_many_seeds_terminal", terminal_order),
        ("exact version profile", "signed_aliases", version),
    ]:
        CONTROLS.append((f"{corpus}: {label}", corpus, on_record(record, mutation)))
    CONTROLS.append((f"{corpus}: unsigned seeds", corpus,
        on_record("unsigned_aliases", unsigned_seeds), f"FAIL {corpus}/unsigned_aliases"))

for corpus in ["cpi_program_1_18_26", "cpi_program_2_2_1", "cpi_program_2_3_0"]:
    CONTROLS.append((f"{corpus}: owned constructor retains input", corpus,
        on_record("signed_aliases", lambda r:
            r["layout"]["constructor_control"].__setitem__("input_retained_after_drop", False))))


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('cpi_invoke_0_4_0_i2_2_1', 'cpi_invoke_0_4_0_i2_3_3', 'cpi_invoke_0_5_0_s3_0_0', 'cpi_invoke_0_5_0_s3_0_1', 'cpi_program_1_15_2', 'cpi_program_1_18_26', 'cpi_program_2_2_1', 'cpi_program_2_3_0')]
