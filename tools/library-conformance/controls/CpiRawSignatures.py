"""Corrupt complete Pinocchio and raw Rust CPI mock boundary observations."""
from common import on_record

CORPUS = "cpi_raw_define_2_3_0"
PINOCCHIO_CORPUS = "cpi_pinocchio_0_9_2"


def request(record):
    return record["outcome"]["state"]["requests"][0]


CONTROLS = []
for prefix in ["unchecked", "raw_c"]:
    for label, change in [
        ("alias", lambda r: request(r)["accounts"][2].__setitem__("lamports_cell", 1)),
        ("order", lambda r: request(r)["accounts"].__setitem__(slice(0, 2), request(r)["accounts"][1::-1])),
        ("seed groups", lambda r: request(r)["signers"].pop(0)),
        ("seed bytes", lambda r: request(r)["signers"][1].__setitem__(1, "0407")),
        ("instruction layout", lambda r: r["layout"]["instruction"].__setitem__(2, 8)),
        ("source account length", lambda r: r["outcome"]["state"]["source"]["input"]["accounts"][0].__setitem__("data_len", 3)),
        ("exact version", lambda r: r["state"].__setitem__("profile", "pinocchio-0.10")),
    ]:
        CONTROLS.append((f"{prefix}: {label}", PINOCCHIO_CORPUS, on_record(prefix + "/aliases", change)))
    CONTROLS.append((f"{prefix}: failure order", PINOCCHIO_CORPUS, on_record(prefix + "/too_many_seeds",
        lambda r: r["outcome"].__setitem__("reason", "MissingAccount"))))
CONTROLS.append(("raw success is zero", PINOCCHIO_CORPUS, on_record("raw_c/aliases",
    lambda r: r["outcome"].__setitem__("result", 1))))
CONTROLS.append(("unchecked success is unit", PINOCCHIO_CORPUS, on_record("unchecked/aliases",
    lambda r: r["outcome"].__setitem__("result", 0))))

for corpus in [CORPUS, "cpi_raw_define_3_0_0", "cpi_raw_program_1_15_2", "cpi_raw_program_1_18_26"]:
    for label, change in [
        ("alias", lambda r: request(r)["accounts"][2].__setitem__("data_cell", 1)),
        ("order", lambda r: request(r)["accounts"].__setitem__(slice(0, 2), request(r)["accounts"][1::-1])),
        ("seed groups", lambda r: request(r)["signers"].pop(0)),
        ("stable vector order", lambda r: r["layout"]["stable_vec"].__setitem__(slice(1, 3), [8, 0])),
        ("zero return", lambda r: r["outcome"].__setitem__("result", 1)),
        ("copyback observation", lambda r: r["outcome"]["state"]["source"]["accounts"][2].__setitem__("data", "0704")),
    ]:
        CONTROLS.append((f"{corpus}: {label}", corpus, on_record("aliases", change)))
    CONTROLS.append((f"{corpus}: failure order", corpus, on_record("too_many_seeds",
        lambda r: r["outcome"].__setitem__("reason", "MissingAccount"))))
