"""Reject wrong unsigned, lexicographic and equal comparison observations."""
from common import on_record


def result(value):
    def change(record):
        record["outcome"]["result"] = value
    return change


CASES = [
    ("unsigned ordering", "address_comparison_261", "cmp/1/1", result("Less")),
    ("last byte participates", "address_comparison_261", "cmp/2/1", result("Equal")),
    ("equal keys", "address_comparison_261", "cmp/0/0", result("Greater")),
]


CONTROLS = [(label, corpus, on_record(identity, mutate)) for label, corpus, identity, mutate in CASES]
