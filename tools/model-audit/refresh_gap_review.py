#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Seal current gap inputs without changing the explicit review date, policies or scope."""
import argparse
from datetime import date
import json

import generate_gap_index as gaps
from review_seals import write_json


def refresh(root=gaps.ROOT):
    path = root / gaps.REVIEW
    review = json.loads(path.read_text())
    if (review.get('schema_version') != 1 or set(review['policies']) != set(gaps.STATUS)
            or any(set(policy) != {'affected_claims', 'resolution'}
                   for policy in review['policies'].values())):
        raise ValueError('Invalid gap review policies; coverage status is not editable review metadata')
    date.fromisoformat(review['reviewed_on'])
    if not review['scope']:
        raise ValueError('Gap review scope must be explicit')
    review['inputs'] = gaps.input_hashes(root)
    write_json(path, review)
    return len(review['inputs'])


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    count = refresh()
    print(f'Sealed {count} gap inputs; review date, policies and scope are unchanged')


if __name__ == '__main__':
    main()
