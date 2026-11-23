"""Controls against stale reviews, hidden new gaps and invented coverage state."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import generate_gap_index as gaps


class GapIndexControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name in [*gaps.input_hashes(gaps.ROOT), gaps.REVIEW.as_posix()]:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(gaps.ROOT / name, target)

    def reviewed_change(self):
        path = self.root / gaps.REVIEW
        review = json.loads(path.read_text())
        review['inputs'] = gaps.input_hashes(self.root)
        path.write_text(json.dumps(review))

    def test_stale_source_record_requires_review(self):
        path = self.root / gaps.SDK / 'source-map/foundation.json'
        path.write_text(path.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'review inputs changed'):
            gaps.records(self.root)

    def test_new_registered_limitation_is_not_hidden(self):
        path = self.root / gaps.SDK / 'source-map/libraries.json'
        data = json.loads(path.read_text())
        identifier = next(name for name, row in data['models'].items()
                          if row.get('kind') == 'supporting'
                          and not row.get('model_gaps') and not row.get('remaining_requirements'))
        data['models'][identifier]['model_gaps'] = ['Control: a newly recorded limitation.']
        path.write_text(json.dumps(data))
        self.reviewed_change()
        _, rows = gaps.records(self.root)
        selected = [row for row in rows if row['id'] == 'sdk-model:' + identifier]
        self.assertEqual(len(selected), 1)
        self.assertIn('Control: a newly recorded limitation.', selected[0]['recorded_behavior'])

    def test_duplicate_runtime_identity_is_rejected(self):
        path = self.root / gaps.RUNTIME
        data = json.loads(path.read_text())
        data['correspondence'].append(copy.deepcopy(data['correspondence'][0]))
        path.write_text(json.dumps(data))
        self.reviewed_change()
        with self.assertRaisesRegex(ValueError, 'Duplicate gap identity'):
            gaps.records(self.root)

    def test_unknown_test_exception_is_rejected(self):
        path = self.root / gaps.CONFORMANCE / 'requires-open.toml'
        path.write_text(path.read_text() + '\n[[model]]\nid = "unknown-control-model"\n'
                        'detail = "control"\nreason = "This model is not registered."\n')
        self.reviewed_change()
        with self.assertRaisesRegex(ValueError, 'unknown model'):
            gaps.records(self.root)

    def test_review_metadata_cannot_claim_closed_source_proofs(self):
        path = self.root / gaps.REVIEW
        review = json.loads(path.read_text())
        review['policies']['sdk-binding']['status'] = 'closed'
        path.write_text(json.dumps(review))
        with self.assertRaisesRegex(ValueError, 'not editable coverage status'):
            gaps.records(self.root)

    def test_test_exception_is_not_source_proof_credit(self):
        _, rows = gaps.records(self.root)
        by_id = {row['id']: row for row in rows}
        native = by_id['native-test:shared-owned-array::construction']
        self.assertEqual(native['status'], 'documented mathematical-only exception')
        self.assertEqual(by_id['sdk:rust-implementation-bindings']['status'], 'open')
        self.assertEqual(by_id['precondition-test:spl-token-2022::onchain::invoke_transfer_checked']['status'], 'open')

    def test_census_releases_have_stable_pending_records(self):
        _, rows = gaps.records(self.root)
        pending = {row['id']: row for row in rows if row['category'] == 'release-review'}
        self.assertEqual(set(pending), {'release-review:pinocchio-system@0.7.1',
                                       'release-review:pinocchio-token-2022@0.5.1'})
        for row in pending.values():
            self.assertEqual(row['status'], 'applicability review pending')
            self.assertEqual(row['origin'], gaps.CENSUS.as_posix())
            self.assertEqual(row['census_checked_on'], '2026-11-22')
            self.assertEqual(row['last_source_review'], '2026-11-09')
            self.assertTrue(row['declarations'])
            self.assertTrue(row['build_conditions']['profile_ids'])

    def test_additional_census_release_is_not_hidden(self):
        path = self.root / gaps.CENSUS
        data = json.loads(path.read_text())
        finding = data['live_source_census']['findings'][0]
        finding['error'] = finding['error'].replace("['0.7.1']", "['0.7.1', '0.7.2']")
        path.write_text(json.dumps(data))
        self.reviewed_change()
        _, rows = gaps.records(self.root)
        pending = {row['id'] for row in rows if row['category'] == 'release-review'}
        self.assertEqual(pending, {'release-review:pinocchio-system@0.7.1',
                                  'release-review:pinocchio-system@0.7.2',
                                  'release-review:pinocchio-token-2022@0.5.1'})

    def test_unrecognized_census_gap_is_rejected(self):
        path = self.root / gaps.CENSUS
        data = json.loads(path.read_text())
        finding = data['live_source_census']['findings'][0]
        finding['error'] = finding['error'].replace('missing []', "missing ['0.7.0']")
        path.write_text(json.dumps(data))
        self.reviewed_change()
        with self.assertRaisesRegex(ValueError, 'Unrecognized source census releases'):
            gaps.records(self.root)

    def test_census_package_identity_is_checked(self):
        path = self.root / gaps.CENSUS
        data = json.loads(path.read_text())
        data['live_source_census']['findings'][0]['package'] = 'wrong-package'
        path.write_text(json.dumps(data))
        self.reviewed_change()
        with self.assertRaisesRegex(ValueError, 'Unrecognized source census finding'):
            gaps.records(self.root)

    def test_recording_release_does_not_silently_close_pending_review(self):
        path = self.root / gaps.SDK / 'source-map/applicability.json'
        data = json.loads(path.read_text())
        releases = data['applicability_sources']['pinocchio-system']['releases']
        releases['0.7.1'] = copy.deepcopy(releases['0.7.0'])
        releases['0.7.1']['archive_url'] = releases['0.7.1']['archive_url'].replace('0.7.0', '0.7.1')
        path.write_text(json.dumps(data))
        self.reviewed_change()
        with self.assertRaisesRegex(ValueError, 'already recorded; review its gap presentation'):
            gaps.records(self.root)


if __name__ == '__main__':
    unittest.main()
