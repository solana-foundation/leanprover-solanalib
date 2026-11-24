# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Controls for clause identity, registry references, ordering and source boundaries."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from registry_data import expand_sections, identifier, registry_files
from solana_source_map import read_json


class RegistryDataControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.header = {'schema_version': 4, 'fragments': ['source-map/example.json'],
                       'texts': 'source-map/texts.json', 'shared': 'source-map/shared.json',
                       'prose': ['BINDINGS.md', 'source-notes/example.md']}
        self.condition = 'The source values represent the selected mathematical values.'
        self.binding = 'Prove the source implementation correct under the selected contract.'
        self.argument = 'The source operation retains the required state and result.'
        self.text_ref = '@text:' + identifier(self.condition)
        self.binding_ref = '@binding:' + identifier(self.binding)
        self.review_ref = '@review:source-notes/example.md#review-' + identifier(self.argument)
        self.shared = [self.text_ref]
        self.shared_key = 'conditions-' + identifier(json.dumps(self.shared, sort_keys=True, ensure_ascii=False))
        self.data = {'binding_defaults': [self.binding_ref], 'api': {
            'example::read': {'order': 0, 'conditions': '@shared:' + self.shared_key,
                              'argument': self.review_ref}}}
        self.save('source-map.json', self.header)
        self.save('source-map/example.json', self.data)
        self.save('source-map/texts.json', {identifier(self.condition): self.condition})
        self.save('source-map/shared.json', {self.shared_key: self.shared})
        self.prose('BINDINGS.md', 'binding', self.binding)
        self.prose('source-notes/example.md', 'review', self.argument)

    def save(self, name, data):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data) + '\n')

    def prose(self, name, kind, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        key = identifier(text)
        path.write_text(f'<!-- registry:{kind}:{key} -->\n<a id="{kind}-{key}"></a>\n\n'
                        f'{text}\n<!-- /registry -->\n')

    def expand(self):
        return expand_sections(self.root, self.header, read_json)

    def test_exact_conditions_binding_defaults_and_review_text(self):
        self.assertEqual(self.expand()['api']['example::read'], {
            'conditions': [self.condition], 'argument': self.argument,
            'binding_obligations': [self.binding]})

    def test_per_function_binding_exception_does_not_inherit_defaults(self):
        self.data['api']['example::other'] = {'order': 1, 'binding_defaults': False,
                                              'binding_obligations': [self.text_ref]}
        self.save('source-map/example.json', self.data)
        self.assertEqual(self.expand()['api']['example::other']['binding_obligations'], [self.condition])

    def test_fragment_order_does_not_reorder_api_identities(self):
        row = self.data['api'].pop('example::read')
        self.data['api']['example::later'] = {'order': 1, 'binding_defaults': False}
        self.save('source-map/example.json', self.data)
        self.save('source-map/second.json', {'api': {'example::read': row},
                                           'binding_defaults': [self.binding_ref]})
        self.header['fragments'].append('source-map/second.json')
        self.assertEqual(list(self.expand()['api']), ['example::read', 'example::later'])

    def test_stale_prose_identity_is_rejected(self):
        path = self.root / 'source-notes/example.md'
        path.write_text(path.read_text().replace(self.argument, 'A different source claim.'))
        with self.assertRaisesRegex(ValueError, 'prose identity'):
            self.expand()

    def test_wrong_text_identity_is_rejected(self):
        self.save('source-map/texts.json', {identifier(self.condition): 'An unreviewed condition.'})
        with self.assertRaisesRegex(ValueError, 'text identity'):
            self.expand()

    def test_changed_shared_value_needs_a_new_identity(self):
        self.save('source-map/shared.json', {self.shared_key: [self.binding_ref]})
        with self.assertRaisesRegex(ValueError, 'stable identity'):
            self.expand()

    def test_cyclic_and_unknown_shared_values_are_rejected(self):
        for value in ['@shared:' + self.shared_key, '@shared:conditions-0000000000000000']:
            with self.subTest(value=value):
                self.save('source-map/shared.json', {self.shared_key: [value]})
                with self.assertRaisesRegex(ValueError, 'shared reference'):
                    self.expand()

    def test_unknown_clause_is_rejected(self):
        self.data['api']['example::read']['argument'] = '@text:0000000000000000'
        self.save('source-map/example.json', self.data)
        with self.assertRaisesRegex(ValueError, 'Unknown registry reference'):
            self.expand()

    def test_unreferenced_definition_is_rejected(self):
        extra = 'An unused obligation must not be retained.'
        self.save('source-map/texts.json', {identifier(self.condition): self.condition,
                                           identifier(extra): extra})
        with self.assertRaisesRegex(ValueError, 'Unused registry definitions'):
            self.expand()

    def test_duplicate_prose_across_documents_is_rejected(self):
        path = self.root / 'source-notes/example.md'
        path.write_text(path.read_text() * 2)
        with self.assertRaisesRegex(ValueError, 'prose identity'):
            self.expand()

    def test_hidden_fragment_is_rejected(self):
        self.save('source-map/unlisted.json', {})
        with self.assertRaisesRegex(ValueError, 'every available'):
            self.expand()

    def test_malformed_input_lists_are_rejected(self):
        for field in ['fragments', 'prose']:
            with self.subTest(field=field):
                header = dict(self.header, **{field: [{}]})
                with self.assertRaises(ValueError):
                    registry_files(self.root, header)

    def test_binding_obligations_require_a_list(self):
        self.data['api']['example::read']['binding_obligations'] = self.text_ref
        self.save('source-map/example.json', self.data)
        with self.assertRaisesRegex(ValueError, 'binding obligations'):
            self.expand()

    def test_duplicate_and_noncontiguous_order_are_rejected(self):
        row = deepcopy(self.data['api']['example::read'])
        self.data['api']['example::duplicate'] = row
        self.save('source-map/example.json', self.data)
        with self.assertRaisesRegex(ValueError, 'order'):
            self.expand()
        del self.data['api']['example::duplicate']
        self.data['api']['example::read']['order'] = 2
        self.save('source-map/example.json', self.data)
        with self.assertRaisesRegex(ValueError, 'order'):
            self.expand()

    def test_linked_or_escaping_inputs_are_rejected(self):
        for name in ['../outside.json', '/tmp/outside.json']:
            with self.subTest(name=name):
                header = dict(self.header, fragments=[name])
                with self.assertRaises(ValueError):
                    registry_files(self.root, header)
        path = self.root / 'source-map/example.json'
        path.unlink()
        path.symlink_to(self.root / 'source-map/texts.json')
        with self.assertRaisesRegex(ValueError, 'linked registry input'):
            self.expand()


if __name__ == '__main__':
    unittest.main()
