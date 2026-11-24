# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Resolve shared registry values and reviewed prose without supplying defaults for source facts."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re

SECTIONS = ('packages', 'interfaces', 'abstractions', 'models', 'api', 'compatibility',
            'applicability_sources', 'applicability')
REFERENCE = re.compile(r'@(?:(?:text|binding|shared):[a-z0-9-]+|'
                       r'review:source-notes/[a-z0-9_.-]+\.md#review-[a-f0-9]{16})\Z')
PROSE = re.compile(
    r'<!-- registry:(binding|review):([a-f0-9]{16}) -->\n'
    r'<a id="\1-\2"></a>\n\n(.*?)\n<!-- /registry -->', re.S)


def identifier(text):
    """The stable identity of an exact prose clause."""
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def compact_json(value, level=0):
    """Keep short values together and expose the structure of longer records."""
    inline = json.dumps(value, ensure_ascii=False, separators=(', ', ': '))
    if not isinstance(value, (dict, list)) or len(inline) + 2 * level <= 110:
        return inline
    indent = '  ' * (level + 1)
    if isinstance(value, dict):
        rows = [json.dumps(k) + ': ' + compact_json(v, level + 1) for k, v in value.items()]
        opening, closing = '{', '}'
    else:
        rows = [compact_json(v, level + 1) for v in value]
        opening, closing = '[', ']'
    return opening + '\n' + ',\n'.join(indent + row for row in rows) + '\n' + '  ' * level + closing


def source_file(package, name):
    relative = Path(name) if isinstance(name, str) else Path('/')
    if (relative.is_absolute() or '..' in relative.parts or not relative.parts
            or relative.suffix not in {'.json', '.md'}):
        raise ValueError(f'Invalid registry input path: {name}')
    path = Path(package) / relative
    if (not path.is_file() or any(parent.is_symlink() for parent in (path, *path.parents)
                                 if parent != Path(package).parent)
            or not path.resolve().is_relative_to(Path(package).resolve())):
        raise ValueError(f'Missing or linked registry input: {name}')
    return path


def registry_files(package, document):
    names = document.get('fragments')
    if (not isinstance(names, list) or not names
            or any(not isinstance(name, str) or not re.fullmatch(r'source-map/[a-z0-9][a-z0-9_.-]*\.json', name)
                   for name in names) or len(names) != len(set(names))):
        raise ValueError('Invalid or repeated registry fragments')
    definitions = [document.get('texts'), document.get('shared')]
    if definitions != ['source-map/texts.json', 'source-map/shared.json']:
        raise ValueError('Registry definitions require texts.json and shared.json')
    prose = document.get('prose')
    if (not isinstance(prose, list) or not prose
            or any(name != 'BINDINGS.md' and (not isinstance(name, str)
                   or not re.fullmatch(r'source-notes/[a-z0-9][a-z0-9_.-]*\.md', name)) for name in prose)
            or len(prose) != len(set(prose))):
        raise ValueError('Invalid registry prose inputs')
    selected = names + definitions + prose
    if len(selected) != len(set(selected)):
        raise ValueError('Duplicate registry input')
    paths = [source_file(package, name) for name in selected]
    available = set((Path(package) / 'source-map').rglob('*.json'))
    if available != set(paths[:len(names) + len(definitions)]):
        raise ValueError('Registry fragments must cover every available JSON input')
    return [Path(package) / 'source-map.json', *paths]


def expand_sections(package, document, read_json):
    """Expand every reference, preserving registered list order and exact clause bytes."""
    registry_files(package, document)
    definitions = {}
    texts = read_json(source_file(package, document['texts']))
    shared = read_json(source_file(package, document['shared']))
    if not isinstance(texts, dict) or not isinstance(shared, dict):
        raise ValueError('Registry definitions must be objects')
    for key, value in texts.items():
        if not isinstance(value, str) or key != identifier(value):
            raise ValueError(f'Invalid text identity: {key}')
        definitions['@text:' + key] = value
    for key, value in shared.items():
        if not re.fullmatch(r'[a-z-]+-[a-f0-9]{16}', key) or not isinstance(value, (dict, list)):
            raise ValueError(f'Invalid shared value: {key}')
        # Validate the expanded shared content below, before resolving prose.
        definitions['@shared:' + key] = value
    for name in document['prose']:
        contents = source_file(package, name).read_text()
        clauses = list(PROSE.finditer(contents))
        if contents.count('<!-- registry:') != len(clauses):
            raise ValueError(f'Malformed registry prose in {name}')
        for clause in clauses:
            kind, key, value = clause.groups()
            ref = ('@binding:' + key if kind == 'binding'
                   else '@review:' + name + '#review-' + key)
            if key != identifier(value) or ref in definitions:
                raise ValueError(f'Duplicate or invalid registry prose identity: {ref}')
            if (kind == 'binding') != (name == 'BINDINGS.md'):
                raise ValueError(f'Registry clause has the wrong document owner: {ref}')
            definitions[ref] = value
    checking = set()

    def shared_contents(value):
        if isinstance(value, str) and value.startswith('@shared:'):
            if value not in definitions or value in checking:
                raise ValueError(f'Unknown or cyclic shared reference: {value}')
            checking.add(value)
            result = shared_contents(definitions[value])
            checking.remove(value)
            return result
        if isinstance(value, dict):
            return {key: shared_contents(item) for key, item in value.items()}
        if isinstance(value, list):
            return [shared_contents(item) for item in value]
        return value

    for key in shared:
        raw = json.dumps(shared_contents('@shared:' + key), sort_keys=True, ensure_ascii=False)
        if not key.endswith('-' + identifier(raw)):
            raise ValueError(f'Shared content disagrees with its stable identity: {key}')
    used = set()
    active = set()

    def expand(value):
        if isinstance(value, str) and value.startswith('@'):
            if not REFERENCE.fullmatch(value) or value not in definitions:
                raise ValueError(f'Unknown registry reference: {value}')
            if value in active:
                raise ValueError(f'Cyclic registry reference: {value}')
            used.add(value)
            active.add(value)
            result = expand(definitions[value]) if value.startswith('@shared:') else definitions[value]
            active.remove(value)
            return deepcopy(result)
        if isinstance(value, dict):
            return {key: expand(item) for key, item in value.items()}
        if isinstance(value, list):
            return [expand(item) for item in value]
        return value

    entries = {key: {} for key in SECTIONS}
    orders = {key: {} for key in SECTIONS}
    for name in document['fragments']:
        data = read_json(source_file(package, name))
        if not isinstance(data, dict) or set(data) - {*SECTIONS, 'binding_defaults'}:
            raise ValueError(f'Unknown registry fields in {name}')
        defaults = expand(data.get('binding_defaults', []))
        if not isinstance(defaults, list) or any(not isinstance(value, str) for value in defaults):
            raise ValueError(f'Invalid binding defaults in {name}')
        for section in SECTIONS:
            rows = data.get(section, {})
            if not isinstance(rows, dict):
                raise ValueError(f'Invalid {section} mapping in {name}')
            for key, row in rows.items():
                if not isinstance(row, dict) or key in entries[section]:
                    raise ValueError(f'Duplicate or invalid {section} record: {key}')
                row = deepcopy(row)
                order = row.pop('order', None)
                if type(order) is not int or order < 0 or order in orders[section]:
                    raise ValueError(f'Duplicate or missing {section} order: {key}')
                orders[section][order] = key
                binding_defaults = row.pop('binding_defaults', True) if section == 'api' else False
                if type(binding_defaults) is not bool:
                    raise ValueError(f'Invalid binding default selection: {key}')
                row = expand(row)
                if section == 'api' and binding_defaults and defaults:
                    obligations = row.get('binding_obligations', [])
                    if not isinstance(obligations, list) or any(not isinstance(item, str) for item in obligations):
                        raise ValueError(f'Invalid binding obligations: {key}')
                    row['binding_obligations'] = defaults + obligations
                entries[section][key] = row
    for section, ordering in orders.items():
        if set(ordering) != set(range(len(ordering))):
            raise ValueError(f'Noncontiguous registry order: {section}')
        entries[section] = {ordering[n]: entries[section][ordering[n]] for n in sorted(ordering)}
    if unused := set(definitions) - used:
        raise ValueError('Unused registry definitions: ' + ', '.join(sorted(unused)))
    strings = [value for value in definitions.values() if isinstance(value, str)]
    if len(strings) != len(set(strings)):
        raise ValueError('Duplicate prose across registry definitions')
    return entries


def record_file(package, section, identifier, read_json):
    """Locate the single editing surface of a named record through its registry index."""
    document = read_json(Path(package) / 'source-map.json')
    candidates = []
    for name in document.get('fragments', []):
        path = source_file(package, name)
        data = read_json(path)
        if identifier in data.get(section, {}):
            candidates.append((path, data))
    if len(candidates) != 1:
        raise ValueError(f'Expected one {section} record for {identifier}')
    return candidates[0]
