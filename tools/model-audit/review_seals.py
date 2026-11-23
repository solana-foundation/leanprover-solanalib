"""Small file helpers for explicit, reviewed seal refreshes."""
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile


def module_digest(root, module, prefix):
    if not isinstance(module, str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', module):
        raise ValueError(f'Invalid module name: {module!r}')
    if module != prefix and not module.startswith(prefix + '.'):
        raise ValueError(f'Module is outside {prefix}: {module}')
    path = root.joinpath(*module.split('.')).with_suffix('.lean')
    if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f'Missing or noncanonical module source: {path}')
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, data):
    content = json.dumps(data, indent=2, ensure_ascii=False) + '\n'
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as temporary:
        staging = Path(temporary.name)
        temporary.write(content)
    try:
        os.chmod(staging, path.stat().st_mode & 0o777)
        os.replace(staging, path)
    finally:
        staging.unlink(missing_ok=True)
