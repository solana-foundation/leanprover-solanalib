#!/usr/bin/env bash
# Keep the existing command, including macOS bash 3.2, for every package.
set -eu
exec python3 "$(dirname "$0")/lint-style.py" "$@"
