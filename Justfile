# Solanalib — Lean 4 library of formal models for Solana programs.

set shell := ["bash", "-cu"]

default:
    @just --list

# Resolve dependencies and download cached Mathlib oleans.
# Run this once after cloning, and again whenever lakefile.lean changes.
setup:
    lake -Kenv=dev update
    lake exe cache get

# Type-check the library (no docs).
build:
    lake build

# Run the regression tests in SolanalibTest/.
test:
    lake test

# Build the documentation site to .lake/build/doc/.
docs:
    lake -Kenv=dev build Solanalib:docs
    python3 scripts/postprocess-docs.py
    @echo ""
    @echo "Docs written to .lake/build/doc/index.html"

# Build and open the documentation site.
docs-open: docs
    open .lake/build/doc/index.html

# Remove build artifacts (keeps the dependency cache).
clean:
    rm -rf .lake/build

# Remove the entire .lake directory, including deps. Forces a full re-setup.
clean-all:
    rm -rf .lake
