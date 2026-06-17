#!/usr/bin/env python3
"""Patch the doc-gen4-generated index.html landing page.

doc-gen4's `DocGen4.Output.Index` hard-codes a generic
`"Welcome to the documentation page"` plus a `"This was built using
Lean 4 ..."` footer. We replace that `<main>...</main>` block with a
Solanalib-branded landing page (banner image + tagline + module nav).

Run this after `lake -Kenv=dev build Solanalib:docs`, before publishing
to GitHub Pages.
"""
from __future__ import annotations

import pathlib
import re
import sys


INDEX = pathlib.Path(".lake/build/doc/index.html")

BANNER_URL = (
    "https://github.com/solana-foundation/leanprover-solanalib"
    "/raw/main/docs/assets/banner-github-light.png"
)

CUSTOM_MAIN = f"""<main>
  <a id="top"></a>
  <div align="center" style="margin: 2em 0;">
    <img src="{BANNER_URL}" alt="Solanalib" style="max-width:100%;">
  </div>
  <h1>Solanalib</h1>
  <p>
    A <a href="https://lean-lang.org/">Lean 4</a> library of formal models
    and verified theorems for Solana programs. Source on
    <a href="https://github.com/solana-foundation/leanprover-solanalib">GitHub</a>.
  </p>
  <p>Start at <a href="./Solanalib.html">the library overview</a>, or
  jump straight to a layer:</p>
  <ul>
    <li><a href="./Solanalib/Primitives/Pubkey.html">Primitives</a>
        — atomic on-chain types (Pubkey, Lamports, Timestamp)</li>
    <li><a href="./Solanalib/Numeric/Fraction.html">Numeric</a>
        — Q68.60 fixed-point arithmetic</li>
    <li><a href="./Solanalib/Account/Basic.html">Account</a>
        — the five-field on-chain account model</li>
    <li><a href="./Solanalib/Instruction/Basic.html">Instruction</a>
        — instruction + AccountMeta</li>
    <li><a href="./Solanalib/Finance/Decay.html">Finance</a>
        — decay, growth, compounding, withdrawal caps</li>
    <li><a href="./Solanalib/SBPF/Syntax.html">SBPF</a>
        — the sBPF ISA semantics</li>
  </ul>
  <p style="color:#888; font-size:0.9em; margin-top:3em;">
    Generated with
    <a href="https://github.com/leanprover/doc-gen4">doc-gen4</a>.
  </p>
</main>"""


PAGE_TITLE = "Solanalib — Lean 4 formal models for Solana"


def main() -> int:
    if not INDEX.exists():
        sys.stderr.write(f"error: {INDEX} not found — has `lake build :docs` been run?\n")
        return 1
    html = INDEX.read_text()
    if "<main>" not in html:
        sys.stderr.write(f"error: no <main> block in {INDEX}; doc-gen4 layout may have changed\n")
        return 2
    # Replace browser-tab title.
    html = html.replace("<title>Index</title>", f"<title>{PAGE_TITLE}</title>", 1)
    # Replace the in-page header filename "Index" with the project name.
    html = html.replace(
        '<span class="name">Index</span>',
        '<span class="name">Solanalib</span>',
        1,
    )
    # Replace the boilerplate <main> with the banner-and-nav landing.
    html = re.sub(r"<main>.*?</main>", CUSTOM_MAIN, html, count=1, flags=re.DOTALL)
    INDEX.write_text(html)
    print(f"patched {INDEX}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
