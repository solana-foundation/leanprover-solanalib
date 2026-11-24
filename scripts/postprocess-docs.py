#!/usr/bin/env python3
"""Patch the doc-gen4-generated index.html landing page.

doc-gen4's `DocGen4.Output.Index` hard-codes a generic
`"Welcome to the documentation page"` plus a `"This was built using
Lean 4 ..."` footer. We replace that `<main>...</main>` block with a
Solanalib-branded landing page (banner image + tagline + module nav).

Called by `scripts/build-docs.py` after rendering all public modules, before publishing
to GitHub Pages.
"""
from __future__ import annotations

import pathlib
import re
import sys


INDEX = pathlib.Path(".lake/build/doc/index.html")

REPO = "https://github.com/solana-foundation/leanprover-solanalib"
BANNER_BASE = REPO + "/raw/main/docs/assets/banner-github-"
GUIDE = REPO + "/blob/main/"

# doc-gen4 resolves the chosen scheme (dark, light or system) to a `data-theme`
# attribute on the root element. Both banners have transparent backgrounds, so
# each one gets the backdrop it was drawn for; the media query covers the moment
# before the theme script has run.
BANNER_STYLE = """<style>
  .solanalib-banner img { max-width: 100%; border-radius: 8px; }
  .solanalib-banner .light { background: #ffffff; }
  .solanalib-banner .dark { background: #0c1116; display: none; }
  [data-theme="dark"] .solanalib-banner .light { display: none; }
  [data-theme="dark"] .solanalib-banner .dark { display: inline; }
  @media (prefers-color-scheme: dark) {
    :root:not([data-theme]) .solanalib-banner .light { display: none; }
    :root:not([data-theme]) .solanalib-banner .dark { display: inline; }
  }
</style>"""

CUSTOM_MAIN = f"""<main>
  <a id="top"></a>
  {BANNER_STYLE}
  <div class="solanalib-banner" align="center" style="margin: 2em 0;">
    <img class="light" src="{BANNER_BASE}light.png" alt="Solanalib">
    <img class="dark" src="{BANNER_BASE}dark.png" alt="Solanalib">
  </div>
  <h1>Solanalib</h1>
  <p>
    <a href="https://lean-lang.org/">Lean 4</a> models of the Solana runtime
    and of the Rust crates Solana programs are built on, so you can state and
    prove properties of a program without modeling Solana yourself. Source and
    guides are on <a href="{REPO}">GitHub</a>.
  </p>
  <h2>Libraries</h2>
  <ul>
    <li><a href="./Solanalib/Runtime.html"><code>Solanalib.Runtime</code></a>
        — the Solana runtime, following Agave 4.3.2:
        <a href="./Solanalib/Runtime/Account.html">accounts and rent</a>,
        <a href="./Solanalib/Runtime/Transaction.html">transactions and fees</a>,
        <a href="./Solanalib/Runtime/Exec.html">instruction execution</a>,
        <a href="./Solanalib/Runtime/Cpi.html">cross-program invocation</a>,
        <a href="./Solanalib/Runtime/Syscall.html">syscalls</a>, the
        <a href="./Solanalib/Runtime/System.html">System program</a> and
        <a href="./Solanalib/Runtime/Transfer.html">transfer conservation</a></li>
    <li><a href="./Solanalib/Contracts.html"><code>Solanalib.Contracts</code></a>
        — the contract vocabulary the crate models are written in:
        preconditions, outcomes, callbacks, capabilities and versioning</li>
    <li><code>Solanalib.Specs.&lt;Crate&gt;</code>
        — contracts for functions of 53 Rust crates, on a
        <a href="./Solanalib/Specs/Core.html">shared core</a>:
      <ul>
        <li>Frameworks:
          <a href="./Solanalib/Specs/AnchorLang.html">anchor-lang</a>,
          <a href="./Solanalib/Specs/AnchorSpl.html">anchor-spl</a>,
          <a href="./Solanalib/Specs/Pinocchio.html">pinocchio</a>,
          <a href="./Solanalib/Specs/PinocchioToken.html">pinocchio-token</a>,
          <a href="./Solanalib/Specs/PinocchioSystem.html">pinocchio-system</a></li>
        <li>Tokens:
          <a href="./Solanalib/Specs/SplToken.html">spl-token</a>,
          <a href="./Solanalib/Specs/SplToken2022.html">spl-token-2022</a>,
          <a href="./Solanalib/Specs/SplTokenInterface.html">spl-token-interface</a>,
          <a href="./Solanalib/Specs/SplTransferHookInterface.html">spl-transfer-hook-interface</a></li>
        <li>Serialization:
          <a href="./Solanalib/Specs/Borsh.html">borsh</a>,
          <a href="./Solanalib/Specs/Bytemuck.html">bytemuck</a></li>
        <li>Oracles:
          <a href="./Solanalib/Specs/PythSolanaReceiverSdk.html">pyth-solana-receiver-sdk</a>,
          <a href="./Solanalib/Specs/SwitchboardOnDemand.html">switchboard-on-demand</a></li>
        <li>Solana SDK:
          <a href="./Solanalib/Specs/SolanaProgram.html">solana-program</a>,
          <a href="./Solanalib/Specs/SolanaAccountInfo.html">solana-account-info</a>,
          <a href="./Solanalib/Specs/SolanaCpi.html">solana-cpi</a>,
          <a href="./Solanalib/Specs/SolanaSystemInterface.html">solana-system-interface</a>
          and the other <code>solana-*</code> crates in the sidebar</li>
      </ul>
    </li>
  </ul>
  <h2>Guides</h2>
  <ul>
    <li><a href="{GUIDE}docs/getting-started.md">Getting started</a>
        — a worked proof from an SDK contract to runtime execution</li>
    <li><a href="{GUIDE}packages/solanalib-specs/LIBRARIES.md">Library catalog</a>
        — the modeled functions of each crate</li>
    <li><a href="{GUIDE}packages/solanalib-runtime/TRUST.md">Trust boundary</a>
        and <a href="{GUIDE}docs/model-gaps.md">gap index</a>
        — what the models assume and what they do not prove</li>
    <li><a href="{GUIDE}docs/extending.md">Extending Solanalib</a>
        — adding a runtime rule or a crate contract</li>
  </ul>
  <p style="color:#888; font-size:0.9em; margin-top:3em;">
    Used by <a href="https://harmonic.fun">Harmonic</a> and
    <a href="https://lusterna.sh">Lusterna</a>. Generated with
    <a href="https://github.com/leanprover/doc-gen4">doc-gen4</a>.
  </p>
</main>"""


PAGE_TITLE = "Solanalib — Lean toolbox for Solana"


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
