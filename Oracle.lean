/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Interpreter

/-!
# sbpf-oracle — an executable front end to the Lean sBPF semantics

A thin command-line wrapper that runs `Solanalib.SBPF.bpfInterp` on test vectors
read from standard input, so the Lean semantics can be differentially tested
against an external sBPF VM (see the `spinoza validate` harness).

## Protocol

One test vector per input line, space-separated decimal:

```
<version> <fuel> <byte0> <byte1> …
```

`version` is `1` or `2`; `fuel` bounds the number of steps; the remaining tokens
are the program bytes. For each line, one result line is written to stdout:

```
ok <return-value>      -- program halted via EXIT at depth 0
fault                  -- runtime fault, malformed instruction, or out of fuel
error: <reason>        -- the input line could not be parsed
```

The initial state is all-zero registers and empty memory, so vectors should be
register-only computations terminating in `EXIT` (matching how the reference VM
is initialised in the differential harness).
-/

open Solanalib.SBPF

/-- Run one parsed vector and render its result line. -/
def runVector (version fuel : Nat) (prog : List U8) : String :=
  let v : SBPFV := if version == 1 then .v1 else .v2
  let st0 : BpfState :=
    .ok 0 initRegMap initMem initStackState v initFuncMap 0 (BitVec.ofNat 64 fuel)
  match bpfInterp fuel prog st0 true 0x100000000 with
  | .success r => s!"ok {r.toNat}"
  | _ => "fault"

/-- Split a line into non-empty, whitespace-stripped tokens. -/
def tokenize (line : String) : List String :=
  (line.splitOn " ").filterMap (fun s =>
    let s := (s.replace "\n" "").replace "\r" ""
    if s == "" then none else some s)

/-- Parse and evaluate a single input line. -/
def processLine (line : String) : String :=
  match tokenize line with
  | [] => ""
  | version :: fuel :: rest =>
    match version.toNat?, fuel.toNat? with
    | some ver, some f =>
      match rest.mapM (fun t => t.toNat?.map (fun n => (BitVec.ofNat 8 n))) with
      | some prog => runVector ver f prog
      | none => "error: bad byte"
    | _, _ => "error: bad header"
  | _ => "error: too few fields"

/-- Read vectors from stdin until EOF, echoing one result line each. -/
partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line == "" then return
  let out := processLine line
  if out ≠ "" then IO.println out
  loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)
