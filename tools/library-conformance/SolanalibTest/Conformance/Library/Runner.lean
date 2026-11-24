/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core

/-!
# The corpus runner

Reads registered corpus files, decides each record with the checker registered
for its corpus, function and generic instantiation, and prints the number of
admitted records per function. A run fails on any rejected record, any record
without a checker, any unreadable record, a checker without records, a missing
corpus file and, when every corpus is checked, an unregistered corpus file.

Records listed as known divergences (`--divergences FILE`) must be rejected
by the listed model; they are counted separately, and a listed record that is
admitted, a listing that matches no record, or one naming another model fails
the run.

`runMain registry ["DIR"]` checks every registered corpus and every `*.json`
file in `DIR`; `runMain registry ["DIR", "--only", "a,b"]` checks only the
corpora `a` and `b`, and `["DIR", "--registered"]` every registered corpus,
without the check for unregistered files (per-family iteration). Files in subdirectories of `DIR`
(such as `manifests/`) are not corpus files.
-/

open Lean (Json)

namespace SolanalibTest.Conformance.Library

structure Tally where
  reference : String
  total : Nat := 0
  admitted : Nat := 0
  /-- Records rejected as listed in `divergences/<corpus>.toml`. -/
  divergent : Nat := 0

/-- A known divergence: records of `corpus` whose ids match the glob `records`
(`*` matches any text) that the registered `model` must reject. The checker
deciding them must name `model` in its reference. -/
structure Divergence where
  corpus : String
  records : String
  model : String
  reason : String
  /-- Pins of the divergent behavior: the recorded exit kind and a substring
  of the recorded reason, when given. -/
  exit : Option String := none
  reasonContains : Option String := none

/-- Glob matching with `*` only. -/
def globMatch : List Char → List Char → Bool
  | [], s => s.isEmpty
  | '*' :: p, s => globMatch p s || (match s with
      | [] => false
      | _ :: t => globMatch ('*' :: p) t)
  | c :: p, d :: s => c == d && globMatch p s
  | _ :: _, [] => false
termination_by p s => (p.length, s.length)

/-- The declaration names the reference text of a checker mentions: its
whitespace-separated words, without surrounding punctuation. -/
def referenceNames (reference : String) : List String :=
  (reference.splitOn " ").map fun w =>
    String.ofList ((w.toList.dropWhile (fun c => "(),+".contains c)).reverse.dropWhile
      (fun c => "(),+".contains c)).reverse

def divergenceOf (j : Json) : Except String Divergence := do
  let opt (k : String) : Except String (Option String) :=
    match j.getObjVal? k with
    | .ok (.str v) => pure (some v)
    | .ok .null | .error _ => pure none
    | .ok other => throw s!"{k} must be a string, got {other.compress}"
  pure { corpus := ← (← field j "corpus").getStr?, records := ← (← field j "records").getStr?,
         model := ← (← field j "model").getStr?, reason := ← (← field j "reason").getStr?,
         exit := ← opt "exit", reasonContains := ← opt "reason_contains" }

/-- The per-model verdicts of a checker on a record (Checker v2), the computed
outcome, and whether the verdicts are per model. A checker without
`checkModels` gives one verdict, which stands for every declared model. -/
def modelVerdicts (checker : Checker) (case : Case) : Result (List ModelVerdict × Json × Bool) := do
  match checker.checkModels with
  | some f =>
    let (vs, expected) ← f case
    let names := vs.map (·.model)
    unless names.length == checker.decides.length && checker.decides.all (names.contains ·) do
      throw s!"per-model verdicts for {names} differ from the declared models \
        {checker.decides}"
    pure (vs, expected, true)
  | none =>
    let v ← checker.check case
    let models := if checker.decides.isEmpty then [checker.reference] else checker.decides
    pure (models.map fun m => ⟨m, v.admitted⟩, v.expected, false)

def containsText (text part : String) : Bool := (text.splitOn part).length > 1

def recordedExit (case : Case) : String :=
  ((case.outcome.getObjVal? "exit").toOption.bind (·.getStr?.toOption)).getD ""

def recordedReason (case : Case) : String :=
  ((case.outcome.getObjVal? "reason").toOption.bind (·.getStr?.toOption)).getD ""

/-! ## Region bytes no family models -/

def jsonAt (j : Json) (path : List String) : Option Json :=
  path.foldlM (fun acc k => (acc.getObjVal? k).toOption) j

/-- The input regions before and after the call: an after-state region read
back with an account-count word (state key `input` or `region`), and the
before-state region under the same key, else under the other one. The region
before is read back (it has a count word) or the account list the region was
serialized from. -/
def regionPairs (case : Case) : List (String × Json × Json) :=
  ["input", "region"].filterMap fun k => do
    let after ← jsonAt case.outcome ["state", k]
    let _ ← jsonAt after ["count"]
    let before ← (jsonAt case.state [k]).orElse fun _ =>
      jsonAt case.state [if k == "input" then "region" else "input"]
    let _ ← jsonAt before ["accounts"]
    pure (k, before, after)

/-- The realloc reserve after the original data of each account. -/
def reserveLength : Nat := 10 * 1024

/-- The region bytes that no family models must be unchanged by every call:
the account-count word, the padding of each duplicate entry, the alignment padding of each account
before the rent epoch, its rent epoch and its spare bytes
(every byte after `data_len` up to the original length plus 10 KiB), the
instruction data and the program id. Against an account list (a fresh
serialization) the padding and the spare bytes must be zero. A function the
driver declares in `spare_writes` (`spareWriter`) may change spare bytes; the models of its
family represent them. -/
def unmodelledRegionProblem (case : Case) (spareWriter : Bool := false) (regionless : Bool :=
  false) :
    Option String := Id.run do
  -- Every account state after the call is a read-back region with its count word and a region
  -- before, or a `frame` (the region bytes outside the projection), or the driver declares that
  -- it builds no loader region (`region = "none"` in driver.toml).
  let mut readBack := false
  for k in ["input", "region"] do
    if let some after := jsonAt case.outcome ["state", k] then
      if (jsonAt after ["accounts"]).isSome then
        readBack := true
        if (jsonAt after ["count"]).isNone then
          return some s!"the read-back region {k} after the call has no account-count word"
        if (regionPairs case).all (·.1 != k) then
          return some s!"the read-back region {k} after the call has no region before the \
            call"
  if let some frame := jsonAt case.outcome ["state", "frame"] then
    unless jsonAt case.state ["frame"] == some frame do
      return some "region bytes no model represents changed: frame"
  else if !readBack && !regionless &&
      ["accounts", "cells"].any (fun k => ((jsonAt case.outcome ["state", k]).bind
        (·.getArr?.toOption)).isSome) then
    return some
      "the state after the call holds accounts without a read-back region or frame; \
        declare region = \"none\" in driver.toml if the driver builds no loader region"
  let bytesOf (j : Option Json) : Option Solanalib.Runtime.Bytes :=
    j.bind fun v => (do parseHex (← v.getStr?) : Result Solanalib.Runtime.Bytes).toOption
  let zero (j : Option Json) : Bool := (bytesOf j).any (·.all (· == 0))
  let len (j : Option Json) : Option Nat := (bytesOf j).map (·.length)
  for (k, before, after) in regionPairs case do
    let fresh := (jsonAt before ["count"]).isNone
    let changed (f : String) : Option String := some
      s!"region bytes no model represents changed: {k}.{f}"
    let entries (j : Json) : Array Json := ((jsonAt j ["accounts"]).bind (·.getArr?.toOption)).getD
      #[]
    let (bs, as) := (entries before, entries after)
    unless bs.size == as.size do
      return changed "accounts length"
    if fresh then
      unless jsonAt after ["count"] == some (Lean.toJson bs.size) do
        return changed "count"
    else
      unless jsonAt before ["count"] == jsonAt after ["count"] do
        return changed "count"
    for f in ["instruction_data", "program_id"] do
      unless jsonAt before [f] == jsonAt after [f] do
        return changed f
    for (i, b, a) in (List.range bs.size).zip (bs.toList.zip as.toList) do
      if (jsonAt a ["duplicate_of"]).isSome then
        -- The 7 padding bytes of a duplicate entry.
        unless (if fresh then zero (jsonAt a ["padding"]) else jsonAt b ["padding"] == jsonAt a
          ["padding"]) do
          return changed s!"accounts[{i}].padding"
      else
        -- The alignment padding and rent epoch of an account. (Its own `padding`
        -- field is the resize delta of the account-view.)
        unless (if fresh then zero (jsonAt a ["alignment_padding"])
                else jsonAt b ["alignment_padding"] == jsonAt a ["alignment_padding"]) do
          return changed s!"accounts[{i}].alignment_padding"
        unless jsonAt b ["rent_epoch"] == jsonAt a ["rent_epoch"] do
          return changed s!"accounts[{i}].rent_epoch"
        unless spareWriter do
          let same := if fresh then
              zero (jsonAt a ["spare"]) && (do
                let n ← len (jsonAt b ["data"])
                let m ← len (jsonAt a ["data"])
                let sp ← len (jsonAt a ["spare"])
                pure (n + reserveLength == m + sp)) == some true
            else jsonAt b ["spare"] == jsonAt a ["spare"]
          unless same do
            return changed
              s!"accounts[{i}].spare (the driver does not declare {case.function} in \
                spare_writes)"
  return none

/-- A function whose calls may change spare bytes, declared by its driver
(`spare_writes` in `driver.toml`): records of `corpus` whose function matches
the glob `function`. -/
structure SpareWriter where
  corpus : String
  function : String

def spareWriterOf (j : Json) : Except String SpareWriter := do
  pure { corpus := ← (← field j "corpus").getStr?, function := ← (← field j "function").getStr? }

/-- Why a listed record does not show its listed divergence, or `none` if it does. -/
def divergenceProblem (d : Divergence) (checker : Checker) (case : Case)
    (verdicts : List ModelVerdict) (perModel : Bool) : Option String :=
  if !checker.decides.contains d.model then
    some s!"listed as a known divergence of {d.model}, but its checker decides \
      {checker.decides}"
  else if !perModel && checker.decides.length > 1 then
    some
      s!"listed as a known divergence of {d.model}, but its checker gives one verdict for \
        {checker.decides}; give per-model verdicts (checkModels)"
  else if verdicts.any (fun v => v.model == d.model && v.admitted) then
    some s!"listed as a known divergence of {d.model}, but that model admits it; remove \
      the listing"
  else if verdicts.any (fun v => v.model != d.model && !v.admitted) then
    some
      s!"listed as a known divergence of {d.model}, but \
        {(verdicts.filter (fun v => v.model != d.model && !v.admitted)).map (·.model)} \
        reject it too"
  else if d.exit.any (· != recordedExit case) then
    some s!"listed with exit {d.exit.getD ""}, but the recorded exit is {recordedExit case}"
  else if d.reasonContains.any (fun r => !containsText (recordedReason case) r) then
    some
      s!"listed with a reason containing {repr (d.reasonContains.getD "")}, but the \
        recorded reason is {repr (recordedReason case)}"
  else none

def corpusSchema : String := "solana-library-conformance/corpus/v1"

def caseOf (corpus : String) (j : Json) : Except String Case := do
  let generics ← match ← field j "generics" with
    | .obj kvs => kvs.toList.mapM fun (k, v) => return (k, ← v.getStr?)
    | other => throw s!"generics must be an object, got {other.compress}"
  return {
    corpus
    id := ← (← field j "id").getStr?
    function := ← (← field j "function").getStr?
    generics
    layout := (j.getObjVal? "layout").toOption
    state := ← field j "state"
    args := ← field j "args"
    outcome := ← field j "outcome" }

/-- `Json` objects are sorted by key; the generics of the record keep the declaration order of the
recorder only in the key text, so compare as sets. -/
def sameGenerics (a b : List (String × String)) : Bool :=
  a.length == b.length && a.all (b.contains ·)

/-- One record outside the selected checker keys. The Python driver derives
these rows only after authenticating the complete unchanged native corpus. -/
structure RecordOmission where
  corpus : String
  id : String
  function : String
  generics : List (String × String)
  deriving Inhabited

def recordOmissionOf (j : Json) : Except String RecordOmission := do
  let generics ← match ← field j "generics" with
    | .obj kvs => kvs.toList.mapM fun (k, v) => return (k, ← v.getStr?)
    | other => throw s!"generics must be an object, got {other.compress}"
  return {
    corpus := ← (← field j "corpus").getStr?
    id := ← (← field j "id").getStr?
    function := ← (← field j "function").getStr?
    generics }

def runCorpus (dir : System.FilePath) (name : String) (checkers : List Checker)
    (divergences : List Divergence := []) (spareWriters : List SpareWriter := [])
    (regionless : List String := []) (omissions : List RecordOmission := []) :
    IO (Nat × List (String × Tally)) := do
  let divs := (divergences.filter (·.corpus == name)).toArray
  let writers := (spareWriters.filter (·.corpus == name)).toArray
  let mut written : Array Nat := writers.map fun _ => 0
  let mut used : Array Nat := divs.map fun _ => 0
  let path := dir / s!"{name}.json"
  unless ← path.pathExists do
    IO.eprintln s!"FAIL {name}: missing corpus file {path}"
    return (1, [])
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok j => pure j
    | .error e => IO.eprintln s!"FAIL {name}: invalid JSON: {e}"; return (1, [])
  let header : Except String (Array Json) := do
    unless (← (← field json "schema").getStr?) == corpusSchema do throw "unknown schema"
    unless (← (← field json "corpus").getStr?) == name do throw "corpus name differs from \
      file name"
    (← field json "records").getArr?
  let records ← match header with
    | .ok r => pure r
    | .error e => IO.eprintln s!"FAIL {name}: {e}"; return (1, [])
  let mut failures := 0
  let checkerArray := checkers.toArray
  let omitted := (omissions.filter (·.corpus == name)).toArray
  let mut omittedUses : Array Nat := omitted.map fun _ => 0
  if !omitted.isEmpty && checkers.isEmpty then
    failures := failures + 1
    IO.eprintln s!"FAIL {name}: no registered checker keys selected"
  for omission in omitted do
    if (omitted.toList.filter (·.id == omission.id)).length != 1 then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}/{omission.id}: duplicate record omission"
    if checkers.any (fun c => c.function == omission.function && sameGenerics c.generics
      omission.generics) then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}/{omission.id}: a registered checker cannot be omitted"
  let mut tallies : Array Tally := checkerArray.map fun c => { reference := c.reference }
  for record in records do
    match caseOf name record with
    | .error e =>
      failures := failures + 1
      IO.eprintln s!"FAIL {name}: unreadable record: {e}"
    | .ok case =>
      if let some j := omitted.findIdx? (·.id == case.id) then
        let omission := omitted[j]!
        if omission.function != case.function || !sameGenerics omission.generics case.generics then
          failures := failures + 1
          IO.eprintln
            s!"FAIL {case.corpus}/{case.id}: no registered checker; omitted identity \
              changed"
        else
          omittedUses := omittedUses.set! j (omittedUses[j]!.succ)
        continue
      let found := checkerArray.findIdx? fun c =>
        c.function == case.function && sameGenerics c.generics case.generics
      match found, found.bind (checkerArray[·]?) with
      | some i, some checker =>
        let tally := tallies[i]?.getD { reference := checker.reference }
        let writer := writers.findIdx? fun w => globMatch w.function.toList case.function.toList
        if let some j := writer then written := written.set! j (written[j]!.succ)
        match (unmodelledRegionProblem case writer.isSome (regionless.contains name)).map
          Except.error
            |>.getD (modelVerdicts checker case) with
        | .error e =>
          failures := failures + 1
          tallies := tallies.set! i { tally with total := tally.total + 1 }
          IO.eprintln s!"FAIL {case.corpus}/{case.id}: {e}"
        | .ok (verdicts, expected, perModel) =>
          let listed := divs.findIdx? fun d => globMatch d.records.toList case.id.toList
          match listed, listed.bind (divs[·]?) with
          | some j, some d =>
            used := used.set! j (used[j]!.succ)
            match divergenceProblem d checker case verdicts perModel with
            | some problem =>
              tallies := tallies.set! i { tally with total := tally.total + 1 }
              failures := failures + 1
              IO.eprintln s!"FAIL {case.corpus}/{case.id}: {problem}"
            | none =>
              tallies := tallies.set! i { tally with total := tally.total + 1, divergent :=
                tally.divergent + 1 }
          | _, _ =>
          let admitted := verdicts.all (·.admitted)
          tallies := tallies.set! i { tally with total := tally.total + 1, admitted :=
            tally.admitted + (if admitted then 1 else 0) }
          unless admitted do
            failures := failures + 1
            let rejecting := (verdicts.filter (!·.admitted)).map (·.model)
            IO.eprintln
              s!"MISMATCH {case.corpus}/{case.id} ({checker.reference}; rejected by \
                {rejecting})"
            IO.eprintln s!"  state:    {case.state.compress}"
            IO.eprintln s!"  args:     {case.args.compress}"
            IO.eprintln s!"  recorded: {case.outcome.compress}"
            IO.eprintln s!"  model:    {expected.compress}"
      | _, _ =>
        failures := failures + 1
        IO.eprintln s!"FAIL {case.corpus}/{case.id}: no registered checker for {case.key}"
  for (omission, n) in omitted.toList.zip omittedUses.toList do
    if n != 1 then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}/{omission.id}: omitted record occurred {n} times, \
        expected once"
  if !omitted.isEmpty then
    IO.println s!"OMITTED\t{name}\t{omittedUses.foldl (· + ·) 0}"
  for (d, n) in divs.toList.zip used.toList do
    if n == 0 then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}: known divergence `{d.records}` ({d.model}) matches no \
        record"
  for (w, n) in writers.toList.zip written.toList do
    if n == 0 then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}: spare_writes `{w.function}` matches no record"
  let pairs := checkerArray.toList.zip tallies.toList
  for (checker, tally) in pairs do
    if tally.total == 0 then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}: no records for {checker.key}"
  return (failures, pairs.map fun (c, t) => (c.key, t))


/-- Options after the corpus directory: `--only a,b`, `--registered`,
`--divergences FILE` (a JSON list of `{corpus, records, model, reason}`),
`--spare-writes FILE` (a JSON list of `{corpus, function}`), `--regionless FILE`
(a JSON list of corpora whose drivers build no loader region).
`--describe-checkers` emits exact keys without reading corpus records.
`--omit-records FILE` lists authenticated identities outside those keys. -/
structure Options where
  only : Option (List String) := none
  registered : Bool := false
  describeCheckers : Bool := false
  omissions : Option System.FilePath := none
  divergences : Option System.FilePath := none
  spareWrites : Option System.FilePath := none
  regionless : Option System.FilePath := none

partial def parseOptions (opts : Options) : List String → Except String Options
  | [] => pure opts
  | "--only" :: names :: rest => parseOptions { opts with only := some (names.splitOn ",") } rest
  | "--registered" :: rest => parseOptions { opts with registered := true } rest
  | "--describe-checkers" :: rest => parseOptions { opts with describeCheckers := true } rest
  | "--omit-records" :: file :: rest => parseOptions { opts with omissions := some file } rest
  | "--divergences" :: file :: rest => parseOptions { opts with divergences := some file } rest
  | "--spare-writes" :: file :: rest => parseOptions { opts with spareWrites := some file } rest
  | "--regionless" :: file :: rest => parseOptions { opts with regionless := some file } rest
  | other :: _ => throw s!"unknown option {other}"

def runMain (registry : List (String × List Checker)) (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "corpus"
  let opts ← match parseOptions {} (args.drop 1) with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let only : Option (List String) :=
    if opts.registered then some (registry.map (·.1)) else opts.only
  if opts.describeCheckers then
    let described := match only with
      | none => registry
      | some names => registry.filter (names.contains ·.1)
    let rows := described.flatMap fun (name, checkers) => checkers.map fun c =>
      Json.mkObj [("corpus", Json.str name), ("function", Json.str c.function),
        ("generics", Json.mkObj (c.generics.map fun (k, v) => (k, Json.str v)))]
    IO.println ("CHECKERS\t" ++ (Json.arr rows.toArray).compress)
    return 0
  let omissions ← match opts.omissions with
    | none => pure []
    | some file => do
      let text ← IO.FS.readFile file
      let parsed : Except String (List RecordOmission) := do
        (← (← Json.parse text).getArr?).toList.mapM recordOmissionOf
      match parsed with
      | .ok rows => pure rows
      | .error e => IO.eprintln s!"FAIL {file}: {e}"; return 1
  let divergences ← match opts.divergences with
    | none => pure []
    | some file => do
      let text ← IO.FS.readFile file
      let parsed : Except String (List Divergence) := do
        (← (← Json.parse text).getArr?).toList.mapM divergenceOf
      match parsed with
      | .ok ds => pure ds
      | .error e => IO.eprintln s!"FAIL {file}: {e}"; return 1
  let spareWriters ← match opts.spareWrites with
    | none => pure []
    | some file => do
      let text ← IO.FS.readFile file
      let parsed : Except String (List SpareWriter) := do
        (← (← Json.parse text).getArr?).toList.mapM spareWriterOf
      match parsed with
      | .ok ws => pure ws
      | .error e => IO.eprintln s!"FAIL {file}: {e}"; return 1
  let regionless ← match opts.regionless with
    | none => pure []
    | some file => do
      let text ← IO.FS.readFile file
      let parsed : Except String (List String) := do
        (← (← Json.parse text).getArr?).toList.mapM (·.getStr?)
      match parsed with
      | .ok names => pure names
      | .error e => IO.eprintln s!"FAIL {file}: {e}"; return 1
  let mut failures := 0
  let mut total := 0
  let mut divergent := 0
  let selected := match only with
    | none => registry
    | some names => registry.filter (names.contains ·.1)
  -- Registry entries: each corpus once.
  let names := registry.map (·.1)
  for name in names.eraseDups do
    if names.count name > 1 then
      failures := failures + 1
      IO.eprintln s!"FAIL {name}: registered by more than one family"
  for omission in omissions do
    unless selected.any (·.1 == omission.corpus) do
      failures := failures + 1
      IO.eprintln s!"FAIL {omission.corpus}: omitted record belongs to a corpus that is \
        not checked"
  for d in divergences do
    unless selected.any (·.1 == d.corpus) do
      failures := failures + 1
      IO.eprintln
        s!"FAIL {d.corpus}: known divergence `{d.records}` for a corpus that is not checked"
  if let some requested := only then
    for name in requested do
      unless registry.any (·.1 == name) do
        failures := failures + 1
        IO.eprintln s!"FAIL {name}: no registered checkers for the requested corpus"
  else
    -- Every corpus file must be registered.
    for entry in ← dir.readDir do
      if entry.fileName.endsWith ".json" && !(← entry.path.isDir) then
        let stem := (entry.fileName.dropEnd 5).toString
        unless registry.any (·.1 == stem) do
          failures := failures + 1
          IO.eprintln s!"FAIL {entry.fileName}: corpus file without registered checkers"
  for (name, checkers) in selected do
    let (f, tallies) ← runCorpus dir name checkers divergences spareWriters regionless omissions
    failures := failures + f
    IO.println s!"{name}"
    for (key, t) in tallies do
      total := total + t.total
      divergent := divergent + t.divergent
      let mark := if t.admitted + t.divergent == t.total && t.total > 0 then "ok  " else
        "FAIL"
      let known := if t.divergent > 0 then s!" [{t.divergent} known divergent]" else ""
      IO.println s!"  {mark} {t.admitted}/{t.total}{known}  {key}  -> {t.reference}"
  if failures == 0 then
    let except := if divergent > 0 then
      s!", except {divergent} known divergences rejected as listed" else ""
    if opts.omissions.isSome then
      IO.println
        s!"All {total} selected records admitted by the registered references{except}; \
          {omissions.length} authenticated records omitted."
    else
      IO.println s!"All {total} records admitted by the registered references{except}."
    return 0
  else
    IO.eprintln s!"{failures} failure(s) in {total} records."
    return 1

end SolanalibTest.Conformance.Library
