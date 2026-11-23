/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.World
import SolanalibTest.Conformance.Library.Families.Anchor.OwnedGraph
import Solanalib.Specs.AnchorLang.construct

/-!
# `Account`, `InterfaceAccount` and `AccountLoader` construction

`try_from` of the three wrappers is decided against the primary owned model
(`AnchorConstructOwned.run`, errors in the registered reference heap focused
in the auxiliary state) and the observation model (`AnchorAccount.construct`).
Their generic `Owner`, `CheckOwner` and `AccountDeserialize` callbacks are the script of the
record (`rust/anchor/src/script.rs`): the k-th call of a callback logs
itself, applies the owner assignment of step k (and, for the decoder, lamports
store) to the account under construction, then panics with
`"script <callback>"` or returns the value of the step; scripted errors are boxed
`ProgramError`s. The auxiliary state holds the current owners of the distinct
accounts (`ownerAt`) and the callback log.

Observation: cell contents and leases, owners and log after the call, and the
result. The decoded value and the AccountInfo of a returned wrapper are
observed (its `Rc` and owner identities); the owner copy of `InterfaceAccount` is a
private field without accessor and is not observed. Errors are observed by
value (owned: the current contents of the returned Box).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor.Construct

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
  SolanalibTest.Conformance.Library.Runtime

/-! ## Scripts -/

structure OwnerStep where
  returns : Solanalib.Runtime.Pubkey
  assign : Option Solanalib.Runtime.Pubkey
  panic : Bool

structure CheckStep where
  err : Option ProgramError.Value
  assign : Option Solanalib.Runtime.Pubkey
  panic : Bool

structure DecodeStep where
  result : Except ProgramError.Value UInt64
  assign : Option Solanalib.Runtime.Pubkey
  lamports : Option UInt64
  panic : Bool

/-- A script and its target: the account under construction (owner
reference and lamports cell). -/
structure Script where
  owner : List OwnerStep
  check : List CheckStep
  decode : List DecodeStep
  target : Nat
  lamportsCell : Nat

def asOwnerStep (j : Json) : Result OwnerStep := do
  pure ⟨← keyField j "returns", ← asOption asPubkey (← field j "assign"), ← boolField j
    "panic"⟩

def asCheckStep (j : Json) : Result CheckStep := do
  pure ⟨← asOption asProgramError (← field j "err"), ← asOption asPubkey (← field j "assign"),
    ← boolField j "panic"⟩

def asDecodeStep (j : Json) : Result DecodeStep := do
  pure ⟨← asExcept asProgramError asU64 (← field j "result"), ← asOption asPubkey (← field j
    "assign"),
    ← asOption asU64 (← field j "lamports"), ← boolField j "panic"⟩

def asScript (j : Json) (info : AccountInfo.Value) : Result Script := do
  pure ⟨← asList asOwnerStep (← field j "owner"), ← asList asCheckStep (← field j
    "check_owner"),
    ← asList asDecodeStep (← field j "deserialize"), info.ownerRef.id, info.lamports.cell⟩

/-- Callback log events. `try_deserialize_unchecked` logs its own event; the decoder callback of the
model is `try_deserialize`, so the scripts never log it. -/
inductive Event where
  | owner
  | checkOwner (ref : Nat)
  | deserialize (bytes : Solanalib.Runtime.Bytes)
  | deserializeUnchecked (bytes : Solanalib.Runtime.Bytes)
  deriving DecidableEq

def asEvent (j : Json) : Result Event := do
  let (k, v) ← asTagged j
  match k with
  | "owner" => pure .owner
  | "check_owner" => pure (.checkOwner (← v.getNat?))
  | "deserialize" => pure (.deserialize (← asBytes v))
  | "deserialize_unchecked" => pure (.deserializeUnchecked (← asBytes v))
  | other => throw s!"unknown callback event {other}"

def eventJson : Event → Json
  | .owner => tagged "owner" .null
  | .checkOwner r => tagged "check_owner" (toJson r)
  | .deserialize b => tagged "deserialize" (bytesJson b)
  | .deserializeUnchecked b => tagged "deserialize_unchecked" (bytesJson b)

/-- Current owners of the distinct accounts and the callback log. -/
structure CAux where
  owners : List Solanalib.Runtime.Pubkey
  log : List Event
  deriving DecidableEq

def CAux.ownerAt (aux : CAux) (ref : AccountInfo.OwnerRef) : Solanalib.Runtime.Pubkey :=
  aux.owners.getD ref.id .zero

def CAux.calls (aux : CAux) (p : Event → Bool) : Nat := aux.log.countP p

def isOwner : Event → Bool | .owner => true | _ => false
def isCheck : Event → Bool | .checkOwner _ => true | _ => false
def isDecode : Event → Bool | .deserialize _ => true | _ => false

def CAux.assign (aux : CAux) (target : Nat) : Option Solanalib.Runtime.Pubkey → CAux
  | none => aux
  | some k => { aux with owners := aux.owners.set target k }

def CAux.push (aux : CAux) (e : Event) : CAux := { aux with log := aux.log ++ [e] }

def exhausted : String := "script exhausted"

/-! ## Scripted callbacks, generic in the auxiliary state -/

/-- Where the callbacks find the script state, and how a scripted
`ProgramError` becomes the error value of the model (allocating it if owned). -/
structure Shape where
  Aux : Type
  Err : Type
  Terminal : Type
  get : Aux → CAux
  set : Aux → CAux → Aux
  boxError : AccountInfo.State × Aux → ProgramError.Value →
    Outcome (AccountInfo.State × Aux) Err String Terminal

variable (sh : Shape) (sc : Script)

def ownerFn (s : AccountInfo.State × sh.Aux) (_ : Unit) :
    Outcome (AccountInfo.State × sh.Aux) Solanalib.Runtime.Pubkey String sh.Terminal :=
  let c := sh.get s.2
  let c1 := c.push .owner
  match sc.owner[c.calls isOwner]? with
  | none => .unwound exhausted (s.1, sh.set s.2 c1)
  | some st =>
    let c2 := c1.assign sc.target st.assign
    if st.panic then .unwound "script owner" (s.1, sh.set s.2 c2) else .returned st.returns (s.1,
      sh.set s.2 c2)

def checkFn (s : AccountInfo.State × sh.Aux) (ref : AccountInfo.OwnerRef) :
    Outcome (AccountInfo.State × sh.Aux) (Except sh.Err Unit) String sh.Terminal :=
  let c := sh.get s.2
  let c1 := c.push (.checkOwner ref.id)
  match sc.check[c.calls isCheck]? with
  | none => .unwound exhausted (s.1, sh.set s.2 c1)
  | some st =>
    let s2 := (s.1, sh.set s.2 (c1.assign sc.target st.assign))
    if st.panic then .unwound "script check_owner" s2
    else match st.err with
      | none => .returned (.ok ()) s2
      | some e => Outcome.map Except.error (sh.boxError s2 e)

def storeLamports (state : AccountInfo.State) (cell : Nat) : Option UInt64 → AccountInfo.State
  | none => state
  | some v => (Borrow.replaceCell state ⟨cell⟩ (.lamports v)).2

def decodeFn {Decoded : Type} (mk : Except sh.Err UInt64 → Decoded)
    (s : AccountInfo.State × sh.Aux) (args : DecodeArgs) :
    Outcome (AccountInfo.State × sh.Aux) Decoded String sh.Terminal :=
  let c := sh.get s.2
  let c1 := c.push (.deserialize args.bytes)
  match sc.decode[c.calls isDecode]? with
  | none => .unwound exhausted (s.1, sh.set s.2 c1)
  | some st =>
    let s2 := (storeLamports s.1 sc.lamportsCell st.lamports, sh.set s.2 (c1.assign sc.target
      st.assign))
    if st.panic then .unwound "script deserialize" s2
    else match st.result with
      | .ok n => .returned (mk (.ok n)) s2
      | .error e => Outcome.map (fun err => mk (.error err)) (sh.boxError s2 e)

/-! ## Graph combinators specific to the constructors -/

theorem pgraph_ite {O : Type} (c : Prop) [Decidable c] {P Q : O → Prop} {x y : Option O}
    (hp : PGraph P x) (hq : PGraph Q y) : PGraph (fun o => if c then P o else Q o) (if c then x
      else y) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact hp
  · simp only [h, ↓reduceIte]; exact hq

theorem widen_graph {S A V U T : Type} {cb : Callback.Run S A V U T} {f : Option (Outcome S V U T)}
    {b : S} {a : A} (h : PGraph (cb b a) f) : PGraph (widenCallback cb b a) (f.map widen) :=
  PGraph.exists_eq widen h

theorem rcLift_graph {S A V U T : Type} {run : Callback.Run S A V Empty T} {f : Option (Outcome S V
  Empty T)}
    {b : S} {a : A} (h : PGraph (run b a) f) :
    PGraph (AccountInfoRc.lift (Unwind := U) run b a) (f.map AccountInfoRc.liftOutcome) :=
  PGraph.exists_eq _ h

def resultK {S E F L U T : Type} (g : F → S → Option (Outcome S (Except E L) U T)) :
    Except E F → S → Option (Outcome S (Except E L) U T)
  | .error e, s => some (.returned (.error e) s)
  | .ok v, s => g v s

theorem resultBind_graph {S A F L U T : Type}
    {first : Callback.Run S A (Except Error F) U T}
    {next : F → S → Outcome S (Except Error L) U T → Prop} {f : Option (Outcome S (Except Error F)
      U T)}
    {g : F → S → Option (Outcome S (Except Error L) U T)} {b : S} {a : A}
    (hf : PGraph (first b a) f) (hn : ∀ v s, PGraph (next v s) (g v s)) :
    PGraph (resultBind first next b a) (f.bind (PGraph.bindK (resultK g))) := by
  apply PGraph.bind hf
  intro r s
  cases r with
  | error e => exact PGraph.eq_left _
  | ok v => exact hn v s

theorem effectsBind_graph {S A E F L U T : Type}
    {first : Callback.Run S A (Except E F) U T}
    {next : F → S → Outcome S (Except E L) U T → Prop} {f : Option (Outcome S (Except E F) U T)}
    {g : F → S → Option (Outcome S (Except E L) U T)} {b : S} {a : A}
    (hf : PGraph (first b a) f) (hn : ∀ v s, PGraph (next v s) (g v s)) :
    PGraph (AnchorEffects.resultBind first next b a) (f.bind (PGraph.bindK (resultK g))) := by
  apply PGraph.bind hf
  intro r s
  cases r with
  | error e => exact PGraph.eq_left _
  | ok v => exact hn v s

theorem withGuard_graph {Aux A V U T : Type} (guard : Borrow.Guard)
    {run : Callback.Run (World Aux) A V U T} {f : Option (Outcome (World Aux) V U T)}
    {b : World Aux} {a : A} (h : PGraph (run b a) f) :
    PGraph (AnchorEffects.withGuard guard run b a) (f.bind
      (AccountInfo.GuardCallback.releaseOutcome guard)) :=
  PGraph.exists_opt _ h

/-! ## Observation model (`AnchorAccount.construct`) -/

def obsShape : Shape where
  Aux := CAux
  Err := Error
  Terminal := Empty
  get := id
  set := fun _ c => c
  boxError := fun s e => .returned (programError e) s

def obsIndex (sc : Script) : ConstructorIndex where
  Aux := CAux
  Payload := UInt64
  Unwind := String
  Terminal := Empty
  discriminator := [1, 2, 3, 4, 5, 6, 7, 8]
  ownerAt := CAux.ownerAt
  owner := Callback.ofFunction (ownerFn obsShape sc)
  checkOwner := Callback.ofFunction (checkFn obsShape sc)
  deserialize := Callback.ofFunction (decodeFn obsShape sc (fun r => (⟨r, []⟩ : Decoded UInt64)))

abbrev OW := World CAux
abbrev OOut (V : Type) := Outcome OW V (ConstructorUnwind String) (ConstructorTerminal Empty)

def obsOwnerCheckFn (before : OW) (args : AccountInfo.Args) : Option (OOut (Except Error Unit)) :=
  (some (widen (ownerFn obsShape sc before ()))).bind (PGraph.bindK fun expected after =>
    let observed := CAux.ownerAt after.2 args.info.ownerRef
    if observed = expected then some (.returned (.ok ()) after)
    else (some (widen (ownerFn obsShape sc after ()))).map (Outcome.map fun diagnostic =>
      Except.error ((error .ownedByWrongProgram).replaceCompared (.pubkeys observed diagnostic))))

theorem obsOwnerCheck_graph (before : OW) (args : AccountInfo.Args) :
    PGraph (ownerCheck (obsIndex sc) before args) (obsOwnerCheckFn sc before args) := by
  apply PGraph.bind (widen_graph (PGraph.ofFunction _ before ()))
  intro expected after
  exact pgraph_ite _ (PGraph.eq_left _) (PGraph.map _ (widen_graph (PGraph.ofFunction _ after ())))

def obsDecodeFn (before : OW) (args : AccountInfo.Args) : Option (OOut (Except Error UInt64)) :=
  match AccountInfo.tryBorrowData before.1 args with
  | (.error failure, during) => some (.returned (.error (programError failure)) (during, before.2))
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      (some (decodeFn obsShape sc (fun r => (⟨r, []⟩ : Decoded UInt64)) (during, before.2)
          ⟨args.info, guard, bytes⟩)).bind fun produced =>
        AccountInfo.GuardCallback.releaseOutcome guard (Outcome.map Decoded.result (widen produced))

theorem obsDecode_graph (before : OW) (args : AccountInfo.Args) :
    PGraph (decodeAccount (obsIndex sc) before args) (obsDecodeFn sc before args) := by
  unfold decodeAccount obsDecodeFn
  rcases AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · exact PGraph.eq_left _
  · dsimp only
    rcases Borrow.current during guard with e | ⟨view, content⟩
    · exact PGraph.false
    · rcases content with l | bytes
      · exact PGraph.false
      · exact PGraph.exists_opt _ (PGraph.ofFunction _ _ _)

def obsLoaderDataFn (before : OW) (args : AccountInfo.Args) : Option (OOut (Except Error Unit)) :=
  match AccountInfo.tryBorrowData before.1 args with
  | (.error failure, during) => some (.returned (.error (programError failure)) (during, before.2))
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      AccountInfo.GuardCallback.releaseOutcome guard
        (.returned (discriminatorCheck (obsIndex sc).discriminator bytes) (during, before.2))

theorem obsLoaderData_graph (before : OW) (args : AccountInfo.Args) :
    PGraph (checkLoaderData (obsIndex sc) before args) (obsLoaderDataFn sc before args) := by
  unfold checkLoaderData obsLoaderDataFn
  rcases AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · exact PGraph.eq_left _
  · dsimp only
    rcases Borrow.current during guard with e | ⟨view, content⟩
    · exact PGraph.false
    · rcases content with l | bytes
      · exact PGraph.false
      · exact PGraph.ofOption _

def obsAccountFn (before : OW) (args : AccountInfo.Args) : Option (OOut (Except Error (Account
  UInt64))) :=
  (initialized (Unwind := String) (Terminal := Empty) CAux.ownerAt before args).bind
    (PGraph.bindK (resultK fun _ after =>
      (obsOwnerCheckFn sc after args).bind (PGraph.bindK (resultK fun _ checked =>
        (obsDecodeFn sc checked args).map (Outcome.map (Except.map fun value => Account.mk value
          args.info))))))

theorem obsAccount_graph (before : OW) (args : AccountInfo.Args) :
    PGraph (construct .account (obsIndex sc) before args) (obsAccountFn sc before args) :=
  resultBind_graph (PGraph.ofOption _) fun _ after =>
    resultBind_graph (obsOwnerCheck_graph sc after args) fun _ checked =>
      PGraph.map _ (obsDecode_graph sc checked args)

def obsInterfaceFn (before : OW) (args : AccountInfo.Args) :
    Option (OOut (Except Error (InterfaceAccount UInt64))) :=
  (initialized (Unwind := String) (Terminal := Empty) CAux.ownerAt before args).bind
    (PGraph.bindK (resultK fun _ after =>
      (some (widen (checkFn obsShape sc after args.info.ownerRef))).bind (PGraph.bindK (resultK fun
        _ checked =>
        (obsDecodeFn sc checked args).bind (PGraph.bindK fun decoded afterDecode =>
          some (.returned (decoded.map fun value => InterfaceAccount.mk ⟨value, args.info⟩
            (CAux.ownerAt afterDecode.2 args.info.ownerRef)) afterDecode))))))

theorem obsInterface_graph (before : OW) (args : AccountInfo.Args) :
    PGraph (construct .interfaceAccount (obsIndex sc) before args) (obsInterfaceFn sc before args)
      :=
  resultBind_graph (PGraph.ofOption _) fun _ after =>
    resultBind_graph (widen_graph (PGraph.ofFunction _ after _)) fun _ checked =>
      PGraph.bind (obsDecode_graph sc checked args) fun _ _ => PGraph.eq_left _

def obsLoaderFn (before : OW) (args : AccountInfo.Args) : Option (OOut (Except Error (Loader
  UInt64))) :=
  (obsOwnerCheckFn sc before args).bind (PGraph.bindK (resultK fun _ checked =>
    (obsLoaderDataFn sc checked args).map (Outcome.map (Except.map fun _ => Loader.mk args.info))))

theorem obsLoader_graph (before : OW) (args : AccountInfo.Args) :
    PGraph (construct .loader (obsIndex sc) before args) (obsLoaderFn sc before args) :=
  resultBind_graph (obsOwnerCheck_graph sc before args) fun _ checked =>
    PGraph.map _ (obsLoaderData_graph sc checked args)

/-! ## Primary owned model (`AnchorConstructOwned.run`) -/

abbrev Heap := AnchorErrorOwned.Reference.State
abbrev BoxId := AnchorErrorOwned.Reference.BoxId
abbrev StringId := AnchorErrorOwned.Reference.StringId
abbrev Failure := AnchorErrorOwned.Reference.Failure
abbrev OAux := Heap × CAux

def heapFocus : Owned.Focus (World OAux) Heap := Owned.Focus.snd.comp Owned.Focus.fst

def ownedOps : AnchorErrorOwned.Ops (World OAux) StringId BoxId Failure :=
  AnchorErrorOwned.Reference.ops.focus heapFocus

def ownedFn : OpsFn (World OAux) StringId BoxId Failure := RefFn.fn.focus heapFocus

theorem ownedGraph : OpsGraph ownedOps ownedFn := RefFn.graph.focus heapFocus

/-- A scripted error is a boxed `ProgramError` in the heap. -/
def boxProgram (s : World OAux) (e : ProgramError.Value) :
    Outcome (World OAux) (AnchorErrorOwned.Error BoxId) String Failure :=
  match AnchorErrorOwned.Reference.allocateBox s.2.1 (.program ⟨e, none, none⟩) with
  | .returned b heap => .returned ⟨b⟩ (s.1, (heap, s.2.2))
  | .unwound impossible _ => nomatch impossible
  | .terminated f => .terminated f

def ownedShape : Shape where
  Aux := OAux
  Err := AnchorErrorOwned.Error BoxId
  Terminal := Failure
  get := Prod.snd
  set := fun a c => (a.1, c)
  boxError := boxProgram

def ownedTypes (sc : Script) : AnchorConstructOwned.Types where
  Aux := OAux
  Payload := UInt64
  Unwind := String
  Terminal := Failure
  StringResource := StringId
  BoxResource := BoxId
  errors := ownedOps
  discriminator := [1, 2, 3, 4, 5, 6, 7, 8]
  ownerAt := fun aux ref => aux.2.ownerAt ref
  owner := Callback.ofFunction (ownerFn ownedShape sc)
  checkOwner := Callback.ofFunction (checkFn ownedShape sc)
  deserialize := Callback.ofFunction
    (decodeFn ownedShape sc (fun r => (⟨r, []⟩ : AnchorConstructOwned.Decoded
      (AnchorErrorOwned.Error BoxId) UInt64)))

abbrev W := World OAux
abbrev Out (V : Type) := Outcome W V (ConstructorUnwind String) (ConstructorTerminal Failure)
abbrev OErr := AnchorErrorOwned.Error BoxId

def depFn {V : Type} (x : Option (Outcome W V Empty Failure)) : Option (Out V) :=
  (x.map AccountInfoRc.liftOutcome).map widen

theorem dep_graph {A V : Type} {run : Callback.Run W A V Empty Failure} {x : Option (Outcome W V
  Empty Failure)}
    {b : W} {a : A} (h : PGraph (run b a) x) :
    PGraph (AnchorConstructOwned.dependency (ownedTypes sc) run b a) (depFn x) :=
  widen_graph (rcLift_graph (U := String) h)

def codeFn (before : W) (value : Code) : Option (Out OErr) :=
  depFn (OwnedFn.buildCodeFn ownedFn before ⟨value.payload.name, value.payload.code,
    value.payload.message⟩)

theorem code_graph (before : W) (value : Code) :
    PGraph (AnchorConstructOwned.code (ownedTypes sc) value before ()) (codeFn before value) :=
  dep_graph sc (OwnedFn.buildCode_graph ownedGraph before _)

def programFn (before : W) (value : ProgramError.Value) : Option (Out OErr) :=
  depFn (OwnedFn.fromProgramFn ownedFn before value)

theorem program_graph (before : W) (value : ProgramError.Value) :
    PGraph (AnchorConstructOwned.program (ownedTypes sc) value before ()) (programFn before value)
      :=
  dep_graph sc (OwnedFn.fromProgram_graph ownedGraph before _)

def initFn (before : W) (args : AccountInfo.Args) : Option (Out (Except OErr Unit)) :=
  if before.2.2.ownerAt args.info.ownerRef = systemProgramId then
    match AccountInfo.observe .lamports before.1 args.info with
    | (.malformed, _) => none
    | (.value balance, after) =>
      if balance = 0 then (codeFn (after, before.2) .notInitialized).map (Outcome.map Except.error)
      else some (.returned (.ok ()) (after, before.2))
    | (.borrowFailed, after) =>
      if args.profile.aborts then some (.terminated (.inl .borrowFailed))
      else some (.unwound (.inl .borrowFailed) (after, before.2))
  else some (.returned (.ok ()) before)

theorem init_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.initialized (ownedTypes sc) before args) (initFn before args) := by
  unfold AnchorConstructOwned.initialized initFn
  apply pgraph_ite
  · rcases AccountInfo.observe .lamports before.1 args.info with ⟨result, after⟩
    rcases result with value | _ | _
    · exact pgraph_ite _ (PGraph.map _ (code_graph sc _ _)) (PGraph.eq_left _)
    · exact pgraph_ite _ (PGraph.eq_left _) (PGraph.eq_left _)
    · exact PGraph.false
  · exact PGraph.eq_left _

def dropErrorFn (error : OErr) (before : W) : Option (Outcome W Unit (ConstructorUnwind String)
  (ConstructorTerminal Failure)) :=
  depFn (OwnedFn.dropErrorFn ownedFn ownedOps error before)

def noDoubleFn : W → ConstructorUnwind String → ConstructorUnwind String → Option
  (ConstructorTerminal Failure) :=
  fun _ _ _ => none

def ownedOwnerCheckFn (before : W) (args : AccountInfo.Args) : Option (Out (Except OErr Unit)) :=
  (some (widen (ownerFn ownedShape sc before ()))).bind (PGraph.bindK fun expected after =>
    if after.2.2.ownerAt args.info.ownerRef = expected then some (.returned (.ok ()) after)
    else (codeFn after .ownedByWrongProgram).bind (PGraph.bindK fun error afterBuild =>
      let copied := afterBuild.2.2.ownerAt args.info.ownerRef
      ((some (widen (ownerFn ownedShape sc afterBuild ()))).bind (PGraph.bindK fun diagnostic
        afterOwner =>
          (depFn (OwnedFn.withPubkeysFn ownedFn ownedOps afterOwner (error, copied,
            diagnostic))).map
            (Outcome.map Except.error))).bind
        (PGraph.onUnwindFn noDoubleFn [dropErrorFn error])))

theorem ownedOwnerCheck_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.ownerCheck (ownedTypes sc) before args) (ownedOwnerCheckFn sc
      before args) := by
  apply PGraph.bind (widen_graph (PGraph.ofFunction _ before ()))
  intro expected after
  apply pgraph_ite _ (PGraph.eq_left _)
  apply PGraph.bind (code_graph sc after _)
  intro error afterBuild
  apply PGraph.protect (fun _ _ _ => PGraph.false)
    (PGraph.DropsGraph.cons (d := AnchorConstructOwned.dropError (ownedTypes sc) error)
      (fun s => dep_graph sc (OwnedFn.dropError_graph ownedGraph error s)) PGraph.DropsGraph.nil)
  apply PGraph.bind (widen_graph (PGraph.ofFunction _ afterBuild ()))
  intro diagnostic afterOwner
  exact PGraph.map _ (dep_graph sc (OwnedFn.withPubkeys_graph ownedGraph afterOwner _))

def ownedDecodeFn (before : W) (args : AccountInfo.Args) : Option (Out (Except OErr UInt64)) :=
  match AccountInfo.tryBorrowData before.1 args with
  | (.error failure, during) => (programFn (during, before.2) failure).map (Outcome.map
    Except.error)
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      ((some (widen (decodeFn ownedShape sc
          (fun r => (⟨r, []⟩ : AnchorConstructOwned.Decoded OErr UInt64)) (during, before.2)
          ⟨args.info, guard, bytes⟩))).map (Outcome.map AnchorConstructOwned.Decoded.result)).bind
        (AccountInfo.GuardCallback.releaseOutcome guard)

theorem ownedDecode_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.decodeAccount (ownedTypes sc) before args) (ownedDecodeFn sc
      before args) := by
  unfold AnchorConstructOwned.decodeAccount ownedDecodeFn
  rcases AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · exact PGraph.map _ (program_graph sc _ _)
  · dsimp only
    rcases Borrow.current during guard with e | ⟨view, content⟩
    · exact PGraph.false
    · rcases content with l | bytes
      · exact PGraph.false
      · exact withGuard_graph guard (PGraph.map _ (widen_graph (PGraph.ofFunction _ _ _)))

def loaderCheckFn (bytes : Solanalib.Runtime.Bytes) (state : W) : Option (Out (Except OErr Unit)) :=
  match AnchorConstructOwned.discriminatorFailure [1, 2, 3, 4, 5, 6, 7, 8] bytes with
  | some failure => (codeFn state failure).map (Outcome.map Except.error)
  | none => some (.returned (.ok ()) state)

theorem loaderCheck_graph (bytes : Solanalib.Runtime.Bytes) (state : W) :
    PGraph (AnchorConstructOwned.loaderCheck (ownedTypes sc) bytes state ()) (loaderCheckFn bytes
      state) := by
  unfold AnchorConstructOwned.loaderCheck loaderCheckFn
  dsimp only [ownedTypes]
  rcases AnchorConstructOwned.discriminatorFailure [1, 2, 3, 4, 5, 6, 7, 8] bytes with _ | failure
  · exact PGraph.eq_left _
  · exact PGraph.map _ (code_graph sc _ _)

def ownedLoaderDataFn (before : W) (args : AccountInfo.Args) : Option (Out (Except OErr Unit)) :=
  match AccountInfo.tryBorrowData before.1 args with
  | (.error failure, during) => (programFn (during, before.2) failure).map (Outcome.map
    Except.error)
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      (loaderCheckFn bytes (during, before.2)).bind (AccountInfo.GuardCallback.releaseOutcome guard)

theorem ownedLoaderData_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.checkLoaderData (ownedTypes sc) before args) (ownedLoaderDataFn
      before args) := by
  unfold AnchorConstructOwned.checkLoaderData ownedLoaderDataFn
  rcases AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · exact PGraph.map _ (program_graph sc _ _)
  · dsimp only
    rcases Borrow.current during guard with e | ⟨view, content⟩
    · exact PGraph.false
    · rcases content with l | bytes
      · exact PGraph.false
      · exact withGuard_graph guard (loaderCheck_graph sc bytes _)

def ownedAccountFn (before : W) (args : AccountInfo.Args) : Option (Out (Except OErr (Account
  UInt64))) :=
  (initFn before args).bind (PGraph.bindK (resultK fun _ after =>
    (ownedOwnerCheckFn sc after args).bind (PGraph.bindK (resultK fun _ checked =>
      (ownedDecodeFn sc checked args).map (Outcome.map (Except.map fun value => Account.mk value
        args.info))))))

theorem ownedAccount_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.run .account (ownedTypes sc) before args) (ownedAccountFn sc
      before args) :=
  effectsBind_graph (init_graph sc before args) fun _ after =>
    effectsBind_graph (ownedOwnerCheck_graph sc after args) fun _ checked =>
      PGraph.map _ (ownedDecode_graph sc checked args)

def ownedInterfaceFn (before : W) (args : AccountInfo.Args) :
    Option (Out (Except OErr (InterfaceAccount UInt64))) :=
  (initFn before args).bind (PGraph.bindK (resultK fun _ after =>
    (some (widen (checkFn ownedShape sc after args.info.ownerRef))).bind (PGraph.bindK (resultK fun
      _ checked =>
      (ownedDecodeFn sc checked args).bind (PGraph.bindK fun decoded afterDecode =>
        some (.returned (decoded.map fun value => InterfaceAccount.mk ⟨value, args.info⟩
          (afterDecode.2.2.ownerAt args.info.ownerRef)) afterDecode))))))

theorem ownedInterface_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.run .interfaceAccount (ownedTypes sc) before args)
      (ownedInterfaceFn sc before args) :=
  effectsBind_graph (init_graph sc before args) fun _ after =>
    effectsBind_graph (widen_graph (PGraph.ofFunction _ after _)) fun _ checked =>
      PGraph.bind (ownedDecode_graph sc checked args) fun _ _ => PGraph.eq_left _

def ownedLoaderFn (before : W) (args : AccountInfo.Args) : Option (Out (Except OErr (Loader
  UInt64))) :=
  (ownedOwnerCheckFn sc before args).bind (PGraph.bindK (resultK fun _ checked =>
    (ownedLoaderDataFn checked args).map (Outcome.map (Except.map fun _ => Loader.mk args.info))))

theorem ownedLoader_graph (before : W) (args : AccountInfo.Args) :
    PGraph (AnchorConstructOwned.run .loader (ownedTypes sc) before args) (ownedLoaderFn sc before
      args) :=
  effectsBind_graph (ownedOwnerCheck_graph sc before args) fun _ checked =>
    PGraph.map _ (ownedLoaderData_graph sc checked args)

end SolanalibTest.Conformance.Library.Families.Anchor.Construct
