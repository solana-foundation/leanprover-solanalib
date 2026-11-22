/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Memory
public import Solanalib.Runtime.Sysvar
public import Solanalib.Runtime.Prims

@[expose] public section

/-!
# Syscalls

Requests carry values. A source argument in private memory is passed as bytes, and
the answer carries the bytes for each destination argument, which the program writes.
An argument inside the input region is accessed by the program through the loads and
stores of `Solanalib.Runtime.Memory`, before or after the syscall; the address of a
destination is part of the request where the runtime checks it.

DEVIATION: in configurations S and D the runtime touches a syscall destination inside
account data before the syscall computes, which can grow the account even when the
syscall then writes nothing (for example `sol_get_sysvar` returning 1); the model
grows the account at the store that the program performs with the answer.
The selected mainnet configuration L has no such translation-triggered growth.
Even there, a correspondence requires successful pointer translation, the actual
output-write protocol and the contracts of the supplied primitives. An arbitrary
value request does not establish those premises.

The memory syscalls `sol_memmove_`, `sol_memset_` and `sol_memcmp_` decompose into such
accesses, and `sol_memcpy_` keeps its overlap check. Logs retain abstract byte
arguments; they do not reproduce the textual formatting of runtime logs.
See [syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives)
for the Agave 4.3.2 handlers and the limitations of other feature combinations.
-/

namespace Solanalib.Runtime

/-- The hash functions handled by the selected Agave 4.3.2 syscall interface. -/
inductive HashAlg where
  | sha256
  | keccak256
  | blake3
  | sha512
  deriving DecidableEq, Repr

/-- The digest width of each hash syscall: `SyscallHash` in Agave 4.3.2 writes
`size_of::<H::Output>()` bytes. The width laws of `Prims` give these widths. -/
def HashAlg.width : HashAlg → Nat
  | .sha256 | .keccak256 | .blake3 => 32
  | .sha512 => 64

/-- `check_aligned` in Agave. `InvokeContext::get_check_aligned` in Agave 4.3.2
`program-runtime/src/invoke_context.rs` holds unless the owner of the program is
`bpf_loader_deprecated`, the owner that selects ABI `v0` (`abiOfOwner`). Where it holds,
the syscalls reject a pointer argument that is not aligned for its type, as the alignment
check of `sol_get_*_sysvar` in `sysStep` does for ABI `v1`. -/
def Abi.checkAligned : Abi → Bool
  | .v0 => false
  | .v1 => true

/-- Agave checks alignment exactly for ABI `v1`. -/
theorem Abi.checkAligned_eq (abi : Abi) : abi.checkAligned = (abi == .v1) := by
  cases abi <;> rfl

/-- An account meta of a CPI instruction, with the flag bytes as the program wrote them. -/
structure CpiMeta where
  key : Pubkey
  signerByte : Nat
  writableByte : Nat
  deriving DecidableEq, Repr

/-- The instruction of a CPI (`StableInstruction` or `SolInstruction`). -/
structure CpiInstruction where
  programId : Pubkey
  metas : List CpiMeta
  data : Bytes
  deriving DecidableEq, Repr

/-- An account info of a CPI: the key, the four pointers the runtime reads, the length
word, and the values at the pointers, following the translation stages of
`cpi_common` in Agave 4.3.2. See [CPI](../../source-notes/agave-4.3.2.md#cpi).
The values matter only for a pointer outside the input region, which the
pointer-check switch rejects. -/
structure CpiAccountInfo where
  key : Pubkey
  keyAddr : Nat
  ownerAddr : Nat
  lamportsAddr : Nat
  dataAddr : Nat
  /-- The slice length in the data `RefCell`, or the field `data_len` of `SolAccountInfo`. -/
  dataLen : Nat
  /-- The `RefCell`s and the length word lie below `MM_INPUT_START`. -/
  boxesBelowInput : Bool
  lamportsVal : Nat
  ownerVal : Pubkey
  dataVal : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- A CPI request (`sol_invoke_signed_c` or `sol_invoke_signed_rust`). -/
structure CpiReq where
  ix : CpiInstruction
  infos : List CpiAccountInfo
  /-- The account-info array ends below `MM_INPUT_START`. -/
  infosBelowInput : Bool
  /-- The signer seeds, one list of seeds per signer. -/
  signers : List (List Bytes)
  deriving DecidableEq, Repr

/-- A syscall request. -/
inductive SysReq where
  | abort
  | panic (file : Bytes) (line col : Nat)
  | log (msg : Bytes)
  | log64 (a b c d e : Nat)
  | logPubkey (key : Bytes)
  | logComputeUnits
  | logData (fields : List Bytes)
  | createProgramAddress (seeds : List Bytes) (programId : Pubkey)
  | tryFindProgramAddress (seeds : List Bytes) (programId : Pubkey) (addrDst bumpDst : Nat)
  | hash (alg : HashAlg) (slices : List Bytes)
  | secp256k1Recover (hash : Bytes) (recoveryId : Nat) (signature : Bytes)
  | poseidon (params endianness : Nat) (inputs : List Bytes)
  | curveValidatePoint (curve : Nat) (point : Bytes)
  | curveGroupOp (curve op : Nat) (left right : Bytes)
  | curveMultiscalarMul (curve : Nat) (scalars points : List Bytes)
  | curveDecompress (curve : Nat) (input : Bytes)
  | curvePairingMap (curve : Nat) (g1 g2 : List Bytes)
  | altBn128GroupOp (op : Nat) (input : Bytes)
  | altBn128Compression (op : Nat) (input : Bytes)
  | bigModExp (base exponent modulus : Bytes)
  | getSysvarTyped (which : TypedSysvar) (dst : Nat)
  | getSysvar (id : Pubkey) (offset len dst : Nat)
  | getEpochStake (vote : Option Pubkey)
  | remainingComputeUnits
  | getStackHeight
  /-- `sol_get_processed_sibling_instruction` with the lengths of the header the program
  passes and the destination ranges for the overlap check. -/
  | getProcessedSibling (index dataLen accountsLen : Nat) (dsts : List (Nat × Nat))
  | setReturnData (data : Bytes)
  | getReturnData (capacity dataDst pidDst : Nat)
  | memcpy (dst src n : Nat)
  | allocFree (size free : Nat)
  | invoke (req : CpiReq)
  deriving Repr

/-- A syscall answer: the value of r0 and the bytes for the destination arguments. -/
structure SysAns where
  r0 : Nat
  out : List Bytes
  deriving DecidableEq, Repr

/-- The represented registration decisions of
`create_program_runtime_environment` in Agave 4.3.2.
The model admits a failing event for an unregistered request. Actual deployment
and symbol resolution require a separate program-cache correspondence; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def SysReq.registered (p : Profile) : SysReq → Bool
  | .hash .blake3 _ => p.features.blake3Syscall
  | .hash .sha512 _ => p.release != .agave_3_1_12 && p.features.sha512Syscall
  | .curveValidatePoint .. | .curveGroupOp .. | .curveMultiscalarMul .. =>
    p.features.curve25519Syscalls
  | .curveDecompress .. | .curvePairingMap .. =>
    p.release != .agave_3_1_12 && p.features.bls12_381Syscalls
  | .getSysvarTyped .lastRestartSlot _ => p.features.lastRestartSlotSysvar
  | .getSysvarTyped .fees _ => !p.features.disableFeesSysvar
  | .getSysvar .. => p.features.getSysvarSyscall
  | .altBn128GroupOp .. => p.features.altBn128Syscall
  | .altBn128Compression .. => p.features.altBn128Compression
  | .poseidon .. => p.features.poseidonSyscall
  | .remainingComputeUnits => p.features.remainingComputeUnitsSyscall
  | .bigModExp .. => p.features.bigModExpSyscall
  | .getEpochStake _ => p.features.epochStakeSyscall
  | _ => true

/-- The raw `is_nonoverlapping` predicate on VM addresses and lengths. Its
arithmetic retains the supplied starts even for an empty range. -/
def nonOverlapping (a an b bn : Nat) : Bool :=
  if b < a then decide (bn ≤ a - b) else decide (an ≤ b - a)

/-- Whether a list of destination ranges is pairwise disjoint. -/
def pairwiseDisjoint : List (Nat × Nat) → Bool
  | [] => true
  | (a, n) :: rest => rest.all (fun (b, m) => nonOverlapping a n b m) && pairwiseDisjoint rest

/-- The output-overlap check of `SyscallGetProcessedSiblingInstruction` in
Agave 4.3.2. `translate_mut!` checks translated host ranges; `translate_slice_inner!`
replaces a zero-length data or account-meta slice with an empty dangling slice,
so its VM start cannot overlap another output. The remaining nonempty ranges
retain the mapped-destination correspondence premise. This normalization applies
only to sibling outputs, not to raw VM-range checks such as `sol_memcpy_`. -/
def siblingOutputsDisjoint (dsts : List (Nat × Nat)) : Bool :=
  pairwiseDisjoint (dsts.filter fun (_, len) => len != 0)

/-- The curve ids that `sol_curve_validate_point` and `sol_curve_group_op` accept:
0 and 1 for curve25519, and the BLS12-381 ids 5 and 6 with or without the big-endian
bit. The selected mainnet profile enables BLS12-381 and aborts on invalid curves;
the disabled-BLS, non-aborting combination has a documented source mismatch in
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def curveIdKnown (p : Profile) (curve : Nat) : Bool :=
  curve == 0 || curve == 1 ||
    (p.release != .agave_3_1_12 && p.features.bls12_381Syscalls &&
      (curve == 5 || curve == 6 || curve == 0x85 || curve == 0x86))

/-- The represented operation codes of `sol_alt_bn128_group_op`. The selected
mainnet profile enables both G2 and little-endian operations. The G2-enabled,
little-endian-disabled combination is narrower here than in Agave 4.3.2; see
[syscalls and primitives](../../source-notes/agave-4.3.2.md#syscalls-and-primitives). -/
def altBn128OpKnown (p : Profile) (op : Nat) : Bool :=
  op == 0 || op == 2 || op == 3 ||
    (p.release != .agave_3_1_12 && p.features.altBn128LittleEndian &&
      (op == 0x80 || op == 0x82 || op == 0x83)) ||
    (p.release != .agave_3_1_12 && p.features.altBn128G2 &&
      (op == 4 || op == 6 ||
        (p.features.altBn128LittleEndian && (op == 0x84 || op == 0x86))))

/-- The operation codes of `sol_alt_bn128_compression` that the profile accepts. -/
def altBn128CompressionOpKnown (p : Profile) (op : Nat) : Bool :=
  op < 4 || (p.release != .agave_3_1_12 && p.features.altBn128LittleEndian &&
    0x80 ≤ op && op < 0x84)

/-- The `index`-th preceding completed instruction with the same parent: the trace is
walked backwards, deeper entries are skipped, the walk stops at a shallower entry, and
the current instruction counts as index 0 of the entries of equal height
(`SyscallGetProcessedSiblingInstruction`, Agave 4.3.2). The logical push-order
trace must correspond to the instruction contexts supplied by the runtime. -/
def findSibling (trace : List TraceEntry) (height index : Nat) : Option TraceEntry :=
  go trace.reverse 0
where
  go : List TraceEntry → Nat → Option TraceEntry
    | [], _ => none
    | e :: es, rev =>
      if e.height < height then none
      else if e.height = height then
        (if index + 1 = rev then some e else go es (rev + 1))
      else go es rev

/-- The account metas of an instruction, as `sol_get_processed_sibling_instruction`
writes them: 34-byte records of key, `is_signer` and `is_writable`. -/
def metaBytes (ts : TxState) (f : Frame) : Bytes :=
  (f.accounts.map fun a => (ts.key a.txIdx).bytes ++ [boolByte a.signer, boolByte
    a.writable]).flatten

/-- The answer `0` with no destination bytes. -/
def SysAns.ok0 : SysAns := ⟨0, []⟩

/-- The common result of a byte-slice hash request. The hash is an abstract
function; only its input concatenation and the slice-count limit are interpreted. -/
def hashReply (maxSlices : Nat) (hash : List Bytes → Bytes) (slices : List Bytes) :
    Except InstrError SysAns :=
  if maxSlices < slices.length then .error .ProgramFailedToComplete
  else .ok ⟨0, [hash slices]⟩

/-- A symbolic hash call returns the application of the supplied abstract function. -/
theorem hashReply_ok (maxSlices : Nat) (hash : List Bytes → Bytes) (slices : List Bytes)
    (bounded : slices.length ≤ maxSlices) :
    hashReply maxSlices hash slices = .ok ⟨0, [hash slices]⟩ := by
  simp only [hashReply, Nat.not_lt.mpr bounded, ite_false]

/-- Shared program-address syscall behavior before checking the output locations. -/
def findAddressReply (P : CryptoPrimitives) (seeds : List Bytes) (programId : Bytes) :
    Except InstrError SysAns :=
  if !seedsOk seeds then .error .ProgramFailedToComplete
  else match findProgramAddressBytes P seeds programId with
    | some (key, bump) => .ok ⟨0, [(Pubkey.ofBytes key).bytes, [UInt8.ofNat bump]]⟩
    | none => .ok ⟨1, []⟩

/-- Shared curve-validation syscall behavior. Primitive implementations remain parameters. -/
def curveValidateReply (p : Profile) (validate : Nat → Bytes → Bool)
    (curve : Nat) (point : Bytes) : Except InstrError SysAns :=
  if !curveIdKnown p curve then
    (if p.features.abortOnInvalidCurve then .error .ProgramFailedToComplete else .ok ⟨1, []⟩)
  else .ok ⟨if validate curve point then 0 else 1, []⟩

/-- Shared byte-range behavior of the generic sysvar getter. Address-space checks
are performed by the runtime before this operation is called. -/
def getSysvarReply (data : Option Bytes) (offset len : Nat) : Except InstrError SysAns :=
  if U64_LIMIT ≤ offset + len then .error .ArithmeticOverflow
  else match data with
    | none => .ok ⟨2, []⟩
    | some bytes =>
      if bytes.length < offset + len then .ok ⟨1, []⟩
      else .ok ⟨0, [slice bytes offset len]⟩

/-- The semantics of every syscall except CPI and `sol_remaining_compute_units`,
whose answer the model leaves free since compute is outside it.
A failure is the instruction error that the syscall raises; every `SyscallError`
becomes `ProgramFailedToComplete` through the error handling in Agave 4.3.2
`program-runtime/src/vm.rs::execute`. The request and result interpretation still
requires the translation and primitive premises stated above. -/
def sysStep (p : Profile) (P : Prims) (sv : Sysvars) (epochStake : Option Pubkey → Nat)
    (c : InvCtx) (st : InvState) : SysReq → Except InstrError (SysAns × InvState)
  | .abort => .error .ProgramFailedToComplete
  | .panic _ _ _ => .error .ProgramFailedToComplete
  | .log msg =>
    if P.isUtf8 msg then .ok (.ok0, { st with logs := st.logs ++ [msg] })
    else .error .ProgramFailedToComplete
  | .log64 a b c' d e =>
    .ok (.ok0, { st with logs := st.logs ++ [u64le a ++ u64le b ++ u64le c' ++ u64le d ++ u64le e]
      })
  | .logPubkey key => .ok (.ok0, { st with logs := st.logs ++ [key] })
  | .logComputeUnits => .ok (.ok0, st)
  | .logData fields => .ok (.ok0, { st with logs := st.logs ++ [fields.flatten] })
  | .createProgramAddress seeds pid =>
    if MAX_SEEDS < seeds.length || seeds.any (fun s => decide (MAX_SEED_LEN < s.length)) then
      .error .ProgramFailedToComplete
    else match createProgramAddress P seeds pid with
      | .ok k => .ok (⟨0, [k.bytes]⟩, st)
      | .error _ => .ok (⟨1, []⟩, st)
  | .tryFindProgramAddress seeds pid addrDst bumpDst =>
    match findAddressReply P.toCryptoPrimitives seeds pid.bytes with
    | .error error => .error error
    | .ok answer =>
      if answer.r0 = 0 && !nonOverlapping addrDst 32 bumpDst 1 then .error .ProgramFailedToComplete
      else .ok (answer, st)
  | .hash alg slices =>
    let hash := match alg with
      | .sha256 => fun bytes => P.sha256 bytes.flatten
      | .keccak256 => P.keccak256
      | .blake3 => P.blake3
      | .sha512 => P.sha512
    match hashReply p.maxHashSlices hash slices with
    | .error error => .error error
    | .ok answer => .ok (answer, st)
  | .secp256k1Recover h rid sig =>
    match P.secp256k1Recover h rid sig with
    | .ok key => .ok (⟨0, [key]⟩, st)
    | .error code => .ok (⟨code, []⟩, st)
  | .poseidon params endianness inputs =>
    if params ≠ 0 || 1 < endianness then .error .ProgramFailedToComplete
    else if 12 < inputs.length then .error .ProgramFailedToComplete
    else match P.poseidon params endianness inputs with
      | some h => .ok (⟨0, [h]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .curveValidatePoint curve point =>
    match curveValidateReply p P.validatePoint curve point with
    | .error error => .error error
    | .ok answer => .ok (answer, st)
  | .curveGroupOp curve op l r =>
    if !curveIdKnown p curve || 2 < op then
      (if p.features.abortOnInvalidCurve then .error .ProgramFailedToComplete else .ok (⟨1, []⟩,
        st))
    else match P.curveGroupOp curve op l r with
      | some out => .ok (⟨0, [out]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .curveMultiscalarMul curve scalars points =>
    if 512 < scalars.length then .error .ProgramFailedToComplete
    else if !(curve == 0 || curve == 1) then
      (if p.features.abortOnInvalidCurve then .error .ProgramFailedToComplete else .ok (⟨1, []⟩,
        st))
    else match P.curveMultiscalarMul curve scalars points with
      | some out => .ok (⟨0, [out]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .curveDecompress curve input =>
    if !(curve == 5 || curve == 6 || curve == 0x85 || curve == 0x86) then
      .error .ProgramFailedToComplete
    else match P.curveDecompress curve input with
      | some out => .ok (⟨0, [out]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .curvePairingMap curve g1 g2 =>
    if !(curve == 4 || curve == 0x84) then .error .ProgramFailedToComplete
    else match P.curvePairingMap curve g1 g2 with
      | some out => .ok (⟨0, [out]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .altBn128GroupOp op input =>
    if !altBn128OpKnown p op then .error .ProgramFailedToComplete
    else match P.altBn128GroupOp op input with
      | some out => .ok (⟨0, [out]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .altBn128Compression op input =>
    if !altBn128CompressionOpKnown p op then .error .ProgramFailedToComplete
    else match P.altBn128Compression op input with
      | some out => .ok (⟨0, [out]⟩, st)
      | none => .ok (⟨1, []⟩, st)
  | .bigModExp b e m =>
    if 512 < b.length || 512 < e.length || 512 < m.length then .error .ProgramFailedToComplete
    else if p.release = .agave_4_3_2 then
      match P.bigModExpLe b e m with
      | none => .error .ProgramFailedToComplete
      | some output => .ok (⟨0, [output]⟩, st)
    else .ok (⟨0, [P.bigModExp b e m]⟩, st)
  | .getSysvarTyped which dst =>
    if p.release != .agave_3_1_12 && c.abi == .v0 then .error .ProgramFailedToComplete
    else if p.features.pointerChecks && decide (MM_INPUT_START ≤ dst) then
      .error .ProgramFailedToComplete
    else if c.abi == .v1 && dst % (which.sizeAlign).2 != 0 then .error .ProgramFailedToComplete
    else match which.value sv with
      | some bytes => .ok (⟨0, [bytes]⟩, st)
      | none => .error .UnsupportedSysvar
  | .getSysvar id offset len dst =>
    if p.release != .agave_3_1_12 && c.abi == .v0 then .error .ProgramFailedToComplete
    else if p.features.pointerChecks && decide (MM_INPUT_START ≤ dst) then
      .error .ProgramFailedToComplete
    else if U64_LIMIT ≤ dst + len then .error .ArithmeticOverflow
    else match getSysvarReply (sv.data id) offset len with
      | .error error => .error error
      | .ok answer => .ok (answer, st)
  | .getEpochStake vote => .ok (⟨epochStake vote, []⟩, st)
  | .remainingComputeUnits => .error .ProgramFailedToComplete
  | .getStackHeight => .ok (⟨st.ts.stack.length, []⟩, st)
  | .getProcessedSibling index dataLen accountsLen dsts =>
    match findSibling st.ts.trace st.ts.stack.length index with
    | none => .ok (⟨0, []⟩, st)
    | some e =>
      if e.frame.data.length = dataLen ∧ e.frame.accounts.length = accountsLen then
        if !siblingOutputsDisjoint dsts then .error .ProgramFailedToComplete
        else .ok (⟨1, [u64le dataLen ++ u64le accountsLen, (st.ts.key e.frame.programIdx).bytes,
          e.frame.data, metaBytes st.ts e.frame]⟩, st)
      else .ok (⟨1, [u64le e.frame.data.length ++ u64le e.frame.accounts.length]⟩, st)
  | .setReturnData data =>
    if MAX_RETURN_DATA < data.length then .error .ProgramFailedToComplete
    else .ok (.ok0, { st with ts := { st.ts with
      returnData := (st.ts.key c.frame.programIdx, data) } })
  | .getReturnData cap dataDst pidDst =>
    let (pid, d) := st.ts.returnData
    let m := min cap d.length
    if 0 < m then
      if !nonOverlapping dataDst m pidDst 32 then .error .ProgramFailedToComplete
      else .ok (⟨d.length, [d.take m, pid.bytes]⟩, st)
    else .ok (⟨d.length, []⟩, st)
  | .memcpy dst src n =>
    if 0 < n && !nonOverlapping dst n src n then .error .ProgramFailedToComplete
    else .ok (.ok0, st)
  | .allocFree size free =>
    if free ≠ 0 then .ok (.ok0, st)
    else
      let align := if c.abi == .v1 then 8 else 1
      let start := (st.heapPos + align - 1) / align * align
      if c.heapSize < start + size then .ok (.ok0, st)
      else .ok (⟨MM_HEAP_START + start, []⟩, { st with heapPos := start + size })
  | .invoke _ => .error .ProgramFailedToComplete

/-- A hash request that succeeds answers status `0` and one digest of the width of the algorithm,
by the width laws of `Prims`, and changes no state. -/
theorem sysStep_hash {p : Profile} {P : Prims} {sv : Sysvars} {es : Option Pubkey → Nat}
    {c : InvCtx} {st st' : InvState} {alg : HashAlg} {slices : List Bytes} {ans : SysAns}
    (h : sysStep p P sv es c st (.hash alg slices) = .ok (ans, st')) :
    st' = st ∧ ans.r0 = 0 ∧ ∃ digest, ans.out = [digest] ∧ digest.length = alg.width := by
  by_cases over : p.maxHashSlices < slices.length
  · cases alg <;> simp [sysStep, hashReply, over] at h
  · cases alg <;> simp only [sysStep, hashReply, over, ite_false, Except.ok.injEq,
      Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      exact ⟨rfl, rfl, _, rfl, by simp [HashAlg.width, P.sha256_length, P.keccak256_length,
        P.blake3_length, P.sha512_length]⟩

/-- A syscall other than CPI leaves the accounts and the counters unchanged. -/
theorem sysStep_accts {p : Profile} {P : Prims} {sv : Sysvars} {es : Option Pubkey → Nat}
    {c : InvCtx} {st st' : InvState} {req : SysReq} {ans : SysAns}
    (h : sysStep p P sv es c st req = .ok (ans, st')) :
    st'.ts.accts = st.ts.accts ∧ st'.ts.keys = st.ts.keys ∧
    st'.ts.lamportsDelta = st.ts.lamportsDelta ∧ st'.ts.resizeDelta = st.ts.resizeDelta ∧
    st'.ts.stack = st.ts.stack ∧ st'.ts.trace = st.ts.trace ∧ st'.ts.topIndex = st.ts.topIndex ∧
    st'.buf = st.buf := by
  cases req <;> simp only [sysStep] at h <;>
    (repeat' split at h) <;> (try cases h) <;> simp

/-- Ordinary syscalls preserve the touched-account set. -/
theorem sysStep_touched {p : Profile} {P : Prims} {sv : Sysvars} {es : Option Pubkey → Nat}
    {c : InvCtx} {st st' : InvState} {req : SysReq} {ans : SysAns}
    (h : sysStep p P sv es c st req = .ok (ans, st')) :
    st'.ts.touched = st.ts.touched := by
  cases req <;> simp only [sysStep] at h <;>
    (repeat' split at h) <;> (try cases h) <;> simp

end Solanalib.Runtime
