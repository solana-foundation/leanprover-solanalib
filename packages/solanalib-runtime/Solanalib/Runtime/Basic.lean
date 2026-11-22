/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

@[expose] public section

/-!
# Basic definitions

Byte strings, little-endian integer encodings, slicing and overwriting of byte
strings, and account addresses.

Unsigned integers of the runtime are natural numbers.
A function that stands for a checked operation of Agave returns `Option` or
`Except`, and a field that Agave stores as `u64` carries the bound `< 2 ^ 64` in
the well-formedness predicates that need it.
-/

namespace Solanalib.Runtime

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- The number of values of a `u64`. -/
def U64_LIMIT : Nat := 2 ^ 64

/-- The value `u64::MAX`. -/
def U64_MAX : Nat := 2 ^ 64 - 1

/-! ## Little-endian integers -/

/-- The little-endian encoding of `n` in `k` bytes, reduced modulo `256 ^ k`. -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leBytes k (n / 256)

/-- The little-endian decoding of a byte string. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

@[simp] theorem length_leBytes (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem leNat_leBytes (k n : Nat) : leNat (leBytes k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [leBytes, leNat, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leNat, ih, UInt8.toNat_ofNat']
    have h8 : (2 : Nat) ^ 8 = 256 := rfl
    have hs : 256 ^ (k + 1) = 256 * 256 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h8, Nat.mod_mod, hs, Nat.mod_mul]

theorem leNat_leBytes_of_lt {k n : Nat} (h : n < 256 ^ k) : leNat (leBytes k n) = n := by
  rw [leNat_leBytes, Nat.mod_eq_of_lt h]

theorem leNat_lt (bs : Bytes) : leNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have hb : b.toNat < 256 := b.toNat_lt
    have : 256 * leNat bs ≤ 256 * (256 ^ bs.length - 1) := Nat.mul_le_mul_left _ (by omega)
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    rw [Nat.mul_sub, Nat.mul_one] at this
    rw [Nat.mul_comm (256 ^ bs.length) 256]
    omega

/-- The little-endian encoding of a `u64`. -/
def u64le (n : Nat) : Bytes := leBytes 8 n

/-- The little-endian encoding of a `u32`. -/
def u32le (n : Nat) : Bytes := leBytes 4 n

/-- The little-endian encoding of a `u16`. -/
def u16le (n : Nat) : Bytes := leBytes 2 n

/-- The byte that holds a Boolean as Agave serializes it. -/
def boolByte (b : Bool) : UInt8 := if b then 1 else 0

/-! ## Slicing and overwriting -/

/-- The `len` bytes of `bs` from offset `off`. -/
def slice (bs : Bytes) (off len : Nat) : Bytes := (bs.drop off).take len

/-- The byte string `bs` with the bytes from offset `off` replaced by `src`. -/
def writeAt (bs : Bytes) (off : Nat) (src : Bytes) : Bytes :=
  bs.take off ++ src ++ bs.drop (off + src.length)

theorem length_slice_of_le {bs : Bytes} {off len : Nat} (h : off + len ≤ bs.length) :
    (slice bs off len).length = len := by
  simp [slice, List.length_take, List.length_drop]
  omega

theorem length_writeAt {bs src : Bytes} {off : Nat} (h : off + src.length ≤ bs.length) :
    (writeAt bs off src).length = bs.length := by
  simp [writeAt, List.length_append, List.length_take, List.length_drop]
  omega

theorem slice_writeAt_self {bs src : Bytes} {off : Nat} (h : off + src.length ≤ bs.length) :
    slice (writeAt bs off src) off src.length = src := by
  have ht : (bs.take off).length = off := by simp [List.length_take]; omega
  simp only [slice, writeAt, List.append_assoc]
  rw [List.drop_left' ht, List.take_left' rfl]

theorem slice_writeAt_left {bs src : Bytes} {off o n : Nat}
    (h : off + src.length ≤ bs.length) (hd : o + n ≤ off) :
    slice (writeAt bs off src) o n = slice bs o n := by
  have ht : (bs.take off).length = off := by simp [List.length_take]; omega
  simp only [slice, writeAt, List.append_assoc]
  rw [List.drop_append_of_le_length (by omega)]
  have hl : n ≤ (List.drop o (List.take off bs)).length := by
    simp [List.length_drop, List.length_take]; omega
  rw [List.take_append_of_le_length hl, List.drop_take, List.take_take]
  congr 1
  omega

theorem slice_writeAt_right {bs src : Bytes} {off o n : Nat}
    (h : off + src.length ≤ bs.length) (hd : off + src.length ≤ o) :
    slice (writeAt bs off src) o n = slice bs o n := by
  have hp : (bs.take off ++ src).length = off + src.length := by
    simp [List.length_take]; omega
  simp only [slice, writeAt]
  rw [List.drop_append, hp, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
  congr 2
  omega

theorem slice_append_left {A B : Bytes} {off len : Nat} (h : off + len ≤ A.length) :
    slice (A ++ B) off len = slice A off len := by
  simp only [slice]
  rw [List.drop_append_of_le_length (by omega)]
  exact List.take_append_of_le_length (by simp [List.length_drop]; omega)

theorem slice_append_right {A B : Bytes} {off len : Nat} (h : A.length ≤ off) :
    slice (A ++ B) off len = slice B (off - A.length) len := by
  simp only [slice]
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem slice_all {A : Bytes} : slice A 0 A.length = A := by
  simp [slice]

theorem slice_zero_of_length {A : Bytes} {n : Nat} (h : A.length = n) : slice A 0 n = A := by
  subst h; exact slice_all

theorem slice_slice {A : Bytes} {o1 n1 o2 n2 : Nat} (h : o2 + n2 ≤ n1) :
    slice (slice A o1 n1) o2 n2 = slice A (o1 + o2) n2 := by
  simp only [slice, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

/-- The offset of element `j` in the concatenation of `recs`. -/
def prefixLen (recs : List Bytes) (j : Nat) : Nat := ((recs.take j).map List.length).sum

theorem slice_flatten {recs : List Bytes} {j o n : Nat} (hj : j < recs.length)
    (h : o + n ≤ recs[j].length) :
    slice recs.flatten (prefixLen recs j + o) n = slice recs[j] o n := by
  induction recs generalizing j with
  | nil => simp at hj
  | cons r rs ih =>
    cases j with
    | zero =>
      simp only [prefixLen, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.flatten_cons, List.getElem_cons_zero]
      exact slice_append_left (by simpa using h)
    | succ j =>
      simp only [List.flatten_cons, List.getElem_cons_succ] at h ⊢
      have hp : prefixLen (r :: rs) (j + 1) = r.length + prefixLen rs j := by
        simp [prefixLen, List.take_succ_cons]
      rw [hp, slice_append_right (by omega)]
      have := ih (j := j) (by simp at hj; omega) h
      rw [show r.length + prefixLen rs j + o - r.length = prefixLen rs j + o by omega]
      exact this

theorem prefixLen_le_length {recs : List Bytes} {j : Nat} (hj : j < recs.length) :
    prefixLen recs j + recs[j].length ≤ recs.flatten.length := by
  induction recs generalizing j with
  | nil => simp at hj
  | cons r rs ih =>
    cases j with
    | zero => simp [prefixLen]
    | succ j =>
      have hp : prefixLen (r :: rs) (j + 1) = r.length + prefixLen rs j := by
        simp [prefixLen, List.take_succ_cons]
      have := ih (j := j) (by simp at hj; omega)
      simp only [hp, List.getElem_cons_succ, List.flatten_cons, List.length_append]
      omega

/-- A byte string all of whose bytes are zero, as `is_zeroed` of Agave tests it. -/
def isZeroed (d : Bytes) : Bool := d.all (· == 0)

/-! ## Addresses -/

/-- An account address: 32 bytes. -/
structure Pubkey where
  bytes : Bytes
  length_eq : bytes.length = 32

instance : DecidableEq Pubkey := fun a b =>
  if h : a.bytes = b.bytes then
    isTrue (by cases a; cases b; simp only at h; subst h; rfl)
  else
    isFalse (by intro e; subst e; exact h rfl)

instance : Repr Pubkey := ⟨fun k _ => repr k.bytes⟩

namespace Pubkey

/-- The address of 32 zero bytes, which is the id of the System program. -/
def zero : Pubkey := ⟨List.replicate 32 0, by simp⟩

/-- The address made of the first 32 bytes of `bs`, padded with zeros. -/
def ofBytes (bs : Bytes) : Pubkey :=
  ⟨(bs ++ List.replicate 32 0).take 32, by simp [List.length_take]⟩

theorem ofBytes_bytes (k : Pubkey) : ofBytes k.bytes = k := by
  cases k with
  | mk b h =>
    simp only [ofBytes, mk.injEq]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- The address whose big-endian value is `n`; base58 decoding yields this value. -/
def ofNat (n : Nat) : Pubkey := ⟨(leBytes 32 n).reverse, by simp⟩

end Pubkey

instance : Inhabited Pubkey := ⟨Pubkey.zero⟩

/-- The bytes of a string, in UTF-8. -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## Traversals in the error monad

`mapM`, `forM` and `foldlM` for `Except`, with explicit recursion so that proofs can
unfold them. -/

/-- `List.mapM` for `Except`. -/
def mapE {α β ε : Type} (f : α → Except ε β) : List α → Except ε (List β)
  | [] => .ok []
  | a :: as =>
    match f a with
    | .error e => .error e
    | .ok b =>
      match mapE f as with
      | .error e => .error e
      | .ok bs => .ok (b :: bs)

/-- `List.forM` for `Except`. -/
def forE {α ε : Type} (f : α → Except ε Unit) : List α → Except ε Unit
  | [] => .ok ()
  | a :: as =>
    match f a with
    | .error e => .error e
    | .ok () => forE f as

/-- `List.foldlM` for `Except`. -/
def foldE {α β ε : Type} (f : β → α → Except ε β) : β → List α → Except ε β
  | b, [] => .ok b
  | b, a :: as =>
    match f b a with
    | .error e => .error e
    | .ok b' => foldE f b' as

theorem mapE_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, mapE f l = .ok l' → ∀ y ∈ l', ∃ x ∈ l, f x = .ok y
  | [], l', h, y, hy => by cases h; simp at hy
  | a :: as, l', h, y, hy => by
    unfold mapE at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i bs hbs
        cases h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., hb⟩
        · obtain ⟨x, hx, hfx⟩ := mapE_mem hbs y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem forE_mem {α ε : Type} {f : α → Except ε Unit} :
    ∀ {l : List α}, forE f l = .ok () → ∀ x ∈ l, f x = .ok ()
  | [], _, x, hx => by simp at hx
  | a :: as, h, x, hx => by
    unfold forE at h
    split at h
    · cases h
    · rename_i hfa
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfa
      · exact forE_mem h x hx

/-- Truncation, or extension with zero bytes, to length `n` (`Vec::resize(n, 0)`). -/
def resizeZero (d : Bytes) (n : Nat) : Bytes := d.take n ++ List.replicate (n - d.length) 0

theorem length_resizeZero (d : Bytes) (n : Nat) : (resizeZero d n).length = n := by
  simp [resizeZero, List.length_take]; omega

end Solanalib.Runtime
