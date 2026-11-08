/-
Copyright (c) 2026 Git Lun Mak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BalancedTernary.Lemmas
import BalancedTernary.Arithmetic
import Mathlib.Data.Set.Function

/-!
# Balanced ternary as a bijection

The capstone correctness result: `ofDigits` restricted to length-`k` digit
lists over `{-1, 0, 1}` is a bijection onto the symmetric integer range
`[-(3^k - 1)/2, (3^k - 1)/2]`.

This is the balanced-ternary analogue of `Nat.bijOn_ofDigits` /
`Nat.setInvOn_digitsAppend_ofDigits` in
`Mathlib.Data.Nat.Digits.Lemmas`, which establishes the parallel fact for
unsigned base-`b` digit lists onto `{n | n < b ^ l}`. There is no existing
Mathlib precedent for the *signed*, symmetric-range version — this is new
content, not a port.
-/

namespace BalTernary

open Set

/-- The set of length-`k` lists with entries in `{-1, 0, 1}`.
Analogue of the set `{L : List ℕ | L.length = l ∧ ∀ x ∈ L, x < b}` used
throughout `Nat.Digits.Lemmas`'s bijection section. -/
def digitLists (k : ℕ) : Set (List ℤ) :=
  {L | L.length = k ∧ ∀ d ∈ L, IsDigit d}

/-- The symmetric integer range representable by exactly `k` balanced
ternary digits. Analogue of `{n | n < b ^ l}`. -/
def symRange (k : ℕ) : Set ℤ :=
  {n | 2 * |n| ≤ 3 ^ k - 1}

/-- Zero-padding `digits n` up to length `k` gives an (in general
non-canonical) `k`-digit representation of `n`.
Analogue of `Nat.digitsAppend`. -/
def digitsAppend (k : ℕ) (n : ℤ) : List ℤ :=
  digits n ++ List.replicate (k - (digits n).length) 0

theorem length_digitsAppend {k : ℕ} {n : ℤ} (hn : n ∈ symRange k) :
    (digitsAppend k n).length = k := by
  unfold digitsAppend
  rw [List.length_append, List.length_replicate]
  exact Nat.add_sub_of_le (digits_length_le hn)
  -- Via digits_length_le (Lemmas.lean) to get (digits n).length ≤ k,
  -- then List.length_append/length_replicate + Nat.add_sub_cancel'.

theorem isDigit_of_mem_digitsAppend {k : ℕ} {n : ℤ} {d : ℤ}
    (hd : d ∈ digitsAppend k n) : IsDigit d := by
  unfold digitsAppend at hd
  rcases List.mem_append.mp hd with hd | hd
  · exact isDigit_of_mem_digits hd
  · exact (List.mem_replicate.mp hd).2 ▸ isDigit_zero
  -- `d` is either in `digits n` (use `isDigit_of_mem_digits`, Lemmas.lean)
  -- or in the padding `List.replicate _ 0`, hence `d = 0`.

theorem mapsTo_ofDigits (k : ℕ) : MapsTo ofDigits (digitLists k) (symRange k) :=
  fun _ h => abs_ofDigits_le h.2 |>.trans_eq (by rw [h.1])

theorem mapsTo_digitsAppend (k : ℕ) : MapsTo (digitsAppend k) (symRange k) (digitLists k) :=
  fun _ h => ⟨length_digitsAppend h, fun _ hd => isDigit_of_mem_digitsAppend hd⟩

theorem injOn_ofDigits (k : ℕ) : InjOn ofDigits (digitLists k) :=
  fun _ h1 _ h2 h => ofDigits_inj_of_len_eq (h1.1.trans h2.1.symm) h1.2 h2.2 h

/-- `digitsAppend k` is a two-sided inverse of `ofDigits` between
`digitLists k` and `symRange k`.
Analogue of `Nat.setInvOn_digitsAppend_ofDigits`. -/
theorem setInvOn_digitsAppend_ofDigits (k : ℕ) :
    InvOn (digitsAppend k) ofDigits (digitLists k) (symRange k) := by
  constructor
  · intro L hL
    have heq : L = digitsAppend k (ofDigits L) := by
      apply injOn_ofDigits k hL (mapsTo_digitsAppend k (mapsTo_ofDigits k hL))
      rw [digitsAppend, ofDigits_append_zeros]
      simp [ofDigits_digits]
    exact heq.symm
  · exact fun n hn => by
      simp [digitsAppend, ofDigits_append_zeros, ofDigits_digits]
  -- Left inverse: for L ∈ digitLists k, show digitsAppend k (ofDigits L) = L
  -- via injOn_ofDigits, reducing to showing both sides evaluate equally
  -- under ofDigits (digits_ofDigits-style argument + ofDigits_append_zeros,
  -- from Arithmetic.lean).
  -- Right inverse: for n ∈ symRange k, digitsAppend k n unfolds via
  -- ofDigits_append_zeros + ofDigits_digits to give ofDigits (digitsAppend k n) = n.

/-- **Main bijection theorem.** `ofDigits` maps `digitLists k` bijectively
onto `symRange k`. Analogue of `Nat.bijOn_ofDigits`. This is the
headline correctness result for the whole project: it is the precise,
formal sense in which "balanced ternary is a positional number system"
on a symmetric range — with **no existing Mathlib analogue** for signed
digit sets. -/
theorem bijOn_ofDigits (k : ℕ) : BijOn ofDigits (digitLists k) (symRange k) :=
  (setInvOn_digitsAppend_ofDigits k).bijOn (mapsTo_ofDigits k) (mapsTo_digitsAppend k)

/-- The reverse bijection, `digitsAppend k` from `symRange k` to
`digitLists k`. Analogue of `Nat.bijOn_digitsAppend`. -/
theorem bijOn_digitsAppend (k : ℕ) : BijOn (digitsAppend k) (symRange k) (digitLists k) :=
  (bijOn_ofDigits k).symm (setInvOn_digitsAppend_ofDigits k).symm

/-- Corollary: every `n` in the symmetric range of radius `k` has a
(possibly non-canonical, zero-padded) `k`-digit representation. -/
theorem exists_digitList_of_mem_symRange {n : ℤ} {k : ℕ} (hn : n ∈ symRange k) :
    ∃ L ∈ digitLists k, ofDigits L = n :=
  ⟨digitsAppend k n, mapsTo_digitsAppend k hn, (setInvOn_digitsAppend_ofDigits k).2 hn⟩

end BalTernary
