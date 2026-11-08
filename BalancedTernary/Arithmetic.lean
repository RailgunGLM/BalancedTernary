/-
Copyright (c) 2026 Git Lun Mak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BalancedTernary.Lemmas

/-!
# Arithmetic properties of balanced ternary digits

Lemmas describing how `digits`/`ofDigits` interact with `+`, `*`, `-`, and
list operations. Modelled on the corresponding section of
`Mathlib.Data.Nat.Digits.Lemmas` (`ofDigits_append`,
`ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq`,
`digits_base_mul`, `ofDigits_mod_pow_eq_ofDigits_take`, etc.), adapted
for signed digits where the carry behaviour differs from the unsigned
case.

The headline result with **no unsigned analogue** is `digits_neg`: because
`{-1, 0, 1}` is closed under negation (unlike `{0, ..., b-1}` for `b > 1`),
balanced ternary enjoys a clean sign-flip law that ordinary positional
systems lack.
-/

namespace BalTernary

/-- `ofDigits` distributes over list append as `L₁ ++ L₂ ↦ ofDigits L₁ +
3 ^ L₁.length * ofDigits L₂`. Analogue of `Nat.ofDigits_append`. -/
theorem ofDigits_append (L₁ L₂ : List ℤ) :
    ofDigits (L₁ ++ L₂) = ofDigits L₁ + 3 ^ L₁.length * ofDigits L₂ := by
  induction L₁ with
  | nil => simp
  | cons d L ih =>
      simp only [List.cons_append, ofDigits_cons, List.length_cons, pow_succ]
      rw [ih]
      ring
  -- Induction on L₁, using ofDigits_cons and pow_succ.

/-- Negating every digit negates the represented value. -/
theorem ofDigits_neg (L : List ℤ) : ofDigits (L.map Neg.neg) = -ofDigits L := by
  induction L with
  | nil => simp
  | cons d L ih =>
      simp only [List.map_cons, ofDigits_cons]
      rw [ih]
      ring
  -- Induction on L: ofDigits_cons + ring.

/-- **Negation symmetry** (no analogue in the unsigned `Nat.digits`
setting): the canonical digits of `-n` are exactly the negated digits of
`n`. This is the key structural advantage of a *signed*-digit system. -/
theorem digits_neg (n : ℤ) : digits (-n) = (digits n).map Neg.neg := by
  let L := digits n
  have hL : WellFormed L := wellFormed_digits n
  have hmap : WellFormed (L.map Neg.neg) := by
    constructor
    · intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
      exact IsDigit.neg (hL.1 e he)
    · intro hne
      have hlast := hL.2 (by simpa using hne)
      rw [List.getLast_map]
      intro hz
      apply hlast
      simpa using hz
  calc
    digits (-n) = digits (ofDigits (L.map Neg.neg)) := by
      rw [ofDigits_neg, ofDigits_digits]
    _ = L.map Neg.neg := digits_ofDigits _ hmap
    _ = (digits n).map Neg.neg := rfl

/-- Multiplying by 3 shifts the digit list right by one (prepends a `0`),
as long as the result is then re-canonicalised. Analogue of
`Nat.digits_base_mul`-style shift lemmas. -/
theorem digits_three_mul (n : ℤ) (hn : n ≠ 0) :
    digits (3 * n) = 0 :: digits n := by
  have hdigits : WellFormed (digits n) := wellFormed_digits n
  have htail : digits n ≠ [] := by simp [digits_eq_nil_iff, hn]
  have hWF : WellFormed (0 :: digits n) := by
    constructor
    · intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact isDigit_zero
      · exact isDigit_of_mem_digits hd
    · intro hne
      rw [List.getLast_cons htail]
      exact hdigits.2 htail
  calc
    digits (3 * n) = digits (ofDigits (0 :: digits n)) := by
      congr 1
      simp [ofDigits_digits n]
    _ = 0 :: digits n := digits_ofDigits _ hWF

/-- Divisibility by 3: `n` is divisible by `3` iff its units (= head,
little-endian) digit is `0`. Unlike base 10 (where `3 ∣ n` reduces to a
nontrivial digit-sum condition, `Nat.three_dvd_iff`), base 3 makes this
check trivial since every digit *except* the units digit already
contributes a multiple of 3 — included for completeness and as the
base case underlying `digits_three_mul`. -/
theorem three_dvd_iff (n : ℤ) :
    (3 : ℤ) ∣ n ↔ (digits n = [] ∨ (digits n).head? = some 0) := by
  by_cases hn : n = 0
  · simp [hn]
  have hhead : (digits n).head? = some (centerMod n) := by
    rw [digits_eq_cons_centerMod_centerDiv hn]
    rfl
  constructor
  · intro hd
    right
    rw [hhead]
    have hmod : n % 3 = 0 := Int.emod_eq_zero_of_dvd hd
    simp [centerMod, hmod]
  · intro h
    have hhead' : (digits n).head? = some 0 := by
      rcases h with hnil | hhead'
      · exact (hn (by simpa [digits_eq_nil_iff] using hnil)).elim
      · exact hhead'
    rw [hhead] at hhead'
    have hcenter : centerMod n = 0 := by simpa using hhead'
    have hmod : n % 3 = 0 := by
      unfold centerMod at hcenter
      split_ifs at hcenter <;> omega
    exact Int.dvd_iff_emod_eq_zero.mpr hmod

/-- **Digit-sum test for divisibility by 2.** Since `3 ≡ 1 [ZMOD 2]`,
`n` is even iff the sum of its balanced ternary digits is even — direct
analogue of `Nat.modEq_digits_sum`/`Nat.dvd_iff_dvd_digits_sum`
specialized to base `3`, modulus `2`. -/
theorem modEq_digit_sum_two (n : ℤ) : n ≡ (digits n).sum [ZMOD 2] := by
  have aux : ∀ L : List ℤ, ofDigits L ≡ L.sum [ZMOD 2] := by
    intro L
    induction L with
    | nil => simp
    | cons d L ih =>
        rw [ofDigits_cons, List.sum_cons]
        have hthree : (3 : ℤ) ≡ 1 [ZMOD 2] := by norm_num [Int.ModEq]
        have hmul := hthree.mul ih
        simpa using (Int.ModEq.refl d).add hmul
  simpa [ofDigits_digits] using aux (digits n)

theorem two_dvd_iff (n : ℤ) : (2 : ℤ) ∣ n ↔ (2 : ℤ) ∣ (digits n).sum := by
  have h := modEq_digit_sum_two n
  constructor
  · intro hn
    apply Int.modEq_zero_iff_dvd.mp
    exact h.symm.trans (Int.modEq_zero_iff_dvd.mpr hn)
  · intro hs
    apply Int.modEq_zero_iff_dvd.mp
    exact h.trans (Int.modEq_zero_iff_dvd.mpr hs)

/-- Sum of two digit lists of equal length, componentwise, evaluates via
`ofDigits` additively — the balanced-ternary analogue of
`Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq`. Note: the
result list need *not* be a valid digit list (entries may be in
`{-2,...,2}`), so this is stated for raw `ℤ` lists, not `IsDigit`-bounded
ones; re-canonicalising such a "raw sum" back into balanced ternary is a
separate carry-propagation lemma left for future work. -/
theorem ofDigits_add_of_length_eq {L₁ L₂ : List ℤ} (h : L₁.length = L₂.length) :
    ofDigits L₁ + ofDigits L₂ = ofDigits (List.zipWith (· + ·) L₁ L₂) := by
  induction L₁ generalizing L₂ with
  | nil =>
      cases L₂ with
      | nil => simp
      | cons b L₂ => simp at h
  | cons a L₁ ih =>
      cases L₂ with
      | nil => simp at h
      | cons b L₂ =>
          have htail : L₁.length = L₂.length := by simpa using h
          simp only [ofDigits_cons]
          change a + 3 * ofDigits L₁ + (b + 3 * ofDigits L₂) =
            (a + b) + 3 * ofDigits (List.zipWith (· + ·) L₁ L₂)
          calc
            a + 3 * ofDigits L₁ + (b + 3 * ofDigits L₂) =
                (a + b) + 3 * (ofDigits L₁ + ofDigits L₂) := by ring
            _ = (a + b) + 3 * ofDigits (List.zipWith (· + ·) L₁ L₂) := by
              rw [ih htail]
  -- Induction on L₁ and L₂ simultaneously using h; ofDigits_cons + ring.

/-- Scaling a digit list by an integer scalar `c` scales the represented
value by `c`. Analogue of `Nat.mul_ofDigits`. -/
theorem mul_ofDigits (c : ℤ) (L : List ℤ) :
    c * ofDigits L = ofDigits (L.map (c * ·)) := by
  induction L with
  | nil => simp
  | cons d L ih =>
      simp only [List.map_cons, ofDigits_cons]
      rw [mul_add]
      calc
        c * d + c * (3 * ofDigits L) =
            c * d + 3 * (c * ofDigits L) := by ring
        _ = c * d + 3 * ofDigits (L.map (c * ·)) := by rw [ih]
  -- Induction on L: ofDigits_cons on both sides + ring. (Note: unlike the
  -- Nat version, the mapped list need not consist of valid digits, e.g.
  -- c = 2 turns {-1,0,1} into {-2,0,2} — this lemma is purely about raw
  -- `ofDigits` evaluation, not a statement about canonical representations.)

/-- Zero-padding a digit list on the high (little-endian tail) end does
not change its value. Shared helper used in `Bijection.lean`; stated
here since it's a general `ofDigits`/list-append fact.
Analogue of `Nat.ofDigits_append_replicate_zero`. -/
theorem ofDigits_append_zeros (L : List ℤ) (m : ℕ) :
    ofDigits (L ++ List.replicate m 0) = ofDigits L := by
  rw [ofDigits_append]
  have hz : ofDigits (List.replicate m 0) = 0 := by
    induction m with
    | zero => simp
    | succ m ih => simp [List.replicate_succ, ih]
  simp [hz]
  -- Via ofDigits_append: ofDigits (L ++ replicate m 0)
  --   = ofDigits L + 3 ^ L.length * ofDigits (replicate m 0),
  -- and ofDigits (replicate m 0) = 0 by a short induction on m.

end BalTernary
