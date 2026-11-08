/-
Copyright (c) 2026 Git Lun Mak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BalancedTernary.Defs

/-!
# Correctness theorems for balanced ternary

This is the balanced-ternary analogue of the round-trip and bound lemmas in
`Mathlib.Data.Nat.Digits.Lemmas`:

* `ofDigits_digits`  ↔ `Nat.ofDigits_digits`
* `digits_ofDigits`  ↔ `Nat.digits_ofDigits`
* `digits_injective`/`digits_inj_iff` ↔ `Nat.digits.injective`/`Nat.digits_inj_iff`
* `abs_lt_of_digits_length` / `digits_length_bound` ↔
  `Nat.ofDigits_lt_base_pow_length` / `Nat.lt_base_pow_length_digits`,
  but over the *symmetric* range `[-(3^k-1)/2, (3^k-1)/2]` instead of
  `[0, b^k)`, since balanced ternary digits can be negative.

## References

See `BalancedTernary/Defs.lean` for the proof outline this file formalizes
(constructive existence via repeated centered division, cf. deriveit.net
"Proof of the balanced ternary expansion"; uniqueness statement in the
Wikipedia article "Balanced ternary").
-/

namespace BalTernary

/-- `ofDigits` as an explicit weighted sum, matching the definitional
`foldr`/`cons` recursion to a more "formula-like" shape.
Analogue of `Nat.ofDigits_eq_sum_mapIdx`. -/
theorem ofDigits_eq_sum_mapIdx (L : List ℤ) :
    ofDigits L = ((L.mapIdx fun i a => a * 3 ^ i)).sum := by
  have aux : ∀ (k : ℕ) (L : List ℤ),
      ofDigits L * 3 ^ k =
        (L.mapIdx fun i a => a * 3 ^ (i + k)).sum := by
    intro k L
    induction L generalizing k with
    | nil => simp
    | cons a L ih =>
        simp only [ofDigits_cons, List.mapIdx_cons, List.sum_cons]
        have htail := ih (k + 1)
        simp only [Nat.add_comm, Nat.add_left_comm] at htail ⊢
        rw [add_mul]
        calc
          a * 3 ^ k + 3 * ofDigits L * 3 ^ k =
              a * 3 ^ k + ofDigits L * 3 ^ (k + 1) := by
                rw [pow_succ]
                ring
          _ = a * 3 ^ (k + 0) +
              (L.mapIdx fun i a => a * 3 ^ (k + (i + 1))).sum := by
                rw [htail]
                simp
  simpa using aux 0 L
  -- Induction on L, same shape as Nat.ofDigits_eq_sum_mapIdx /
  -- ofDigits_eq_sum_mapIdx_aux: peeling the head contributes `a₀ * 3⁰`
  -- and reindexes the tail's weights by one.

/-- If a (not necessarily well-formed) digit list evaluates to `0`, every
entry is `0`. Analogue of `Nat.digits_zero_of_eq_zero`; used as the key
uniqueness lemma inside `digits_ofDigits`. -/
theorem isDigit_list_eq_zero_of_ofDigits_eq_zero {L : List ℤ} (h : ∀ d ∈ L, IsDigit d)
    (heq : ofDigits L = 0) : ∀ d ∈ L, d = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha : IsDigit a := h a (by simp)
      have htail : ∀ d ∈ L, IsDigit d := by
        intro d hd
        exact h d (by simp [hd])
      have hzero : a = 0 := by
        rcases ha with rfl | rfl | rfl <;> simp_all [ofDigits_cons] <;> omega
      have heq' : ofDigits L = 0 := by
        rw [ofDigits_cons, hzero] at heq
        omega
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hzero
      · exact ih htail heq' d hd
  -- Induction on L. Cons case `d :: L`: `d + 3 * ofDigits L = 0` forces
  -- `d ≡ 0 [ZMOD 3]` (since `ofDigits L : ℤ` is arbitrary but the
  -- equation pins `d`'s residue), and `|d| ≤ 1 < 3` (from `IsDigit.abs_le_one`)
  -- forces `d = 0` exactly, then `ofDigits L = 0` and apply IH.

/-- **Round-trip theorem (existence direction).**
Evaluating the canonical digits of `n` recovers `n`.
Analogue of `Nat.ofDigits_digits`. -/
theorem ofDigits_digits (n : ℤ) : ofDigits (digits n) = n := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
      by_cases hzero : n = 0
      · simp [hzero]
      · rw [digits_eq_cons_centerMod_centerDiv hzero, ofDigits_cons]
        have hlt : (centerDiv n).natAbs < k := by
          simpa [← hn] using centerDiv_lt_abs n hzero
        rw [ih (centerDiv n).natAbs hlt (centerDiv n) rfl]
        have hs := centerMod_spec n
        omega
  -- Proof sketch: strong induction on n.natAbs.
  -- Unfold `digits n = digitsAux n`; if n = 0 trivial.
  -- Else `digits n = centerMod n :: digits (centerDiv n)`,
  -- apply IH to `centerDiv n` (using `centerDiv_lt_abs`),
  -- then `ofDigits_cons` + `centerMod_spec` closes it by `ring`/`omega`.

/-- Every entry of `digits n` is a valid balanced ternary digit. -/
theorem isDigit_of_mem_digits {n d : ℤ} (hd : d ∈ digits n) : IsDigit d := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
      by_cases hzero : n = 0
      · simp [hzero] at hd
      · rw [digits_eq_cons_centerMod_centerDiv hzero] at hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact centerMod_isDigit n
        · have hlt : (centerDiv n).natAbs < k := by
            simpa [← hn] using centerDiv_lt_abs n hzero
          exact ih (centerDiv n).natAbs hlt hd rfl
  -- Induction following digitsAux's recursive structure; the head is
  -- `centerMod_isDigit`, the tail follows by the induction hypothesis.

/-- `digits n` has no trailing (= last, since little-endian) zero digit,
unless `n = 0` (in which case the list is empty). -/
theorem wellFormed_digits (n : ℤ) : WellFormed (digits n) := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
      by_cases hzero : n = 0
      · simp [hzero, WellFormed]
      · rw [digits_eq_cons_centerMod_centerDiv hzero]
        constructor
        · intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact centerMod_isDigit n
          · have hlt : (centerDiv n).natAbs < k := by
              simpa [← hn] using centerDiv_lt_abs n hzero
            exact isDigit_of_mem_digits hd
        · intro hne
          have hq : WellFormed (digits (centerDiv n)) := by
            apply ih (centerDiv n).natAbs
            · simpa [← hn] using centerDiv_lt_abs n hzero
            · rfl
          by_cases ht : digits (centerDiv n) = []
          · have hlast : (centerMod n :: digits (centerDiv n)).getLast hne =
                centerMod n := by simp [ht]
            rw [hlast]
            intro hr
            have hqzero : centerDiv n = 0 := by
              have hq := congrArg ofDigits ht
              simpa [ofDigits_digits] using hq
            have hs := centerMod_spec n
            omega
          · have hlast := hq.2 ht
            rw [List.getLast_cons ht]
            exact hlast

/-- **Round-trip theorem (uniqueness direction).**
If `L` is a well-formed digit list, then `digits (ofDigits L) = L`.
Analogue of `Nat.digits_ofDigits`. -/
theorem digits_ofDigits (L : List ℤ) (h : WellFormed L) :
    digits (ofDigits L) = L := by
  induction L with
  | nil => simp
  | cons d L ih =>
      have hd : IsDigit d := h.1 d (by simp)
      cases L with
      | nil =>
          have hd0 : d ≠ 0 := by
            simpa [WellFormed] using h.2 (by simp)
          simpa [ofDigits_singleton] using digits_of_isDigit hd hd0
      | cons a L =>
          have htail : WellFormed (a :: L) := by
            constructor
            · intro x hx
              exact h.1 x (by simp [hx])
            · intro hne
              have hlast := h.2 (by simp)
              simpa [List.getLast_cons] using hlast
          have hcond : d ≠ 0 ∨ ofDigits (a :: L) ≠ 0 := by
            by_cases hd0 : d = 0
            · right
              intro hz
              have hall : ∀ x ∈ a :: L, x = 0 :=
                isDigit_list_eq_zero_of_ofDigits_eq_zero htail.1 hz
              have hne : a :: L ≠ [] := by simp
              have hlast := htail.2 hne
              have hmem := hall ((a :: L).getLast hne) (List.getLast_mem hne)
              exact hlast hmem
            · exact Or.inl hd0
          rw [ofDigits_cons, digits_add hd hcond, ih htail]
  -- Proof sketch: induction on L. Nil case trivial (ofDigits [] = 0).
  -- Cons case `d :: L`: show `centerMod (ofDigits (d :: L)) = d` using
  -- `IsDigit d` to pin down the residue class, then
  -- `centerDiv (ofDigits (d :: L)) = ofDigits L`, and close with IH.
  -- The "no trailing zero" hypothesis is needed to distinguish e.g.
  -- `[0]` from `[]`, both evaluating to 0.

/-- `digits` is injective on well-formed lists, hence two *canonical*
digit lists agree iff the integers they represent agree.
Analogue of `Nat.digits.injective`/`Nat.digits_inj_iff`. -/
theorem digits_injective : Function.Injective digits := by
  intro m n h
  calc
    m = ofDigits (digits m) := (ofDigits_digits m).symm
    _ = ofDigits (digits n) := by rw [h]
    _ = n := ofDigits_digits n
  -- Follows from ofDigits_digits: if digits m = digits n then
  -- m = ofDigits (digits m) = ofDigits (digits n) = n.

theorem digits_inj_iff {m n : ℤ} : digits m = digits n ↔ m = n :=
  digits_injective.eq_iff

@[simp] theorem digits_eq_nil_iff {n : ℤ} : digits n = [] ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg ofDigits h
    simpa [ofDigits_digits n] using this
  · intro h
    simp [h]
  -- (←) is `digits_zero`. (→): `ofDigits [] = 0` combined with
  -- `ofDigits_digits`.

theorem digits_ne_nil_iff {n : ℤ} : digits n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff

/-- **Injectivity on fixed-length (not necessarily well-formed) digit
lists.** If two length-equal digit lists with entries in `{-1,0,1}`
evaluate to the same integer, they are equal. This is the key lemma
needed for the symmetric-range bijection in `Bijection.lean` — direct
analogue of `Nat.ofDigits_inj_of_len_eq`. -/
theorem ofDigits_inj_of_len_eq {L₁ L₂ : List ℤ} (hlen : L₁.length = L₂.length)
    (h₁ : ∀ d ∈ L₁, IsDigit d) (h₂ : ∀ d ∈ L₂, IsDigit d)
    (h : ofDigits L₁ = ofDigits L₂) : L₁ = L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
      cases L₂ with
      | nil => rfl
      | cons b L₂ => simp at hlen
  | cons a L₁ ih =>
      cases L₂ with
      | nil => simp at hlen
      | cons b L₂ =>
          have ha : IsDigit a := h₁ a (by simp)
          have hb : IsDigit b := h₂ b (by simp)
          have hab : a = b := by
            rw [ofDigits_cons, ofDigits_cons] at h
            rcases ha with rfl | rfl | rfl <;>
              rcases hb with rfl | rfl | rfl <;> omega
          subst b
          apply congrArg (List.cons a)
          apply ih
          · simpa using hlen
          · intro d hd
            exact h₁ d (by simp [hd])
          · intro d hd
            exact h₂ d (by simp [hd])
          · rw [ofDigits_cons, ofDigits_cons] at h
            omega
  -- Proof sketch (mirrors Nat.ofDigits_inj_of_len_eq): induction on L₁
  -- generalizing L₂. Cons case: from `ofDigits (d₁ :: t₁) = ofDigits (d₂ :: t₂)`
  -- deduce `d₁ ≡ d₂ [ZMOD 3]` (same argument as centerMod uniqueness),
  -- and since both lie in `{-1,0,1}` (width < 3) conclude `d₁ = d₂`;
  -- cancel to get `ofDigits t₁ = ofDigits t₂` and apply IH.

/-! ## Length and magnitude bounds -/

/-- Evaluating any length-`k` digit list (entries in `{-1,0,1}`, not
necessarily well-formed) lands in the symmetric range of radius
`(3 ^ k - 1) / 2`. Analogue of `Nat.ofDigits_lt_base_pow_length`. -/
theorem abs_ofDigits_le {L : List ℤ} (h : ∀ d ∈ L, IsDigit d) :
    2 * |ofDigits L| ≤ 3 ^ L.length - 1 := by
  induction L with
  | nil => simp
  | cons d L ih =>
      have hd : IsDigit d := h d (by simp)
      have htail : ∀ x ∈ L, IsDigit x := by
        intro x hx
        exact h x (by simp [hx])
      have hdabs := IsDigit.abs_le_one hd
      have hbound := ih htail
      have hmul : |3 * ofDigits L| = 3 * |ofDigits L| := by
        by_cases hx : 0 ≤ ofDigits L
        · rw [abs_of_nonneg (by nlinarith), abs_of_nonneg hx]
        · have hx' : ofDigits L < 0 := lt_of_not_ge hx
          rw [abs_of_neg (by nlinarith), abs_of_neg hx']
          ring
      rw [ofDigits_cons, List.length_cons, pow_succ]
      calc
        2 * |d + 3 * ofDigits L| ≤
            2 * (|d| + |3 * ofDigits L|) := by
              gcongr
              exact abs_add_le d (3 * ofDigits L)
        _ = 2 * |d| + 6 * |ofDigits L| := by
              rw [hmul]
              ring
        _ ≤ 3 ^ L.length * 3 - 1 := by
              nlinarith
  -- Induction on L using |ofDigits (d :: L)| ≤ |d| + 3 * |ofDigits L|
  -- (triangle inequality + h gives |d| ≤ 1), then the geometric sum
  -- identity 1 + 3 + 3*(3^k - 1) = 3^(k+1) - 1, closed by `ring`/`omega`.

/-- **Unconditional bound** (no hypothesis on `k`): `n` always fits in the
symmetric range sized by its own canonical digit length.
Direct analogue of `Nat.lt_base_pow_length_digits`. -/
theorem abs_lt_of_digits_length (n : ℤ) :
    2 * |n| ≤ 3 ^ (digits n).length - 1 := by
  calc
    2 * |n| = 2 * |ofDigits (digits n)| := by rw [ofDigits_digits]
    _ ≤ 3 ^ (digits n).length - 1 :=
      abs_ofDigits_le (fun d hd => isDigit_of_mem_digits hd)
  -- Immediate from `abs_ofDigits_le` applied to `digits n`
  -- (using `isDigit_of_mem_digits`) together with `ofDigits_digits`.

/-- **Lower bound.** A well-formed digit list of length `l ≥ 1` (so its
last/leading digit is nonzero) evaluates to something of magnitude at
least `(3 ^ (l - 1) + 1) / 2`, i.e. it genuinely needs all `l` digits.
Analogue of `Nat.pow_length_le_mul_ofDigits` / `Nat.base_pow_length_digits_le`
(the "can't represent an `l`-digit number with fewer digits" direction). -/
theorem abs_ofDigits_ge_of_wellFormed_strong {L : List ℤ} (h : WellFormed L) (hl : L ≠ []) :
    3 ^ (L.length - 1) + 1 ≤ 2 * |ofDigits L| := by
  let P := L.dropLast
  let a := L.getLast hl
  have hdecomp : L = P ++ [a] := by
    exact (List.dropLast_concat_getLast hl).symm
  have hP : ∀ d ∈ P, IsDigit d := by
    intro d hd
    exact h.1 d (by rw [hdecomp]; simp [P, hd])
  have ha : a = -1 ∨ a = 1 := by
    have had := h.1 a (by simp [a])
    have haz := h.2 hl
    change IsDigit a at had
    rcases had with ha | ha | ha
    · exact Or.inl ha
    · exact (haz ha).elim
    · exact Or.inr ha
  have hbound := abs_ofDigits_le hP
  have hlow : -(3 ^ P.length - 1) ≤ 2 * ofDigits P := by
    by_cases hx : 0 ≤ ofDigits P
    · rw [abs_of_nonneg hx] at hbound
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hx)] at hbound
      nlinarith
  have hhigh : 2 * ofDigits P ≤ 3 ^ P.length - 1 := by
    by_cases hx : 0 ≤ ofDigits P
    · rw [abs_of_nonneg hx] at hbound
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hx)] at hbound
      nlinarith
  have hlen : P.length = L.length - 1 := by
    simp [P, List.length_dropLast]
  have happ : ∀ X Y : List ℤ,
      ofDigits (X ++ Y) = ofDigits X + 3 ^ X.length * ofDigits Y := by
    intro X Y
    induction X with
    | nil => simp
    | cons d X ih =>
        simp only [List.cons_append, ofDigits_cons, List.length_cons, pow_succ]
        rw [ih]
        ring
  have hrepr : ofDigits L = ofDigits P + 3 ^ P.length * a := by
    rw [hdecomp, happ]
    simp [a]
  rw [hrepr, ← hlen]
  rcases ha with ha | ha
  · simp [ha]
    change 3 ^ P.length + 1 ≤ 2 * |ofDigits P - 3 ^ P.length|
    by_cases hx : 0 ≤ ofDigits P - 3 ^ P.length
    · rw [abs_of_nonneg hx]
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hx)]
      nlinarith [hhigh]
  · simp [ha]
    by_cases hx : 0 ≤ ofDigits P + 3 ^ P.length
    · rw [abs_of_nonneg hx]
      nlinarith [hlow]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      nlinarith [hhigh]

theorem abs_ofDigits_ge_of_wellFormed {L : List ℤ} (h : WellFormed L) (hl : L ≠ []) :
    3 ^ (L.length - 1) ≤ 2 * |ofDigits L| + 1 := by
  have hs := abs_ofDigits_ge_of_wellFormed_strong h hl
  nlinarith

/-- Conversely, if `|n|` is within the radius of a `k`-digit
representation, `digits n` has length at most `k`. -/
theorem digits_length_le {n : ℤ} {k : ℕ} (h : 2 * |n| ≤ 3 ^ k - 1) :
    (digits n).length ≤ k := by
  by_cases hnil : digits n = []
  · simp [hnil]
  have hstrong := abs_ofDigits_ge_of_wellFormed_strong
    (wellFormed_digits n) hnil
  have hstrong' : 3 ^ ((digits n).length - 1) + 1 ≤ 2 * |n| := by
    simpa [ofDigits_digits] using hstrong
  by_contra hnot
  have hkl : k ≤ (digits n).length - 1 := by omega
  have hpow : 3 ^ k ≤ 3 ^ ((digits n).length - 1) :=
    Nat.pow_le_pow_right (by omega) hkl
  nlinarith [hstrong']

/-- The length of `digits n` is the least `k` for which `n` fits in the
symmetric radius-`(3^k - 1)/2` range. -/
theorem digits_length_eq (n : ℤ) :
    (digits n).length = Nat.find (by
      show ∃ k, 2 * |n| ≤ 3 ^ k - 1
      exact ⟨(digits n).length, abs_lt_of_digits_length n⟩) := by
  let H : ∃ k, 2 * |n| ≤ 3 ^ k - 1 :=
    ⟨(digits n).length, abs_lt_of_digits_length n⟩
  have hlen : 2 * |n| ≤ 3 ^ (digits n).length - 1 :=
    abs_lt_of_digits_length n
  change (digits n).length = Nat.find H
  symm
  apply (Nat.find_eq_iff H).2
  constructor
  · exact hlen
  · intro m hm hPm
    have hle : (digits n).length ≤ m := digits_length_le hPm
    omega

end BalTernary
