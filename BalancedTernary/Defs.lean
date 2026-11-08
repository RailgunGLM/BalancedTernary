/-
Copyright (c) 2026 Git Lun Mak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-!
# Balanced ternary representation of integers

This file defines the *balanced ternary* positional numeral system: every
integer `n` is represented as a (little-endian) list of digits drawn from
`{-1, 0, 1}` such that

  `n = Σ i, d i * 3 ^ i`.

This mirrors `Mathlib.Data.Nat.Digits.Defs`, but

* digits live in `ℤ` (constrained to `{-1, 0, 1}`) instead of `ℕ`,
* the base is fixed at `3` (balanced ternary is only interesting at base 3;
  a general "balanced base `b`" construction is possible but out of scope),
* the digit-extraction step uses a *centered* remainder instead of the
  ordinary `%`, since ordinary base-3 remainders lie in `{0, 1, 2}` and `2`
  is not an allowed digit.

## Main definitions

* `BalTernary.IsDigit d` : `d ∈ ({-1, 0, 1} : Set ℤ)`.
* `BalTernary.ofDigits L` : evaluates a digit list `L : List ℤ` to the
  integer it represents (little-endian, no well-formedness assumed yet).
* `BalTernary.digits n` : the canonical digit list of `n : ℤ` (no trailing
  zero digits, `digits 0 = []`).

## Implementation notes

The centering step is: given `n : ℤ`, write `n = 3 * q + r` with
`r = n - 3 * q ∈ {-1, 0, 1}` via "round `n / 3` to the nearest integer".
We implement this with `Int.ediv`/`Int.emod` adjustments rather than
reusing `Nat.digits`' auxiliary machinery, since that machinery is
specialized to non-negative remainders.

## References

* Wikipedia, *Balanced ternary*.
* deriveit.net, "Proof of the balanced ternary expansion" (existence proof
  via repeated division, re-centering any remainder of `2` into `-1` with a
  carry).
* `Mathlib.Data.Nat.Digits.Defs`, whose `ofDigits`/`digits` pair and
  round-trip theorems this file's API is modelled on.
-/

namespace BalTernary

/-- A balanced ternary digit is one of `-1`, `0`, `1`. -/
def IsDigit (d : ℤ) : Prop := d = -1 ∨ d = 0 ∨ d = 1

@[simp] lemma isDigit_neg_one : IsDigit (-1) := Or.inl rfl
@[simp] lemma isDigit_zero : IsDigit 0 := Or.inr (Or.inl rfl)
@[simp] lemma isDigit_one : IsDigit 1 := Or.inr (Or.inr rfl)

lemma IsDigit.neg {d : ℤ} (h : IsDigit d) : IsDigit (-d) := by
  rcases h with h | h | h <;> simp [h]

lemma IsDigit.abs_le_one {d : ℤ} (h : IsDigit d) : |d| ≤ 1 := by
  rcases h with rfl | rfl | rfl <;> norm_num

/-- A list of integers is a valid (unpadded) balanced ternary digit list if
every entry is a digit and the leading (= last, little-endian) entry is
nonzero (so the representation has no redundant leading zero digit),
unless the list is empty. -/
def WellFormed (L : List ℤ) : Prop :=
  (∀ d ∈ L, IsDigit d) ∧ (∀ h : L ≠ [], L.getLast h ≠ 0)

/-- Evaluate a little-endian digit list `[d₀, d₁, ..., dₖ]` to
`d₀ + 3 d₁ + 3² d₂ + ⋯ + 3ᵏ dₖ`. Analogous to `Nat.ofDigits`. -/
def ofDigits : List ℤ → ℤ
  | [] => 0
  | d :: L => d + 3 * ofDigits L

@[simp] lemma ofDigits_nil : ofDigits [] = 0 := rfl

@[simp] lemma ofDigits_cons (d : ℤ) (L : List ℤ) :
    ofDigits (d :: L) = d + 3 * ofDigits L := rfl

lemma ofDigits_singleton (d : ℤ) : ofDigits [d] = d := by simp

/-- The "centered remainder" of `n` mod 3: the unique `r ∈ {-1, 0, 1}` with
`r ≡ n [ZMOD 3]`. -/
def centerMod (n : ℤ) : ℤ :=
  if n % 3 = 2 then -1 else if n % 3 = -2 then 1 else n % 3

/-- The matching quotient: `n = 3 * centerDiv n + centerMod n`. -/
def centerDiv (n : ℤ) : ℤ :=
  (n - centerMod n) / 3

lemma centerMod_isDigit (n : ℤ) : IsDigit (centerMod n) := by
  unfold centerMod
  have h3 : (3:ℤ) ≠ 0 := by norm_num
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 ∨ n % 3 = -1 ∨ n % 3 = -2 := by
    omega
  rcases hr with h0 | h1 | h2 | hm1 | hm2 <;> simp_all [IsDigit]

lemma centerMod_spec (n : ℤ) : n = 3 * centerDiv n + centerMod n := by
  unfold centerDiv
  have : (3:ℤ) ∣ (n - centerMod n) := by
    unfold centerMod
    have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 ∨ n % 3 = -1 ∨ n % 3 = -2 := by omega
    split_ifs with h1 h2 <;> omega
  omega

/-- Termination measure: centering strictly decreases `|n|` once `n ≠ 0`
(in fact for `|n| ≥ 1`, `|centerDiv n| < |n|`), mirroring the
`n / b < n` lemma used for `Nat.digitsAux`'s termination. -/
lemma centerDiv_lt_abs (n : ℤ) (hn : n ≠ 0) : (centerDiv n).natAbs < n.natAbs := by
  unfold centerDiv
  unfold centerMod
  omega

/-- Auxiliary recursive digit extraction, well-founded on `n.natAbs`. -/
def digitsAux (n : ℤ) : List ℤ :=
  if h : n = 0 then []
  else centerMod n :: digitsAux (centerDiv n)
termination_by n.natAbs
decreasing_by exact centerDiv_lt_abs n h

/-- `digits n` is the canonical (no trailing-zero) balanced ternary
representation of `n`, little-endian. `digits 0 = []`. -/
def digits (n : ℤ) : List ℤ := digitsAux n

@[simp] lemma digits_zero : digits 0 = [] := by unfold digits digitsAux; simp

/-- Unfolding equation for `digits` at a nonzero argument: peel off the
centered-mod digit and recurse on the centered-div quotient.
Analogue of `Nat.digits_def'` / `Nat.digits_eq_cons_digits_div`. -/
theorem digits_eq_cons_centerMod_centerDiv {n : ℤ} (h : n ≠ 0) :
    digits n = centerMod n :: digits (centerDiv n) := by
  change digitsAux n = centerMod n :: digitsAux (centerDiv n)
  rw [digitsAux]
  exact dite_eq_right h

/-- A single nonzero digit is its own canonical representation.
Analogue of `Nat.digits_of_lt`. -/
theorem digits_of_isDigit {d : ℤ} (hd : IsDigit d) (h0 : d ≠ 0) : digits d = [d] := by
  rcases hd with h | h | h <;> simp_all [digits_eq_cons_centerMod_centerDiv, centerMod, centerDiv];

/-- Analogue of `Nat.digits_add`: prepending a valid digit `d` and
multiplying the remainder by `3` is exactly what `ofDigits`/`digits`
undo each other on, i.e. `digits` of `d + 3 * n` is `d :: digits n`,
provided `d` is a genuine digit and the pair isn't the degenerate
`(0, 0)` case. This is the key step used to prove `digits_ofDigits`. -/
theorem digits_add {d n : ℤ} (hd : IsDigit d) (h : d ≠ 0 ∨ n ≠ 0) :
    digits (d + 3 * n) = d :: digits n := by
  have hsum : d + 3 * n ≠ 0 := by
    intro hzero
    rcases hd with hd | hd | hd
    · omega
    · rcases h with _ | hn
      · omega
      · exact hn (by omega)
    · omega
  have hMod : centerMod (d + 3 * n) = d := by
    unfold centerMod
    rcases hd with rfl | rfl | rfl <;> simp
  have hDiv : centerDiv (d + 3 * n) = n := by
    unfold centerDiv
    rw [hMod]
    omega
  rw [digits_eq_cons_centerMod_centerDiv hsum, hMod, hDiv]
  -- Proof sketch: show centerMod (d + 3*n) = d (since d ∈ {-1,0,1} and
  -- adding a multiple of 3 doesn't change the centered residue class),
  -- and centerDiv (d + 3*n) = n (by `centerMod_spec` + cancellation),
  -- then `digits_eq_cons_centerMod_centerDiv` using `h` to rule out
  -- the n = 0 ∧ d = 0 case where `d + 3*n = 0` and digits should be `[]`.

end BalTernary
