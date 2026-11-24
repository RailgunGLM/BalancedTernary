# Formalising Balanced Ternary in Lean 4

A formalization of the balanced ternary positional numeral system
(digits in `{-1, 0, 1}`, base 3), modelled structurally on
`Mathlib.Data.Nat.Digits.Defs` / `Lemmas`.

## Status

Skeleton stage: all definitions are complete and compile (modulo the
`centerDiv_lt_abs` termination lemma); all theorem **statements** are
final-draft, with proofs left as `sorry` and a proof sketch in a comment
above each.

## File layout

| File | Mirrors | Content |
|---|---|---|
| `BalancedTernary/Defs.lean` | `Nat.Digits.Defs` | `IsDigit`, `WellFormed`, `ofDigits`, `digits`, centered-mod recursion |
| `BalancedTernary/Lemmas.lean` | `Nat.Digits.Lemmas` (round-trip part) | `ofDigits_digits`, `digits_ofDigits`, injectivity, length bounds |
| `BalancedTernary/Bijection.lean` | `Nat.bijOn_ofDigits` | Symmetric-range `BijOn` theorem (new: unsigned Mathlib targets `[0, b^k)`, this targets `[-(3^k-1)/2, (3^k-1)/2]`) |
| `BalancedTernary/Arithmetic.lean` | misc. arithmetic lemmas in `Nat.Digits.Lemmas` | append, negation symmetry (`digits_neg`, no unsigned analogue), ×3 shift, divisibility |

## Build

```
lake update
lake build
```

### Troubleshooting: "bad import" / "no such file or directory" on a Mathlib module

If `lake build` fails partway through building Mathlib itself (not your own
files) with an error like:

```
error: no such file or directory ... Mathlib\Data\Int\ModCast.lean
error: BalancedTernary\Defs.lean: bad import 'Mathlib.Data.Int.ModCast'
```

this means the Mathlib *source* fetched by `lake update` is a different
revision than the one your `lean-toolchain` / `lake-manifest.json` expects,
so file paths that existed in one Mathlib version have since been renamed or
merged in another. This is almost always caused by the pinned tag being
**stale or nonexistent** — `v4.14.0` (used in an earlier revision of this
project) is well over a year old and predates large reorganizations of
`Mathlib/Data/Int/...`, which is exactly why that file no longer exists at
that path. Fix:

1. `lakefile.toml` and `lean-toolchain` now both pin to `v4.35.0` (the
   latest stable mathlib4/Lean release as of writing). **Check
   <https://github.com/leanprover-community/mathlib4/releases> yourself
   before building** — if a newer stable tag exists by the time you read
   this, use that instead, and make sure `lean-toolchain` names the exact
   Lean version listed in that mathlib4 tag's own `lean-toolchain` file
   (open `https://raw.githubusercontent.com/leanprover-community/mathlib4/<tag>/lean-toolchain`
   to check). The two files must always agree.
2. Delete `lake-manifest.json` and the `.lake` directory entirely, then
   re-run `lake update && lake build` to force a fresh, consistent fetch —
   stale manifests are the second most common cause of this error.
3. `Defs.lean`'s import of `Mathlib.Data.Int.ModCast` was removed — it was
   unused (no casting lemmas are needed there; everything is `ℤ`-native),
   and is one less thing that can break if Mathlib reorganizes that corner
   of `Data.Int` again.

## Priority order for filling in `sorry`s

1. `Defs.centerDiv_lt_abs` — needed for `digitsAux` to type-check as
   well-founded recursion (currently assumed).
2. `Lemmas.ofDigits_digits` — the core existence/round-trip proof;
   everything else depends on it.
3. `Lemmas.isDigit_of_mem_digits`, `Lemmas.wellFormed_digits`.
4. `Lemmas.digits_ofDigits`, `digits_injective`, `digits_inj_iff`.
5. `Lemmas.abs_ofDigits_le`, `digits_length_le` (bounds).
6. `Arithmetic.ofDigits_neg`, `digits_neg` (negation symmetry —
   flagship result with no unsigned analogue).
7. `Bijection.*` (depends on 2–5 plus a new padding lemma).
8. Remaining `Arithmetic.lean` lemmas (append, ×3 shift, divisibility).
9. `Lemmas.digits_length_eq` — left loosely stated, revisit once a
   `Int.log`-style closed form is chosen.

## References

* Wikipedia, "Balanced ternary" — definition, uniqueness statement,
  Knuth/Euler historical notes.
* deriveit.net, "Proof of the balanced ternary expansion" — the
  repeated-centered-division existence proof that `Lemmas.ofDigits_digits`
  formalizes.
* `Mathlib.Data.Nat.Digits.Defs` / `Mathlib.Data.Nat.Digits.Lemmas` —
  structural template for this entire project.
