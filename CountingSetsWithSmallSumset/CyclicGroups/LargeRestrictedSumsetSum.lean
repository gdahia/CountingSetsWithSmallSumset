/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CountingSetsWithSmallSumset.CyclicGroups.RestrictedSumsetCardBounds
import CountingSetsWithSmallSumset.RpowBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The expected number of cliques with large restricted sumset in `ℤ_N`

Let `j ≥ 2 ^ 9000` and `j ≥ 20 * log₂ N`. This file bounds the sum of `|S_j^m(ℤ_N)| * 2 ^ (-m)`
over `7 * j ≤ m ≤ N` by `N ^ (-2)`, which is the computation of Section 7 of Green, *Counting
sets with small sumset, and the clique number of random Cayley graphs*, for `ℤ_N`. By
Proposition 23 each term is at most `2 ^ (-m / 40)`. For `m ≤ j ^ (31 / 30) / 2` this uses the
bound `N ^ (1 + 4 * m / j) * (2 * e * m / j) ^ j * exp (j ^ (31 / 32))` and the inequality
`log (2 * e * c) ≤ 4 * log 2 + c / 8`. For larger `m` it uses the bound
`N ^ (1 + 4 * m / j) * j ^ (4 * j)`. As `m ≥ 7 * j ≥ 140 * log₂ N`, each term is at most
`N ^ (-3)`, and there are at most `N` terms.

## Main statements

* `card_restrictedSumsetCardSets_zmod_div_two_pow_le`: `|S_j^m(ℤ_N)| / 2 ^ m ≤ N ^ (-3)` for
  `m ≥ 7 * j`.
* `sum_card_restrictedSumsetCardSets_zmod_div_two_pow_le`: the sum over `7 * j ≤ m ≤ N` is at most
  `N ^ (-2)`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real

private lemma mul_log_two_mul_exp_one_mul_div_le {j m : ℝ} (hj : 0 < j) (hm : 0 < m) :
    j * log (2 * exp 1 * m / j) ≤ 4 * log 2 * j + m / 8 := by
  have h : 2 * exp 1 * m / j = 2 ^ 4 * exp 1 * (m / (8 * j)) := by
    field_simp
    ring
  rw [h, log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_exp]
  nlinarith [log_le_sub_one_of_pos (by positivity : 0 < m / (8 * j)),
    (by field_simp : j * (m / (8 * j)) = m / 8)]

private lemma four_mul_div_mul_le {j m L : ℝ} (hj : 0 < j) (hm : 0 ≤ m)
    (hLj : 20 * L ≤ j * log 2) : 4 * m / j * L ≤ m * log 2 / 5 := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hj (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hLj hm]

/-- The logarithm of the bound of Proposition 23 (i), divided by `2 ^ m`, is at most
`-m * log 2 / 40`. -/
private lemma exponent_le_of_le_rpow {j m L : ℝ} (hj : 0 < j) (h : 100 ≤ j ^ (32 : ℝ)⁻¹)
    (hjm : 7 * j ≤ m) (hLj : 20 * L ≤ j * log 2) :
    (1 + 4 * m / j) * L + j * log (2 * exp 1 * m / j) + j ^ ((31 : ℝ) / 32) - m * log 2 ≤
      -(m * log 2 / 40) := by
  nlinarith [four_mul_div_mul_le (m := m) hj (by linarith) hLj,
    mul_log_two_mul_exp_one_mul_div_le (m := m) hj (by linarith),
    rpow_thirtyOne_div_thirtyTwo_le hj.le h, mul_le_mul_of_nonneg_left log_two_lt_d9.le hj.le,
    mul_le_mul_of_nonneg_left log_two_gt_d9.le (by linarith : 0 ≤ m)]

/-- The logarithm of the bound of Proposition 23 (ii), divided by `2 ^ m`, is at most
`-m * log 2 / 40` when `m > j ^ (31 / 30) / 2`. -/
private lemma exponent_le_of_rpow_lt {j m L : ℝ} (hj : 0 < j) (hu : 1000 ≤ j ^ (60 : ℝ)⁻¹)
    (hjm : j ^ ((31 : ℝ) / 30) / 2 < m) (hLj : 20 * L ≤ j * log 2) :
    (1 + 4 * m / j) * L + 4 * j * log j - m * log 2 ≤ -(m * log 2 / 40) := by
  rw [rpow_thirtyOne_div_thirty_eq hj.le] at hjm
  have hm : 0 ≤ m := le_trans (by positivity) hjm.le
  nlinarith [four_mul_div_mul_le hj hm hLj,
    mul_le_mul_of_nonneg_left (log_le_sixty_mul_rpow_inv_sixty hj.le) (by positivity : 0 ≤ 4 * j),
    mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ j * j ^ (60 : ℝ)⁻¹),
    mul_le_mul_of_nonneg_left hu hj.le, mul_le_mul_of_nonneg_left log_two_lt_d9.le hj.le,
    mul_le_mul_of_nonneg_left log_two_gt_d9.le hm]

variable {N : ℕ} [NeZero N]

private lemma card_restrictedSumsetCardSets_zmod_div_two_pow_le_exp {j m : ℕ} (hj : 2 ^ 9000 ≤ j)
    (hLj : 20 * log N ≤ j * log 2) (hjm : 7 * j ≤ m) :
    (#(restrictedSumsetCardSets (ZMod N) j m) : ℝ) / 2 ^ m ≤ exp (-(m * log 2 / 40)) := by
  have hj₀ : (0 : ℝ) < j := Nat.cast_pos.2 (Nat.one_le_two_pow.trans hj)
  have hm : (7 : ℝ) * j ≤ m := by exact_mod_cast hjm
  have hm₀ : (0 : ℝ) < m := by linarith
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  by_cases hsmall : (m : ℝ) ≤ j ^ ((31 : ℝ) / 30) / 2
  · refine (div_le_div_of_nonneg_right
      (card_restrictedSumsetCardSets_zmod_le_of_le_rpow N hj hsmall) (by positivity)).trans
      ((log_le_iff_le_exp (by positivity)).1 ?_)
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_rpow hN, log_pow, log_exp, log_pow]
    linarith [exponent_le_of_le_rpow hj₀ (hundred_le_rpow_inv_thirtyTwo hj) hm hLj]
  · refine (div_le_div_of_nonneg_right
      (card_restrictedSumsetCardSets_zmod_le N (Nat.cast_pos.1 hj₀) m) (by positivity)).trans
      ((log_le_iff_le_exp (by positivity)).1 ?_)
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_rpow hN, log_pow, log_pow]
    push_cast
    linarith [exponent_le_of_rpow_lt hj₀ (thousand_le_rpow_inv_sixty hj) (not_le.1 hsmall) hLj]

/-- If `j ≥ 2 ^ 9000`, `j ≥ 20 * log₂ N` and `m ≥ 7 * j`, then `|S_j^m(ℤ_N)| / 2 ^ m ≤ N ^ (-3)`. -/
lemma card_restrictedSumsetCardSets_zmod_div_two_pow_le {j m : ℕ} (hj : 2 ^ 9000 ≤ j)
    (hjN : 20 * logb 2 N ≤ j) (hjm : 7 * j ≤ m) :
    (#(restrictedSumsetCardSets (ZMod N) j m) : ℝ) / 2 ^ m ≤ 1 / N ^ 3 := by
  have hLj : 20 * log N ≤ j * log 2 := by
    rwa [logb, ← mul_div_assoc, div_le_iff₀ (log_pos one_lt_two)] at hjN
  refine (card_restrictedSumsetCardSets_zmod_div_two_pow_le_exp hj hLj hjm).trans ?_
  rw [one_div, ← exp_log (pow_pos (Nat.cast_pos.2 (NeZero.pos N)) 3), ← exp_neg, exp_le_exp,
    log_pow, neg_le_neg_iff]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right (by exact_mod_cast hjm : (7 : ℝ) * j ≤ m)
    (log_pos one_lt_two).le, log_natCast_nonneg N]

/-- The computation of Section 7 of Green for `ℤ_N`. If `j ≥ 2 ^ 9000` and `j ≥ 20 * log₂ N`, then
the sum of `|S_j^m(ℤ_N)| / 2 ^ m` over `7 * j ≤ m ≤ N` is at most `N ^ (-2)`. -/
lemma sum_card_restrictedSumsetCardSets_zmod_div_two_pow_le {j : ℕ} (hj : 2 ^ 9000 ≤ j)
    (hjN : 20 * logb 2 N ≤ j) :
    ∑ m ∈ Icc (7 * j) N, (#(restrictedSumsetCardSets (ZMod N) j m) : ℝ) / 2 ^ m ≤ 1 / N ^ 2 := by
  refine (sum_le_sum (g := fun _ ↦ 1 / (N : ℝ) ^ 3) ?_).trans ?_
  · intro m hm
    obtain ⟨hjm, -⟩ := mem_Icc.1 hm
    exact card_restrictedSumsetCardSets_zmod_div_two_pow_le hj hjN hjm
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by grind [Nat.one_le_two_pow.trans hj] :
    N + 1 - 7 * j ≤ N)) (by positivity)).trans_eq ?_
  field_simp

end CountingSetsWithSmallSumset
