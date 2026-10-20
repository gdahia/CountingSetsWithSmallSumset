/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CountingSetsWithSmallSumset.BinaryGroups.RestrictedSumsetCardBounds
import CountingSetsWithSmallSumset.RpowBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The expected number of cliques with large restricted sumset in `𝔽₂ⁿ`

Let `n ≥ 2 ^ 9000` and `j ≥ 38 * n * log₂ n`, and write `N = 2 ^ n`. This file bounds the sum of
`|S_j^m(𝔽₂ⁿ)| * 2 ^ (-m)` over `7 * j ≤ m ≤ N` by `N ^ (-2)`, which is the computation of Section 7
of Green, *Counting sets with small sumset, and the clique number of random Cayley graphs*, for
`𝔽₂ⁿ`. The hypothesis on `j` gives `40 * n * log j ≤ j` and `j ≥ 2 ^ 9000`. By Proposition 26
each term is then at most `2 ^ (-m / 5)`. For `m ≤ j ^ (31 / 30)` this uses the bound
`N ^ (4 * m * log₂ j / j) * (e * m / j) ^ j * exp (j ^ (31 / 32))` and the inequality
`log (e * c) ≤ 3 * log 2 + c / 8`. For larger `m` it uses the bound
`N ^ (4 * m * log₂ j / j) * j ^ (4 * j)`. As `m ≥ 7 * j ≥ 15 * n`, each term is at most
`N ^ (-3)`, and there are at most `N` terms.

## Main statements

* `card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le`: `|S_j^m(𝔽₂ⁿ)| / 2 ^ m ≤ N ^ (-3)`
  for `m ≥ 7 * j`.
* `sum_card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le`: the sum over `7 * j ≤ m ≤ N` is
  at most `N ^ (-2)`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real

/-- For `j, m > 0`, `j * log (e * m / j) ≤ 3 * log 2 * j + m / 8`. This is
`log (e * c) ≤ 3 * log 2 + c / 8` for `c = m / j`. -/
private lemma mul_log_exp_one_mul_div_le {j m : ℝ} (hj : 0 < j) (hm : 0 < m) :
    j * log (exp 1 * m / j) ≤ 3 * log 2 * j + m / 8 := by
  have h : exp 1 * m / j = 2 ^ 3 * exp 1 * (m / (8 * j)) := by
    field_simp
    ring
  rw [h, log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_exp]
  nlinarith [log_le_sub_one_of_pos (by positivity : 0 < m / (8 * j)),
    (by field_simp : j * (m / (8 * j)) = m / 8)]

/-- The logarithm of `(2 ^ n) ^ (4 * m * log₂ j / j)` is at most `m / 10` when
`40 * n * log j ≤ j`. -/
private lemma four_mul_logb_div_mul_le {j m n : ℝ} (hj : 0 < j) (hm : 0 ≤ m)
    (hnj : 40 * (n * log j) ≤ j) : 4 * m * logb 2 j / j * (n * log 2) ≤ m / 10 := by
  rw [logb]
  field_simp [(log_pos one_lt_two).ne']
  nlinarith [mul_le_mul_of_nonneg_left hnj hm]

/-- The logarithm of the bound of Proposition 26 (i), divided by `2 ^ m`, is at most
`-m * log 2 / 5`. -/
private lemma exponent_le_of_le_rpow {j m n : ℝ} (hj : 0 < j) (h : 100 ≤ j ^ (32 : ℝ)⁻¹)
    (hjm : 7 * j ≤ m) (hnj : 40 * (n * log j) ≤ j) :
    4 * m * logb 2 j / j * (n * log 2) + j * log (exp 1 * m / j) + j ^ ((31 : ℝ) / 32) -
      m * log 2 ≤ -(m * log 2 / 5) := by
  nlinarith [four_mul_logb_div_mul_le (m := m) hj (by linarith) hnj,
    mul_log_exp_one_mul_div_le (m := m) hj (by linarith),
    rpow_thirtyOne_div_thirtyTwo_le hj.le h,
    mul_le_mul_of_nonneg_left hjm (log_pos one_lt_two).le,
    mul_le_mul_of_nonneg_left log_two_gt_d9.le (by linarith : 0 ≤ m)]

/-- The logarithm of the bound of Proposition 26 (ii), divided by `2 ^ m`, is at most
`-m * log 2 / 5` when `m > j ^ (31 / 30)`. -/
private lemma exponent_le_of_rpow_lt {j m n : ℝ} (hj : 0 < j) (hu : 1000 ≤ j ^ (60 : ℝ)⁻¹)
    (hjm : j ^ ((31 : ℝ) / 30) < m) (hnj : 40 * (n * log j) ≤ j) :
    4 * m * logb 2 j / j * (n * log 2) + 4 * j * log j - m * log 2 ≤ -(m * log 2 / 5) := by
  rw [rpow_thirtyOne_div_thirty_eq hj.le] at hjm
  have hm : 0 ≤ m := le_trans (by positivity) hjm.le
  nlinarith [four_mul_logb_div_mul_le hj hm hnj,
    mul_le_mul_of_nonneg_left (log_le_sixty_mul_rpow_inv_sixty hj.le) (by positivity : 0 ≤ 4 * j),
    mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ j * j ^ (60 : ℝ)⁻¹),
    mul_le_mul_of_nonneg_left log_two_gt_d9.le hm]

variable {n : ℕ}

/-- If `j ≥ 2 ^ 9000`, `40 * n * log j ≤ j` and `m ≥ 7 * j`, then
`|S_j^m(𝔽₂ⁿ)| / 2 ^ m ≤ exp (-m * log 2 / 5)`. -/
private lemma card_restrictedSumsetCardSets_div_two_pow_le_exp {j m : ℕ} (hj : 2 ^ 9000 ≤ j)
    (hnj : 40 * (n * log j) ≤ j) (hjm : 7 * j ≤ m) :
    (#(restrictedSumsetCardSets (Fin n → ZMod 2) j m) : ℝ) / 2 ^ m ≤
      exp (-(m * log 2 / 5)) := by
  have hj₀ : (0 : ℝ) < j := Nat.cast_pos.2 (Nat.one_le_two_pow.trans hj)
  have hm : (7 : ℝ) * j ≤ m := by exact_mod_cast hjm
  have hm₀ : (0 : ℝ) < m := by linarith
  by_cases hsmall : (m : ℝ) ≤ j ^ ((31 : ℝ) / 30)
  · refine (div_le_div_of_nonneg_right (card_restrictedSumsetCardSets_pi_zmod_two_le_of_le_rpow
      n hj hsmall) (by positivity)).trans ((log_le_iff_le_exp (by positivity)).1 ?_)
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_rpow (by positivity), log_pow, log_pow,
      log_exp, log_pow]
    linarith [exponent_le_of_le_rpow hj₀ (hundred_le_rpow_inv_thirtyTwo hj) hm hnj]
  · refine (div_le_div_of_nonneg_right (card_restrictedSumsetCardSets_pi_zmod_two_le n
      ((Nat.le_self_pow (by norm_num) 2).trans hj) m) (by positivity)).trans
      ((log_le_iff_le_exp (by positivity)).1 ?_)
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_rpow (by positivity), log_pow, log_pow, log_pow]
    push_cast
    linarith [exponent_le_of_rpow_lt hj₀ (thousand_le_rpow_inv_sixty hj) (not_le.1 hsmall) hnj]

/-- If `n ≥ 2 ^ 9000`, then `9000 * log 2 ≤ log n`. -/
private lemma nineThousand_mul_log_two_le_log (hn : 2 ^ 9000 ≤ n) : 9000 * log 2 ≤ log n := by
  simpa using log_le_log (by positivity) (by exact_mod_cast hn : (2 : ℝ) ^ 9000 ≤ n)

/-- The inequality `38 * n * log₂ n ≤ j` in natural logarithms. -/
private lemma mul_log_le_mul_log_two {j : ℕ} (hjn : 38 * n * logb 2 n ≤ j) :
    38 * n * log n ≤ j * log 2 := by
  rwa [logb, ← mul_div_assoc, div_le_iff₀ (log_pos one_lt_two)] at hjn

/-- If `n ≥ 2 ^ 9000` and `j ≥ 38 * n * log₂ n`, then `1000 * n ≤ j`. -/
private lemma thousand_mul_le {j : ℕ} (hn : 2 ^ 9000 ≤ n) (hjn : 38 * n * logb 2 n ≤ j) :
    1000 * n ≤ (j : ℝ) := by
  nlinarith [mul_log_le_mul_log_two hjn, nineThousand_mul_log_two_le_log hn,
    mul_le_mul_of_nonneg_left (nineThousand_mul_log_two_le_log hn) (Nat.cast_nonneg n),
    mul_le_mul_of_nonneg_left log_two_lt_d9.le (Nat.cast_nonneg j),
    mul_le_mul_of_nonneg_left log_two_gt_d9.le (Nat.cast_nonneg n)]

/-- If `n ≥ 2 ^ 9000` and `j ≥ 38 * n * log₂ n`, then `n ≤ j`. -/
private lemma le_of_le_mul_logb {j : ℕ} (hn : 2 ^ 9000 ≤ n) (hjn : 38 * n * logb 2 n ≤ j) :
    n ≤ j := by
  refine (Nat.cast_le (α := ℝ)).1 ?_
  linarith [thousand_mul_le hn hjn, Nat.cast_nonneg (α := ℝ) n]

/-- If `n ≥ 2 ^ 9000` and `j ≥ 38 * n * log₂ n`, then `40 * n * log j ≤ j`. This follows from
`log j ≤ j / (2 ^ 8 * n) + log (2 ^ 8 * n) - 1`. -/
private lemma forty_mul_mul_log_le {j : ℕ} (hn : 2 ^ 9000 ≤ n) (hjn : 38 * n * logb 2 n ≤ j) :
    40 * (n * log j) ≤ j := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.one_le_two_pow.trans hn)
  have hj₀ : (0 : ℝ) < j := by linarith [thousand_mul_le hn hjn]
  have h := log_le_sub_one_of_pos (by positivity : 0 < (j : ℝ) / (2 ^ 8 * n))
  rw [log_div hj₀.ne' (by positivity), log_mul (by positivity) hn₀.ne', log_pow] at h
  nlinarith [mul_le_mul_of_nonneg_left h hn₀.le, mul_log_le_mul_log_two hjn,
    (by field_simp : (n : ℝ) * (j / (2 ^ 8 * n)) = j / 2 ^ 8),
    mul_le_mul_of_nonneg_left (nineThousand_mul_log_two_le_log hn) hn₀.le,
    mul_le_mul_of_nonneg_left log_two_lt_d9.le hj₀.le,
    mul_le_mul_of_nonneg_left log_two_lt_d9.le hn₀.le,
    mul_le_mul_of_nonneg_left log_two_gt_d9.le hn₀.le]

/-- If `n ≥ 2 ^ 9000`, `j ≥ 38 * n * log₂ n` and `m ≥ 7 * j`, then
`|S_j^m(𝔽₂ⁿ)| / 2 ^ m ≤ (2 ^ n) ^ (-3)`. -/
lemma card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le {j m : ℕ} (hn : 2 ^ 9000 ≤ n)
    (hjn : 38 * n * logb 2 n ≤ j) (hjm : 7 * j ≤ m) :
    (#(restrictedSumsetCardSets (Fin n → ZMod 2) j m) : ℝ) / 2 ^ m ≤ 1 / (2 ^ n) ^ 3 := by
  refine (card_restrictedSumsetCardSets_div_two_pow_le_exp (hn.trans (le_of_le_mul_logb hn hjn))
    (forty_mul_mul_log_le hn hjn) hjm).trans ?_
  rw [one_div, ← exp_log (by positivity : (0 : ℝ) < (2 ^ n) ^ 3), ← exp_neg, exp_le_exp, log_pow,
    log_pow, neg_le_neg_iff]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right (by exact_mod_cast hjm : (7 : ℝ) * j ≤ m)
    (log_pos one_lt_two).le, mul_le_mul_of_nonneg_right (thousand_mul_le hn hjn)
    (log_pos one_lt_two).le, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (log_pos one_lt_two).le]

/-- The computation of Section 7 of Green for `𝔽₂ⁿ`. If `n ≥ 2 ^ 9000` and
`j ≥ 38 * n * log₂ n`, then the sum of `|S_j^m(𝔽₂ⁿ)| / 2 ^ m` over `7 * j ≤ m ≤ 2 ^ n` is at most
`(2 ^ n) ^ (-2)`. -/
lemma sum_card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le {j : ℕ} (hn : 2 ^ 9000 ≤ n)
    (hjn : 38 * n * logb 2 n ≤ j) :
    ∑ m ∈ Icc (7 * j) (2 ^ n), (#(restrictedSumsetCardSets (Fin n → ZMod 2) j m) : ℝ) / 2 ^ m ≤
      1 / (2 ^ n) ^ 2 := by
  refine (sum_le_sum (g := fun _ ↦ 1 / ((2 : ℝ) ^ n) ^ 3) ?_).trans ?_
  · intro m hm
    obtain ⟨hjm, -⟩ := mem_Icc.1 hm
    exact card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le hn hjn hjm
  have hj : 1 ≤ j := (Nat.one_le_two_pow.trans hn).trans (le_of_le_mul_logb hn hjn)
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by grind : 2 ^ n + 1 - 7 * j ≤ 2 ^ n))
    (by positivity)).trans_eq ?_
  push_cast
  field_simp

end CountingSetsWithSmallSumset
