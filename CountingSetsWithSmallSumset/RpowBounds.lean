/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers of large numbers

This file collects the estimates for real powers that the computations of Section 7 of Green,
*Counting sets with small sumset, and the clique number of random Cayley graphs*, use for
`ℤ_N` and for `𝔽₂ⁿ`. For `j ≥ 2 ^ 9000` the powers `j ^ (1 / 32)` and `j ^ (1 / 60)` are at
least `100` and `1000`, so `j ^ (31 / 32) ≤ j / 100`.

## Main statements

* `hundred_le_rpow_inv_thirtyTwo`, `thousand_le_rpow_inv_sixty`: `100 ≤ j ^ (1 / 32)` and
  `1000 ≤ j ^ (1 / 60)` for `j ≥ 2 ^ 9000`.
* `rpow_thirtyOne_div_thirtyTwo_le`: `j ^ (31 / 32) ≤ j / 100` when `100 ≤ j ^ (1 / 32)`.
* `rpow_thirtyOne_div_thirty_eq`: `j ^ (31 / 30) = j * (j ^ (1 / 60)) ^ 2`.
* `log_le_sixty_mul_rpow_inv_sixty`: `log j ≤ 60 * j ^ (1 / 60)`.
-/

public section

namespace CountingSetsWithSmallSumset

open Real

private lemma pow_le_two_pow_nineThousand {c : ℝ} {n : ℕ} (hc₀ : 0 ≤ c) (hc : c ≤ 2 ^ 10)
    (hn : 10 * n ≤ 9000) : c ^ n ≤ 2 ^ 9000 := by
  refine (pow_le_pow_left₀ hc₀ hc n).trans ?_
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) hn

private lemma le_natCast_rpow_inv {j : ℕ} (hj : 2 ^ 9000 ≤ j) {c z : ℝ} (hc : 0 ≤ c) (hz : 0 < z)
    (h : c ^ z ≤ 2 ^ 9000) : c ≤ (j : ℝ) ^ z⁻¹ :=
  (le_rpow_inv_iff_of_pos hc (Nat.cast_nonneg j) hz).2 (h.trans (by exact_mod_cast hj))

lemma hundred_le_rpow_inv_thirtyTwo {j : ℕ} (hj : 2 ^ 9000 ≤ j) :
    100 ≤ (j : ℝ) ^ (32 : ℝ)⁻¹ := by
  refine le_natCast_rpow_inv hj (by norm_num) (by norm_num) ?_
  rw [rpow_ofNat]
  exact pow_le_two_pow_nineThousand (by norm_num) (by norm_num) (by norm_num)

lemma thousand_le_rpow_inv_sixty {j : ℕ} (hj : 2 ^ 9000 ≤ j) : 1000 ≤ (j : ℝ) ^ (60 : ℝ)⁻¹ := by
  refine le_natCast_rpow_inv hj (by norm_num) (by norm_num) ?_
  rw [rpow_ofNat]
  exact pow_le_two_pow_nineThousand (by norm_num) (by norm_num) (by norm_num)

lemma rpow_thirtyOne_div_thirtyTwo_le {j : ℝ} (hj : 0 ≤ j) (h : 100 ≤ j ^ (32 : ℝ)⁻¹) :
    j ^ ((31 : ℝ) / 32) ≤ j / 100 := by
  have hj' : j ^ ((31 : ℝ) / 32) * j ^ (32 : ℝ)⁻¹ = j := by
    rw [← rpow_add' hj (by norm_num)]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_left h (rpow_nonneg hj ((31 : ℝ) / 32))]

lemma rpow_thirtyOne_div_thirty_eq {j : ℝ} (hj : 0 ≤ j) :
    j ^ ((31 : ℝ) / 30) = j * (j ^ (60 : ℝ)⁻¹) ^ 2 := by
  rw [← rpow_natCast, ← rpow_mul hj, ← rpow_one_add' hj (by norm_num)]
  norm_num

lemma log_le_sixty_mul_rpow_inv_sixty {j : ℝ} (hj : 0 ≤ j) : log j ≤ 60 * j ^ (60 : ℝ)⁻¹ := by
  simpa [div_inv_eq_mul, mul_comm] using log_le_rpow_div hj (by norm_num : (0 : ℝ) < 60⁻¹)

end CountingSetsWithSmallSumset
