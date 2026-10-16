/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The dimension of the subspaces in the lower bound for the clique number

For `n ≥ 2 ^ 16` we choose `k` with `2 ^ (k + 1) ≤ n * (⌊log₂ n⌋ + 1) < 2 ^ (k + 2)`, close to the
choice `k = ⌊log₂ n + log₂ log₂ n - 1⌋` of Green. Then `2 ^ k ≥ n * log₂ n / 4`, so a
`k`-dimensional subspace of `𝔽₂ⁿ` is large enough, and `k = O(log n)`, so that the variance
estimate in the proof of Proposition 27 is small. This file proves the inequalities between `n` and
`k` that the proof uses.

## Main statements

* `exists_dim_of_two_pow_sixteen_le`: the choice of `k`.
* `succ_mul_mul_two_pow_mul_le`: the bound for the contribution of the pairs of subspaces with an
  intersection of dimension `l` to the variance.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

/-- The sequence `2 ^ l / l` is nondecreasing for `l ≥ 1`. -/
lemma mul_two_pow_le_mul_two_pow {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) :
    k * 2 ^ l ≤ l * 2 ^ k := by
  induction k, hlk using Nat.le_induction with
  | base => rfl
  | succ k hlk ih =>
    have := Nat.pow_le_pow_right two_pos hlk
    have := Nat.mul_le_mul_right (2 ^ k) hl
    rw [pow_succ]
    nlinarith

lemma sixteen_mul_sq_add_le_two_pow {m : ℕ} (hm : 16 ≤ m) : 16 * m ^ 2 + 14 * m + 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 2 m]
    nlinarith

/-- For `n ≥ 2 ^ 16` there is a `k ≤ n` with `n * log₂ n / 4 ≤ 2 ^ k`, `2 * 2 ^ k ≤ n * k` and
`((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n`. -/
lemma exists_dim_of_two_pow_sixteen_le {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    ∃ k, k ≤ n ∧ n * Real.logb 2 n / 4 ≤ 2 ^ k ∧ 2 * 2 ^ k ≤ n * k ∧
      ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n := by
  set m := Nat.log 2 n
  have hm : 16 ≤ m := Nat.le_log_of_pow_le one_lt_two hn
  have hmn : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by grind)
  have hnm : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self one_lt_two n
  have hj : 2 ^ Nat.log 2 (n * (m + 1)) ≤ n * (m + 1) := Nat.pow_log_le_self 2 (by positivity)
  have hj' : n * (m + 1) < 2 ^ (Nat.log 2 (n * (m + 1)) + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two _
  have hj₀ := Nat.log_pos one_lt_two (by nlinarith : 2 ≤ n * (m + 1))
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 (n * (m + 1)) = k + 1 := ⟨Nat.log 2 (n * (m + 1)) - 1, by grind⟩
  rw [hk] at hj hj'
  have hmk : m + 3 ≤ k := by
    have : 2 ^ (m + 4) < 2 ^ (k + 1 + 1) := by rw [pow_add]; nlinarith
    rw [Nat.pow_lt_pow_iff_right (by grind)] at this
    grind
  have hkm : k ≤ 2 * m := by
    have : n * (m + 1) < 2 ^ (m + 1) * 2 ^ (m + 1) := Nat.mul_lt_mul'' hnm Nat.lt_two_pow_self
    rw [← pow_add] at this
    have := hj.trans_lt this
    rw [Nat.pow_lt_pow_iff_right (by grind)] at this
    grind
  have hP := sixteen_mul_sq_add_le_two_pow hm
  refine ⟨k, by nlinarith, ?_, by rw [← pow_succ']; nlinarith, ?_⟩
  · have hlog : Real.logb 2 n < m + 1 := by
      rw [Real.logb_lt_iff_lt_rpow one_lt_two (by positivity),
        (by push_cast; ring : (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ)), Real.rpow_natCast]
      exact_mod_cast hnm
    have h4 : (n : ℝ) * (m + 1) < 2 ^ k * 4 := by
      rw [pow_add, pow_add] at hj'
      exact_mod_cast (by grind : n * (m + 1) < 2 ^ k * 4)
    nlinarith [mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg (α := ℝ) n)]
  · have hkn : (k + 1) * n ≤ 2 ^ (3 * m + 2) := by
      rw [(by ring : 3 * m + 2 = (2 * m + 1) + (m + 1)), pow_add]
      exact Nat.mul_le_mul ((by grind : k + 1 ≤ 2 * m + 1).trans Nat.lt_two_pow_self.le) hnm.le
    refine (Nat.mul_le_mul (Nat.pow_le_pow_left hkn 2)
      (Nat.pow_le_pow_right two_pos (by nlinarith : 4 * (k ^ 2 + k) ≤ 16 * m ^ 2 + 8 * m))).trans ?_
    rw [← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right two_pos (by nlinarith [Nat.pow_le_pow_right two_pos hP])

/-- If `1 ≤ l ≤ k`, `2 * 2 ^ k ≤ n * k` and `((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n`,
then `(k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ (n * (2 * k - l)) * 2 ^ 2 ^ l ≤ 2 ^ (2 * (n * k))`.
-/
lemma succ_mul_mul_two_pow_mul_le {n k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) (hk : 2 * 2 ^ k ≤ n * k)
    (hkn : ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n) :
    (k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ (n * (2 * k - l)) * 2 ^ 2 ^ l ≤
      2 ^ (2 * (n * k)) := by
  have hl' : 2 * 2 ^ l ≤ n * l := by
    have := mul_two_pow_le_mul_two_pow hl hlk
    have := Nat.mul_le_mul_left l hk
    exact Nat.le_of_mul_le_mul_right (by nlinarith) (by grind : 0 < k)
  have key : (k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ 2 ^ l ≤ 2 ^ (n * l) := by
    refine (Nat.pow_le_pow_iff_left two_ne_zero).mp ?_
    rw [(by ring : ((k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ 2 ^ l) ^ 2 =
      ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) * 2 ^ (2 ^ l * 2)), ← pow_mul]
    refine (Nat.mul_le_mul hkn
      (Nat.pow_le_pow_right two_pos (by grind : 2 ^ l * 2 ≤ n * l))).trans ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right two_pos (by nlinarith)
  have hexp : 2 * (n * k) = n * l + n * (2 * k - l) := by
    rw [← mul_add, Nat.add_sub_cancel' (by grind)]
    ring
  rw [mul_right_comm _ (2 ^ (n * (2 * k - l))), hexp, pow_add]
  exact Nat.mul_le_mul_right _ key

end CountingSetsWithSmallSumset
