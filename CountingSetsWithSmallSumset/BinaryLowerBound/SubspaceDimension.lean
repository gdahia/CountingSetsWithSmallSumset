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
    rw [pow_succ]
    nlinarith [Nat.pow_le_pow_right two_pos hlk, Nat.mul_le_mul_right (2 ^ k) hl]

/-- `16 * m ^ 2 + 14 * m + 4 ≤ 2 ^ m` for `m ≥ 16`. -/
lemma sixteen_mul_sq_add_le_two_pow {m : ℕ} (hm : 16 ≤ m) : 16 * m ^ 2 + 14 * m + 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 2 m]
    nlinarith

/-- Every natural number `N ≥ 2` satisfies `2 ^ (k + 1) ≤ N < 2 ^ (k + 2)` for some `k`. -/
private lemma exists_two_pow_succ_le_lt {N : ℕ} (hN : 2 ≤ N) :
    ∃ k, 2 ^ (k + 1) ≤ N ∧ N < 2 ^ (k + 2) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one.2 (Nat.log_pos one_lt_two hN)
  refine ⟨k, hk ▸ Nat.pow_log_le_self 2 (by grind), ?_⟩
  simpa [hk] using Nat.lt_pow_succ_log_self one_lt_two N

/-- If `16 ≤ m`, `2 ^ m ≤ n < 2 ^ (m + 1)` and `2 ^ (k + 1) ≤ n * (m + 1) < 2 ^ (k + 2)`, then
`m + 3 ≤ k ≤ 2 * m`. -/
private lemma add_three_le_and_le_two_mul {n m k : ℕ} (hm : 16 ≤ m) (hmn : 2 ^ m ≤ n)
    (hnm : n < 2 ^ (m + 1)) (hkn : 2 ^ (k + 1) ≤ n * (m + 1)) (hnk : n * (m + 1) < 2 ^ (k + 2)) :
    m + 3 ≤ k ∧ k ≤ 2 * m := by
  constructor
  · have h : 2 ^ (m + 4) < 2 ^ (k + 2) := by nlinarith [pow_add 2 m 4]
    rw [Nat.pow_lt_pow_iff_right one_lt_two] at h
    grind
  · have h := hkn.trans_lt (Nat.mul_lt_mul'' hnm Nat.lt_two_pow_self)
    rw [← pow_add, Nat.pow_lt_pow_iff_right one_lt_two] at h
    grind

/-- If `16 ≤ m`, `k ≤ 2 * m` and `2 ^ m ≤ n < 2 ^ (m + 1)`, then
`((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n`. -/
private lemma succ_mul_sq_mul_two_pow_le {n m k : ℕ} (hm : 16 ≤ m) (hkm : k ≤ 2 * m)
    (hmn : 2 ^ m ≤ n) (hnm : n < 2 ^ (m + 1)) :
    ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n := by
  have hkn : (k + 1) * n ≤ 2 ^ (3 * m + 2) := by
    rw [(by ring : 3 * m + 2 = (2 * m + 1) + (m + 1)), pow_add]
    exact Nat.mul_le_mul ((by grind : k + 1 ≤ 2 * m + 1).trans Nat.lt_two_pow_self.le) hnm.le
  refine (Nat.mul_le_mul (Nat.pow_le_pow_left hkn 2)
    (Nat.pow_le_pow_right two_pos (by nlinarith : 4 * (k ^ 2 + k) ≤ 16 * m ^ 2 + 8 * m))).trans ?_
  rw [← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right two_pos (by linarith [sixteen_mul_sq_add_le_two_pow hm])

/-- If `n * (⌊log₂ n⌋ + 1) < 2 ^ (k + 2)`, then `n * log₂ n / 4 ≤ 2 ^ k`. -/
private lemma mul_logb_div_four_le_two_pow {n k : ℕ} (hnk : n * (Nat.log 2 n + 1) < 2 ^ (k + 2)) :
    n * Real.logb 2 n / 4 ≤ 2 ^ k := by
  have hlog : Real.logb 2 n < Nat.log 2 n + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Real.logb 2 n)
  have h4 : (n : ℝ) * (Nat.log 2 n + 1) < 2 ^ k * 2 ^ 2 := by
    exact_mod_cast pow_add 2 k 2 ▸ hnk
  nlinarith [mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg (α := ℝ) n)]

/-- For `n ≥ 2 ^ 16` there is a `k ≤ n` with `n * log₂ n / 4 ≤ 2 ^ k`, `2 * 2 ^ k ≤ n * k` and
`((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n`. -/
lemma exists_dim_of_two_pow_sixteen_le {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    ∃ k, k ≤ n ∧ n * Real.logb 2 n / 4 ≤ 2 ^ k ∧ 2 * 2 ^ k ≤ n * k ∧
      ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n := by
  have hm : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  have hmn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by grind)
  have hnm : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self one_lt_two n
  obtain ⟨k, hkn, hnk⟩ := exists_two_pow_succ_le_lt (by nlinarith : 2 ≤ n * (Nat.log 2 n + 1))
  obtain ⟨hmk, hkm⟩ := add_three_le_and_le_two_mul hm hmn hnm hkn hnk
  refine ⟨k, ?_, mul_logb_div_four_le_two_pow hnk, ?_, succ_mul_sq_mul_two_pow_le hm hkm hmn hnm⟩
  · nlinarith [sixteen_mul_sq_add_le_two_pow hm]
  · nlinarith [pow_succ' 2 k]

/-- If `1 ≤ l`, `2 * 2 ^ l ≤ n * l` and `((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n`, then
`(k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ 2 ^ l ≤ 2 ^ (n * l)`. -/
private lemma succ_mul_mul_two_pow_le {n k l : ℕ} (hl : 1 ≤ l) (hln : 2 * 2 ^ l ≤ n * l)
    (hkn : ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n) :
    (k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ 2 ^ l ≤ 2 ^ (n * l) := by
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
  rw [(by ring : ((k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ 2 ^ l) ^ 2 =
    ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) * 2 ^ (2 ^ l * 2)), ← pow_mul]
  refine (Nat.mul_le_mul hkn
    (Nat.pow_le_pow_right two_pos (by grind : 2 ^ l * 2 ≤ n * l))).trans ?_
  rw [← pow_add]
  exact Nat.pow_le_pow_right two_pos (by nlinarith)

/-- If `1 ≤ l ≤ k`, `2 * 2 ^ k ≤ n * k` and `((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n`,
then `(k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ (n * (2 * k - l)) * 2 ^ 2 ^ l ≤ 2 ^ (2 * (n * k))`.
-/
lemma succ_mul_mul_two_pow_mul_le {n k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) (hk : 2 * 2 ^ k ≤ n * k)
    (hkn : ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n) :
    (k + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ (n * (2 * k - l)) * 2 ^ 2 ^ l ≤
      2 ^ (2 * (n * k)) := by
  have hexp : 2 * (n * k) = n * l + n * (2 * k - l) := by
    rw [← mul_add, Nat.add_sub_cancel' (by grind)]
    ring
  rw [mul_right_comm _ (2 ^ (n * (2 * k - l))), hexp, pow_add]
  refine Nat.mul_le_mul_right _ (succ_mul_mul_two_pow_le hl ?_ hkn)
  exact Nat.le_of_mul_le_mul_right
    (by nlinarith [mul_two_pow_le_mul_two_pow hl hlk, Nat.mul_le_mul_left l hk]) (by grind : 0 < k)

end CountingSetsWithSmallSumset
