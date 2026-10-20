/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CountingSetsWithSmallSumset.AlmostAllSets
import CountingSetsWithSmallSumset.BinaryGroups.LargeRestrictedSumsetSum
import CountingSetsWithSmallSumset.BinaryLowerBound.CliqueNumber
import CountingSetsWithSmallSumset.CliqueCount

/-!
# The clique number of random Cayley graphs on `𝔽₂ⁿ`

This file proves the upper bound of Theorem 9 of Green, *Counting sets with small sumset, and the
clique number of random Cayley graphs*, and combines it with Proposition 27 into Theorem 9. In
`𝔽₂ⁿ` the Cayley sum graph of `A` is the Cayley graph `SimpleGraph.addCayley A`. Write
`N = 2 ^ n`, so that `log₂ N = n` and `log₂ log₂ N = log₂ n`.

Let `X` be a clique of the Cayley graph of `A` of size greater than `308 * n * log₂ n`.
Corollary 20 gives `C ⊆ X` with `|X| ≤ 8 * |C|` and `|C ∔ C| ≥ 7 * |C|`. Then `C` is a clique, so
`C ∔ C ⊆ A`, and `|C| > 38 * n * log₂ n`. A set `R ⊆ 𝔽₂ⁿ` lies in `2 ^ (N - |R|)` sets `A`, so
the number of such `A` is at most `2 ^ N` times the sum of `|S_j^m(𝔽₂ⁿ)| / 2 ^ m` over
`38 * n * log₂ n < j ≤ N` and `7 * j ≤ m ≤ N`. Each inner sum is at most `N ^ (-2)`, so at most
`2 ^ N / N` sets `A` have clique number greater than `308 * n * log₂ n`.

## Main statements

* `card_cliqueNum_addCayley_gt_le`: the upper bound of Theorem 9 of Green, explicit form.
* `card_cliqueNum_addCayley_lt_or_gt_le`: Theorem 9 of Green, explicit form.
* `tendsto_card_le_cliqueNum_addCayley_le`: Theorem 9 of Green with `C₁ = 1 / 4` and
  `C₂ = 308`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real SimpleGraph Filter Topology

variable {n : ℕ}

private lemma cayleySumGraph_eq_addCayley_pi_zmod_two (A : Set (Fin n → ZMod 2)) :
    cayleySumGraph A = addCayley A := by
  refine cayleySumGraph_eq_addCayley ?_ A
  intro x
  ext i
  exact CharTwo.add_self_eq_zero (x i)

private lemma card_univ_pi_zmod_two : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  simp

private lemma two_pow_sixteen_le (hn : 2 ^ 9000 ≤ n) : 2 ^ 16 ≤ n :=
  (pow_le_pow_right₀ (by norm_num) (by norm_num)).trans hn

private lemma one_le_logb (hn : 2 ^ 9000 ≤ n) : 1 ≤ logb 2 n := by
  have h : 2 ≤ n := (Nat.le_self_pow (by norm_num) 2).trans hn
  rw [le_logb_iff_rpow_le one_lt_two (Nat.cast_pos.2 (zero_lt_two.trans_le h)), rpow_one]
  exact_mod_cast h

private lemma le_three_hundred_eight_mul_mul_logb (hn : 2 ^ 9000 ≤ n) :
    46656 ≤ 308 * n * logb 2 n := by
  have h : (46656 : ℝ) ≤ n := by
    exact_mod_cast (by norm_num : 46656 ≤ 2 ^ 16).trans (two_pow_sixteen_le hn)
  nlinarith [mul_le_mul_of_nonneg_left (one_le_logb hn) (Nat.cast_nonneg (α := ℝ) n)]

/-- **Theorem 9** of Green, upper bound, explicit form. If `n ≥ 2 ^ 9000`, then at most
`2 ^ 2 ^ n / 2 ^ n` of the `2 ^ 2 ^ n` sets `A ⊆ 𝔽₂ⁿ` have a Cayley graph with clique number
greater than `308 * n * log₂ n`. -/
lemma card_cliqueNum_addCayley_gt_le (hn : 2 ^ 9000 ≤ n) :
    (#{A : Finset (Fin n → ZMod 2) |
      308 * n * logb 2 n < (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum} : ℝ) ≤
      2 ^ 2 ^ n / 2 ^ n := by
  have hL : 0 ≤ n * logb 2 n := mul_nonneg (Nat.cast_nonneg n) (zero_le_one.trans (one_le_logb hn))
  simp_rw [← cayleySumGraph_eq_addCayley_pi_zmod_two]
  refine (card_lt_cliqueNum_cayleySumGraph_le (le_three_hundred_eight_mul_mul_logb hn)).trans ?_
  rw [card_univ_pi_zmod_two]
  refine (mul_le_mul_of_nonneg_left (sum_le_card_nsmul _ _ (1 / ((2 : ℝ) ^ n) ^ 2) ?_)
    (by positivity)).trans ?_
  · intro j hj
    obtain ⟨-, hjL⟩ := mem_filter.1 hj
    exact sum_card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le hn
      (by linarith only [hL, hjL])
  · rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.2
      ((card_filter_le _ _).trans (by simp : #(Icc 1 (2 ^ n)) ≤ 2 ^ n))) (by positivity))
        (by positivity)).trans_eq ?_
    push_cast
    field_simp

/-- **Theorem 9** of Green, explicit form. If `n ≥ 2 ^ 9000`, then at most
`2 ^ 2 ^ n / n + 2 ^ 2 ^ n / 2 ^ n` of the `2 ^ 2 ^ n` sets `A ⊆ 𝔽₂ⁿ` have a Cayley graph with
clique number less than `n * log₂ n / 4` or greater than `308 * n * log₂ n`. -/
theorem card_cliqueNum_addCayley_lt_or_gt_le (hn : 2 ^ 9000 ≤ n) :
    (#{A : Finset (Fin n → ZMod 2) |
      (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * logb 2 n / 4 ∨
        308 * n * logb 2 n < (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum} : ℝ) ≤
      2 ^ 2 ^ n / n + 2 ^ 2 ^ n / 2 ^ n := by
  rw [filter_or]
  refine (Nat.cast_le.2 (card_union_le _ _)).trans ?_
  push_cast
  exact add_le_add (card_cliqueNum_addCayley_lt_le (two_pow_sixteen_le hn))
    (card_cliqueNum_addCayley_gt_le hn)

/-- **Theorem 9** of Green, with `C₁ = 1 / 4` and `C₂ = 308`. The proportion of the sets
`A ⊆ 𝔽₂ⁿ` whose Cayley graph has clique number between `n * log₂ n / 4` and `308 * n * log₂ n`
tends to `1`. -/
theorem tendsto_card_le_cliqueNum_addCayley_le :
    Tendsto (fun n : ℕ ↦ (#{A : Finset (Fin n → ZMod 2) |
      n * logb 2 n / 4 ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum ∧
        (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum ≤ 308 * n * logb 2 n} : ℝ) / 2 ^ 2 ^ n)
      atTop (𝓝 1) := by
  refine tendsto_card_filter_div_two_pow_of_card_filter_not_le (fun _ ↦ card_univ_pi_zmod_two) _
    (ε := fun n ↦ (n : ℝ)⁻¹ + ((2 : ℝ) ^ n)⁻¹) ?_ ?_
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).add
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  · filter_upwards [eventually_ge_atTop (2 ^ 9000)] with n hn
    simp only [not_and_or, not_le]
    exact (card_cliqueNum_addCayley_lt_or_gt_le hn).trans_eq (by ring)

end CountingSetsWithSmallSumset
