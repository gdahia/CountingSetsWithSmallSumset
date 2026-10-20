/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.CayleySumGraph
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CountingSetsWithSmallSumset.AlmostAllSets
import CountingSetsWithSmallSumset.CliqueCount
import CountingSetsWithSmallSumset.CyclicGroups.LargeRestrictedSumsetSum

/-!
# The clique number of random Cayley sum graphs on `ℤ_N`

This file proves Theorem 7 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*: at most `2 ^ N / N` sets `A ⊆ ℤ_N` have a Cayley sum graph `G_A` with
clique number greater than `160 * log₂ N`. The number of such `A` is at most `2 ^ N` times the sum
of `|S_j^m(ℤ_N)| / 2 ^ m` over `20 * log₂ N < j ≤ N` and `7 * j ≤ m ≤ N`. Each inner sum is at
most `N ^ (-2)`. Hence the proportion of the sets `A ⊆ ℤ_N` with clique number at most
`160 * log₂ N` tends to `1`, which is the statement of the paper.

## Main statements

* `card_cliqueNum_cayleySumGraph_gt_le`: Theorem 7 of Green, explicit form.
* `tendsto_card_cliqueNum_cayleySumGraph_le`: Theorem 7 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real SimpleGraph Filter Topology

variable {N : ℕ} [NeZero N]

/-- **Theorem 7** of Green, explicit form. If `log₂ N ≥ 2 ^ 9000`, then at most `2 ^ N / N` sets
`A ⊆ ℤ_N` have a Cayley sum graph with clique number greater than `160 * log₂ N`. -/
theorem card_cliqueNum_cayleySumGraph_gt_le (hN : 2 ^ 9000 ≤ logb 2 N) :
    (#{A : Finset (ZMod N) | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).cliqueNum} :
      ℝ) ≤ 2 ^ N / N := by
  have hL : (46656 : ℝ) ≤ 160 * logb 2 N :=
    ((by norm_num : (46656 : ℝ) ≤ 160 * 2 ^ 9).trans
      (by gcongr <;> norm_num : (160 : ℝ) * 2 ^ 9 ≤ 160 * 2 ^ 9000)).trans
        (mul_le_mul_of_nonneg_left hN (by norm_num))
  refine (card_lt_cliqueNum_cayleySumGraph_le hL).trans ?_
  rw [ZMod.card]
  refine (mul_le_mul_of_nonneg_left (sum_le_card_nsmul _ _ (1 / (N : ℝ) ^ 2) ?_)
    (by positivity)).trans ?_
  · intro j hj
    obtain ⟨-, hjL⟩ := mem_filter.1 hj
    refine sum_card_restrictedSumsetCardSets_zmod_div_two_pow_le ?_ (by linarith only [hjL])
    exact_mod_cast hN.trans (by linarith only [hL, hjL] : logb 2 N ≤ j)
  · rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.2
      ((card_filter_le _ _).trans (by simp : #(Icc 1 N) ≤ N))) (by positivity))
        (by positivity)).trans_eq ?_
    field_simp

private lemma two_pow_le_logb_of_two_pow_two_pow_le {x : ℝ} (hx : 2 ^ 2 ^ 9000 ≤ x) :
    2 ^ 9000 ≤ logb 2 x := by
  rw [le_logb_iff_rpow_le one_lt_two ((pow_pos two_pos _).trans_le hx)]
  rwa [← rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] at hx

/-- **Theorem 7** of Green. The proportion of the sets `A ⊆ ℤ_N` whose Cayley sum graph has clique
number at most `160 * log₂ N` tends to `1`. -/
theorem tendsto_card_cliqueNum_cayleySumGraph_le :
    Tendsto (fun N : ℕ+ ↦ (#{A : Finset (ZMod N) |
      (cayleySumGraph (A : Set (ZMod N))).cliqueNum ≤ 160 * logb 2 N} : ℝ) / 2 ^ (N : ℕ))
      atTop (𝓝 1) := by
  refine tendsto_card_filter_div_two_pow_of_card_filter_not_le (fun N : ℕ+ ↦ ZMod.card N) _
    (ε := fun N : ℕ+ ↦ ((N : ℕ) : ℝ)⁻¹)
    (tendsto_inv_atTop_nhds_zero_nat.comp tendsto_PNat_val_atTop_atTop) ?_
  filter_upwards [(tendsto_natCast_atTop_atTop.comp
    tendsto_PNat_val_atTop_atTop).eventually_ge_atTop ((2 : ℝ) ^ 2 ^ 9000)] with N hN
  simp only [not_le]
  exact (card_cliqueNum_cayleySumGraph_gt_le (two_pow_le_logb_of_two_pow_two_pow_le hN)).trans_eq
    (by ring)

end CountingSetsWithSmallSumset
