/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import CountingSetsWithSmallSumset.BinaryLowerBound.SubspaceDimension
import CountingSetsWithSmallSumset.BinaryLowerBound.SubspacePairs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The covariance terms for subspaces of `𝔽₂ⁿ`

For a uniformly random `A ⊆ 𝔽₂ⁿ` and subspaces `H`, `H'`, the normalized indicators of
`H \ {0} ⊆ A` and `H' \ {0} ⊆ A` have covariance `2 ^ (2 ^ dim (H ∩ H') - 1) - 1`. This term
vanishes when `H ∩ H' = 0`. We bound the sum of these terms over the pairs of `k`-dimensional
subspaces by grouping the pairs by `dim (H ∩ H')` and applying Lemma 28 of Green.

## Main statements

* `mul_sum_sum_two_pow_sub_one_le`: under the inequalities of `exists_dim_of_two_pow_sixteen_le`,
  the sum of the covariance terms times `n * 2 ^ (2 * (k ^ 2 + k))` is at most `2 ^ (2 * n * k)`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Module

/-- A set `s` of at most `2 ^ (n * (2 * k - l))` pairs of subspaces with intersections of
dimension `l ≥ 1` contributes at most `2 ^ (2 * (n * k)) / (k + 1)` to the sum of the covariance
terms, times `n * 2 ^ (2 * (k ^ 2 + k))`. -/
private lemma mul_card_mul_two_pow_sub_one_le {n k l : ℕ} (hk : 2 * 2 ^ k ≤ n * k)
    (hkn : ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n) (hl₀ : 0 < l) (hl : l ≤ k)
    {s : Finset (Submodule (ZMod 2) (Fin n → ZMod 2) × Submodule (ZMod 2) (Fin n → ZMod 2))}
    (hs : (#s : ℝ) ≤ 2 ^ (n * (2 * k - l))) :
    (n : ℝ) * 2 ^ (2 * (k ^ 2 + k)) * (#s * ((2 : ℝ) ^ (2 ^ l - 1) - 1)) ≤
      2 ^ (2 * (n * k)) / (k + 1) := by
  rw [le_div_iff₀ (by positivity)]
  calc (n : ℝ) * 2 ^ (2 * (k ^ 2 + k)) * (#s * ((2 : ℝ) ^ (2 ^ l - 1) - 1)) * ((k : ℝ) + 1)
      = ((k : ℝ) + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * #s * ((2 : ℝ) ^ (2 ^ l - 1) - 1) := by ring
    _ ≤ ((k : ℝ) + 1) * n * 2 ^ (2 * (k ^ 2 + k)) * 2 ^ (n * (2 * k - l)) * 2 ^ 2 ^ l := by
      gcongr
      · linarith [one_le_pow₀ (one_le_two (α := ℝ)) (n := 2 ^ l - 1)]
      · linarith [pow_le_pow_right₀ (one_le_two (α := ℝ)) (Nat.sub_le (2 ^ l) 1)]
    _ ≤ 2 ^ (2 * (n * k)) := by exact_mod_cast succ_mul_mul_two_pow_mul_le hl₀ hl hk hkn

/-- The sum over the ordered pairs `(H, H')` of `k`-dimensional subspaces of `𝔽₂ⁿ` of the
covariance terms `2 ^ (2 ^ dim (H ∩ H') - 1) - 1`, times `n * 2 ^ (2 * (k ^ 2 + k))`, is at most
`2 ^ (2 * (n * k))`. -/
lemma mul_sum_sum_two_pow_sub_one_le {n k : ℕ} (hk : 2 * 2 ^ k ≤ n * k)
    (hkn : ((k + 1) * n) ^ 2 * 2 ^ (4 * (k ^ 2 + k)) ≤ 2 ^ n) :
    (n : ℝ) * 2 ^ (2 * (k ^ 2 + k)) *
      ∑ H ∈ ({H | finrank (ZMod 2) H = k} : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))),
        ∑ H' ∈ ({H | finrank (ZMod 2) H = k} : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))),
          ((2 : ℝ) ^ (2 ^ finrank (ZMod 2) ↥(H ⊓ H') - 1) - 1) ≤ 2 ^ (2 * (n * k)) := by
  set ℋ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2)) := {H | finrank (ZMod 2) H = k}
  rw [← sum_product', ← sum_fiberwise_of_maps_to' (M := ℝ) (s := ℋ ×ˢ ℋ) (t := range (k + 1))
    (g := fun (H, H') ↦ finrank (ZMod 2) ↥(H ⊓ H')) (f := fun l ↦ (2 : ℝ) ^ (2 ^ l - 1) - 1),
    mul_sum]
  · refine (sum_le_sum ?_).trans_eq (by simp [field] :
      ∑ _l ∈ range (k + 1), (2 : ℝ) ^ (2 * (n * k)) / (k + 1) = 2 ^ (2 * (n * k)))
    intro l hl
    rw [mem_range, Nat.lt_succ_iff] at hl
    rw [sum_const, nsmul_eq_mul]
    obtain rfl | hl₀ := Nat.eq_zero_or_pos l
    · simp only [pow_zero, tsub_self, sub_self, mul_zero]
      positivity
    refine mul_card_mul_two_pow_sub_one_le hk hkn hl₀ hl ?_
    norm_cast
    refine (card_le_card ?_).trans (card_finrank_inf_eq_le n hl)
    intro p hp
    simp_all [ℋ]
  · rintro ⟨H, H'⟩ hp
    obtain ⟨hH, -⟩ := mem_product.mp hp
    simp only [ℋ, mem_filter, mem_univ, true_and] at hH
    rw [mem_range, Nat.lt_succ_iff, ← hH]
    exact Submodule.finrank_mono inf_le_left

end CountingSetsWithSmallSumset
