/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CountingSetsWithSmallSumset.LargeRestrictedSumset.SubsetAveraging

/-!
# A small subset with a large restricted sumset

Let `A` be a finite subset of an additive commutative group with `#A = k`, and let
`0 < ε ≤ 1 / 2` with `k ≥ 16 / ε ^ 2`. Proposition 19 of Green, *Counting sets with small sumset,
and the clique number of random Cayley graphs*, gives `B ⊆ A` with
`#B ≤ 3 * logb 2 (1 / ε) / ε * √k` and `#(restrictedSumset B) ≥ (1 - ε) * k`.

The paper picks the elements of `B` independently with a fixed probability and uses a Chernoff
bound. Here `B` has exactly `n = ⌈2 * √k / ε⌉` elements. Averaging over all such subsets bounds
the number `N` of non-degenerate summing quadruples of some `B` by
`k ^ 3 * n.choose 4 / k.choose 4`. The Cauchy–Schwarz inequality
`(n * (n - 1)) ^ 2 ≤ #(restrictedSumset B) * (2 * n * (n - 1) + N)` then gives the lower bound.
This proves the stronger bound `#B ≤ 3 * √k / ε`.

## Main definitions

* `largeRestrictedSumsetThreshold ε`: the lower bound `16 / ε ^ 2` on `#A`.

## Main statements

* `exists_subset_card_le_sqrt_div_and_le_card_restrictedSumset`: the version with
  `#B ≤ 3 * √k / ε`.
* `exists_subset_card_le_and_le_card_restrictedSumset`: Proposition 19 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The lower bound on `#A` in Proposition 19 of Green. -/
noncomputable def largeRestrictedSumsetThreshold (ε : ℝ) : ℝ := 16 / ε ^ 2

private lemma twentyFour_mul_choose_four (n : ℕ) :
    (24 : ℝ) * n.choose 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  rcases n with _ | _ | _ | _ | m
  · simp
  · simp [Nat.choose_eq_zero_of_lt]
  · simp [Nat.choose_eq_zero_of_lt]
  · norm_num [Nat.choose_eq_zero_of_lt]
  rw [← Nat.cast_ofNat, ← Nat.cast_mul, (by rfl : 24 = (4).factorial),
    ← Nat.descFactorial_eq_factorial_mul_choose]
  push_cast [Nat.descFactorial_succ, Nat.descFactorial_zero]
  ring

private lemma mul_sub_one_le_of_mul_le {k b N : ℝ} (hb : 3 < b) (hbk : b ≤ k)
    (hN : N * (k * (k - 1) * (k - 2) * (k - 3)) ≤ k ^ 3 * (b * (b - 1) * (b - 2) * (b - 3))) :
    N * (k - 1) ≤ b * (b - 1) * b ^ 2 := by
  have h : k ^ 2 * ((b - 2) * (b - 3)) ≤ b ^ 2 * ((k - 2) * (k - 3)) := by
    nlinarith [mul_le_mul (by linarith : (b - 2) * k ≤ b * (k - 2))
      (by linarith : (b - 3) * k ≤ b * (k - 3)) (by nlinarith) (by nlinarith)]
  refine le_of_mul_le_mul_right ?_
    (mul_pos (by linarith) (mul_pos (by linarith) (by linarith)) : 0 < k * ((k - 2) * (k - 3)))
  nlinarith [mul_le_mul_of_nonneg_left h (by nlinarith : 0 ≤ k * (b * (b - 1)))]

private lemma mul_sub_one_le_mul_of_sq_le {k b S N : ℝ} (hb : 1 < b) (hk : 1 < k) (hS : 0 ≤ S)
    (hN : N * (k - 1) ≤ b * (b - 1) * b ^ 2)
    (hCS : (b * b - b) ^ 2 ≤ S * (2 * (b * b - b) + N)) :
    b * (b - 1) * (k - 1) ≤ S * (2 * (k - 1) + b ^ 2) := by
  refine le_of_mul_le_mul_left ?_ (by nlinarith : 0 < b * (b - 1))
  nlinarith [mul_le_mul_of_nonneg_right hCS (by linarith : 0 ≤ k - 1),
    mul_le_mul_of_nonneg_left hN hS]

private lemma one_sub_mul_mul_le {k b ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2)
    (hk : 16 ≤ k * ε ^ 2) (hb : 4 * k ≤ ε ^ 2 * b ^ 2) (hb₀ : 0 ≤ b) :
    (1 - ε) * k * (2 * (k - 1) + b ^ 2) ≤ b * (b - 1) * (k - 1) := by
  have hεk : 2 ≤ ε * k := by nlinarith
  have hεb : 8 * k ≤ ε * b ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hε₀.le (sq_nonneg b)) (by linarith : 0 ≤ 1 - 2 * ε)]
  nlinarith [mul_le_mul_of_nonneg_left hεk (sq_nonneg b),
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hε₀.le hb₀] : 4 ≤ ε * b)
      (by nlinarith : 0 ≤ b * k),
    mul_le_mul_of_nonneg_left hεb (by nlinarith : 0 ≤ k)]

private lemma one_sub_mul_le_of_bounds {k b S N ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2)
    (hk : 16 ≤ k * ε ^ 2) (hb : 4 * k ≤ ε ^ 2 * b ^ 2) (hb₃ : 3 < b) (hbk : b ≤ k) (hS : 0 ≤ S)
    (hN : N * (k * (k - 1) * (k - 2) * (k - 3)) ≤ k ^ 3 * (b * (b - 1) * (b - 2) * (b - 3)))
    (hCS : (b * b - b) ^ 2 ≤ S * (2 * (b * b - b) + N)) :
    (1 - ε) * k ≤ S := by
  refine le_of_mul_le_mul_right ?_ (by nlinarith : 0 < 2 * (k - 1) + b ^ 2)
  grw [one_sub_mul_mul_le hε₀ hε hk hb (by linarith)]
  exact mul_sub_one_le_mul_of_sq_le (by linarith) (by linarith) hS
    (mul_sub_one_le_of_mul_le hb₃ hbk hN) hCS

/-- If `0 < ε ≤ 1 / 2` and `#A ≥ 16 / ε ^ 2`, then some `B ⊆ A` has `#B ≤ 3 * √#A / ε` and
`#(restrictedSumset B) ≥ (1 - ε) * #A`. -/
lemma exists_subset_card_le_sqrt_div_and_le_card_restrictedSumset {ε : ℝ} (hε₀ : 0 < ε)
    (hε : ε ≤ 1 / 2) {A : Finset G} (hA : largeRestrictedSumsetThreshold ε ≤ #A) :
    ∃ B ⊆ A, #B ≤ 3 * √(#A) / ε ∧ (1 - ε) * #A ≤ #(restrictedSumset B) := by
  rw [largeRestrictedSumsetThreshold, div_le_iff₀ (by positivity)] at hA
  have hk := sq_sqrt (Nat.cast_nonneg (α := ℝ) (#A))
  have hεk : 4 ≤ ε * √(#A) := by nlinarith [mul_nonneg hε₀.le (sqrt_nonneg (#A))]
  have hn₁ : 2 * √(#A) ≤ ε * ⌈2 * √(#A) / ε⌉₊ := by
    rw [← div_le_iff₀' hε₀]
    exact Nat.le_ceil _
  have hn₂ : ε * ⌈2 * √(#A) / ε⌉₊ < 2 * √(#A) + ε := by
    rw [← lt_div_iff₀' hε₀, add_div, div_self hε₀.ne']
    exact Nat.ceil_lt_add_one (by positivity)
  obtain ⟨B, hBA, hBn, hBN⟩ := exists_card_eq_card_nondegenerateSummingQuadruples_mul_le
    (A := A) (n := ⌈2 * √(#A) / ε⌉₊) (by exact_mod_cast (by nlinarith : (4 : ℝ) ≤ ⌈2 * √(#A) / ε⌉₊))
    (by exact_mod_cast (by nlinarith : (⌈2 * √(#A) / ε⌉₊ : ℝ) ≤ #A))
  refine ⟨B, hBA, ?_, ?_⟩
  · rw [hBn, le_div_iff₀' hε₀]
    nlinarith
  · have hCS := (Nat.cast_le (α := ℝ)).mpr (sq_card_offDiag_le_card_restrictedSumset_mul B)
    have hN := (Nat.cast_le (α := ℝ)).mpr hBN
    rw [offDiag_card, hBn] at hCS
    push_cast [Nat.le_mul_self] at hCS hN
    refine one_sub_mul_le_of_bounds hε₀ hε hA
      (by nlinarith [mul_self_le_mul_self (by positivity) hn₁]) (by nlinarith) (by nlinarith)
      (Nat.cast_nonneg _) ?_ hCS
    rw [← twentyFour_mul_choose_four, ← twentyFour_mul_choose_four]
    linarith

/-- **Proposition 19** of Green. If `0 < ε ≤ 1 / 2` and `#A ≥ 16 / ε ^ 2`, then some `B ⊆ A` has
`#B ≤ 3 * logb 2 (1 / ε) / ε * √(#A)` and `#(restrictedSumset B) ≥ (1 - ε) * #A`. -/
theorem exists_subset_card_le_and_le_card_restrictedSumset {ε : ℝ} (hε₀ : 0 < ε)
    (hε : ε ≤ 1 / 2) {A : Finset G} (hA : largeRestrictedSumsetThreshold ε ≤ #A) :
    ∃ B ⊆ A, #B ≤ 3 * logb 2 (1 / ε) / ε * √(#A) ∧ (1 - ε) * #A ≤ #(restrictedSumset B) := by
  obtain ⟨B, hBA, hB, hS⟩ := exists_subset_card_le_sqrt_div_and_le_card_restrictedSumset hε₀ hε hA
  refine ⟨B, hBA, hB.trans ?_, hS⟩
  rw [(by ring : 3 * √(#A) / ε = 3 * 1 / ε * √(#A))]
  gcongr
  rw [le_logb_iff_rpow_le one_lt_two (by positivity), rpow_one, le_div_iff₀ hε₀]
  linarith

end CountingSetsWithSmallSumset
