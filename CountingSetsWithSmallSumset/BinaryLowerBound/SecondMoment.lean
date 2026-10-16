/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The second moment method for a uniformly random set

Let `α` be a finite type and let `B i`, for `i ∈ s`, be subsets of `α`. If `A ⊆ α` is uniformly
random, the variable `X = #{i ∈ s | B i ⊆ A}` has `𝔼 [2 ^ |B i| * 1_{B i ⊆ A}] = 1` for every `i`,
and the covariance of the `i`-th and `j`-th of these normalized indicators is
`2 ^ |B i ∩ B j| - 1`. Chebyshev's inequality then bounds the probability that `A` contains none
of the `B i`. We write the argument as a count over the `2 ^ |α|` sets `A`.

## Main statements

* `card_filter_superset`: there are `2 ^ (|α| - |B|)` sets `A ⊆ α` containing `B`.
* `card_filter_forall_not_subset_mul_sq_le`: the number of sets `A ⊆ α` containing none of the
  `B i` times `|s| ^ 2` is at most `2 ^ |α| * ∑ i ∈ s, ∑ j ∈ s, (2 ^ |B i ∩ B j| - 1)`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma card_filter_superset (B : Finset α) :
    #{A : Finset α | B ⊆ A} = 2 ^ (Fintype.card α - #B) := by
  rw [← card_compl, ← card_powerset]
  refine card_nbij' (· \ B) (· ∪ B) ?_ ?_ ?_ ?_ <;> intro A hA
  · simp
  · simp
  · simp_all
  · simp_all [Set.subset_compl_iff_disjoint_right, union_sdiff_cancel_right]

/-- The sum over all `A ⊆ α` of the product of the normalized indicators of `B ⊆ A` and
`C ⊆ A`, both centered, is `2 ^ |α| * (2 ^ |B ∩ C| - 1)`. -/
lemma sum_centered_indicator_mul (B C : Finset α) :
    ∑ A : Finset α, ((if B ⊆ A then (2 : ℝ) ^ #B else 0) - 1) *
      ((if C ⊆ A then (2 : ℝ) ^ #C else 0) - 1) =
      2 ^ Fintype.card α * (2 ^ #(B ∩ C) - 1) := by
  trans ∑ A : Finset α, ((if B ∪ C ⊆ A then (2 : ℝ) ^ (#B + #C) else 0) -
    (if B ⊆ A then (2 : ℝ) ^ #B else 0) - (if C ⊆ A then (2 : ℝ) ^ #C else 0) + 1)
  · congr with A
    by_cases hB : B ⊆ A <;> by_cases hC : C ⊆ A <;>
      simp [hB, hC, union_subset_iff, pow_add] <;> grind
  have key (D : Finset α) (m : ℕ) (h : #D ≤ m + Fintype.card α) :
      (2 : ℝ) ^ m * 2 ^ (Fintype.card α - #D) = 2 ^ (Fintype.card α + m - #D) := by
    rw [← pow_add]
    grind [card_le_univ D]
  have hBC := card_union_add_card_inter B C
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_filter, sum_const, nsmul_eq_mul,
    card_filter_superset, card_univ, Fintype.card_finset]
  push_cast
  rw [mul_comm _ ((2 : ℝ) ^ (#B + #C)), mul_comm _ ((2 : ℝ) ^ #B), mul_comm _ ((2 : ℝ) ^ #C),
    key _ _ (by grind), key _ _ (by grind), key _ _ (by grind),
    (by grind : Fintype.card α + (#B + #C) - #(B ∪ C) = Fintype.card α + #(B ∩ C)),
    Nat.add_sub_cancel, Nat.add_sub_cancel, pow_add]
  ring

/-- Chebyshev's inequality for the number of `i ∈ s` with `B i ⊆ A`, for a uniformly random
`A ⊆ α`, written as a count over the sets `A`. -/
lemma card_filter_forall_not_subset_mul_sq_le {ι : Type*} (s : Finset ι) (B : ι → Finset α) :
    #{A : Finset α | ∀ i ∈ s, ¬B i ⊆ A} * (#s : ℝ) ^ 2 ≤
      2 ^ Fintype.card α * ∑ i ∈ s, ∑ j ∈ s, (2 ^ #(B i ∩ B j) - 1) := by
  set f : ι → Finset α → ℝ := fun i A ↦ (if B i ⊆ A then (2 : ℝ) ^ #(B i) else 0) - 1
  have hf (A : Finset α) (hA : A ∈ ({A : Finset α | ∀ i ∈ s, ¬B i ⊆ A} : Finset _)) :
      (#s : ℝ) ^ 2 = (∑ i ∈ s, f i A) ^ 2 := by
    obtain ⟨-, hA⟩ := mem_filter.mp hA
    simp [f, sum_sub_distrib, sum_ite_of_false hA]
  rw [← nsmul_eq_mul, ← sum_const, sum_congr rfl hf]
  trans ∑ A : Finset α, (∑ i ∈ s, f i A) ^ 2
  · apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro A _ _
    exact sq_nonneg _
  apply le_of_eq
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  congr with i
  rw [sum_comm]
  congr with j
  exact sum_centered_indicator_mul (B i) (B j)

end CountingSetsWithSmallSumset
