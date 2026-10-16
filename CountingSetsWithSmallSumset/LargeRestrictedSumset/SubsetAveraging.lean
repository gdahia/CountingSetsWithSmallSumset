/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.LargeRestrictedSumset.SummingQuadruples
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Subsets with few non-degenerate summing quadruples

Let `A` be a finite subset of an additive commutative group and let `4 ≤ n ≤ #A`. A
non-degenerate summing quadruple of `A` has four distinct entries, so it lies in exactly
`(#A - 4).choose (n - 4)` subsets of `A` with `n` elements. Averaging over these subsets, some
`B ⊆ A` with `#B = n` has at most `#A ^ 3 * n.choose 4 / (#A).choose 4` non-degenerate summing
quadruples.

## Main statements

* `sum_card_nondegenerateSummingQuadruples_powersetCard`: the sum over the `n`-element subsets
  `B ⊆ A` of the number of non-degenerate summing quadruples of `B`.
* `exists_card_eq_card_nondegenerateSummingQuadruples_mul_le`: some `B ⊆ A` with `#B = n` has
  `#(nondegenerateSummingQuadruples B) * (#A).choose 4 ≤ #A ^ 3 * n.choose 4`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

lemma nondegenerateSummingQuadruples_eq_filter {A B : Finset G} (hBA : B ⊆ A) :
    nondegenerateSummingQuadruples B =
      (nondegenerateSummingQuadruples A).filter fun ((a, b), (c, d)) ↦ {a, b, c, d} ⊆ B := by
  ext ⟨⟨a, b⟩, c, d⟩
  simp only [nondegenerateSummingQuadruples, mem_filter, mem_product, mem_offDiag,
    insert_subset_iff, singleton_subset_iff]
  grind

/-- The sum over the `n`-element subsets `B ⊆ A` of the number of non-degenerate summing
quadruples of `B`. -/
lemma sum_card_nondegenerateSummingQuadruples_powersetCard (A : Finset G) {n : ℕ} (hn : 4 ≤ n) :
    ∑ B ∈ A.powersetCard n, #(nondegenerateSummingQuadruples B) =
      #(nondegenerateSummingQuadruples A) * (#A - 4).choose (n - 4) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := A.powersetCard n)
    (t := nondegenerateSummingQuadruples A)
    (r := fun B ((a, b), (c, d)) ↦ ({a, b, c, d} : Finset G) ⊆ B)
  simp only [bipartiteAbove, bipartiteBelow] at h
  have hfilter (B : Finset G) (hB : B ∈ A.powersetCard n) :
      #(nondegenerateSummingQuadruples B) = #((nondegenerateSummingQuadruples A).filter
        fun ((a, b), (c, d)) ↦ ({a, b, c, d} : Finset G) ⊆ B) := by
    obtain ⟨hBA, -⟩ := mem_powersetCard.mp hB
    rw [nondegenerateSummingQuadruples_eq_filter hBA]
  rw [sum_congr rfl hfilter, h, sum_const_nat]
  rintro ⟨⟨a, b⟩, c, d⟩ hq
  have h4 := card_entries_eq_four_of_mem_nondegenerateSummingQuadruples hq
  rw [← h4, card_filter_powersetCard_subset _ _ _ ?_ (by grind)]
  simp only [nondegenerateSummingQuadruples, mem_filter, mem_product, mem_offDiag] at hq
  simp only [insert_subset_iff, singleton_subset_iff]
  grind

/-- Some `n`-element subset `B ⊆ A` has at most `#A ^ 3 * n.choose 4 / (#A).choose 4`
non-degenerate summing quadruples. -/
lemma exists_card_eq_card_nondegenerateSummingQuadruples_mul_le {A : Finset G} {n : ℕ}
    (hn : 4 ≤ n) (hnA : n ≤ #A) :
    ∃ B ⊆ A, #B = n ∧
      #(nondegenerateSummingQuadruples B) * (#A).choose 4 ≤ #A ^ 3 * n.choose 4 := by
  have hsum : ∑ B ∈ A.powersetCard n, #(nondegenerateSummingQuadruples B) * (#A).choose n ≤
      ∑ _B ∈ A.powersetCard n, #(nondegenerateSummingQuadruples A) * (#A - 4).choose (n - 4) := by
    rw [← sum_mul, sum_card_nondegenerateSummingQuadruples_powersetCard A hn,
      sum_const_nat fun _ _ ↦ rfl, card_powersetCard]
    grind
  obtain ⟨B, hB, hle⟩ := exists_le_of_sum_le (powersetCard_nonempty.mpr hnA) hsum
  obtain ⟨hBA, hBn⟩ := mem_powersetCard.mp hB
  refine ⟨B, hBA, hBn, Nat.le_of_mul_le_mul_right ?_ (Nat.choose_pos (by grind : n - 4 ≤ #A - 4))⟩
  grw [mul_assoc, ← Nat.choose_mul hn, ← mul_assoc, Nat.mul_le_mul_right _ hle,
    card_nondegenerateSummingQuadruples_le]
  grind

end CountingSetsWithSmallSumset
