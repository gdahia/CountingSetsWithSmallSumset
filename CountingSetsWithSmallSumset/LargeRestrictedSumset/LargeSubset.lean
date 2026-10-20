/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
import CountingSetsWithSmallSumset.LargeRestrictedSumset.SmallSubset

/-!
# A large subset whose restricted sumset is seven times larger

This file proves Corollary 20 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*: if `#A ≥ 46656`, then some `C ⊆ A` has `#C ≥ #A / 8` and
`#(restrictedSumset C) ≥ 7 * #C`. The paper assumes `#A` sufficiently large. Proposition 19 with
`ε = 1 / 9` gives `B ⊆ A` with `#B ≤ 27 * √#A` and `#(restrictedSumset B) ≥ 8 * #A / 9`. The set
`C` is `B` together with further elements of `A`, so that `#C = ⌈#A / 8⌉`.

## Main statements

* `exists_subset_seven_mul_card_le_card_restrictedSumset`: Corollary 20 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real

variable {G : Type*} [DecidableEq G]

/-- **Corollary 20** of Green. If `#A ≥ 46656`, then some `C ⊆ A` has `#A ≤ 8 * #C` and
`7 * #C ≤ #(restrictedSumset C)`. -/
lemma exists_subset_seven_mul_card_le_card_restrictedSumset [AddCommGroup G] {A : Finset G}
    (hA : 46656 ≤ #A) : ∃ C ⊆ A, #A ≤ 8 * #C ∧ 7 * #C ≤ #(restrictedSumset C) := by
  have hk : (46656 : ℝ) ≤ #A := by exact_mod_cast hA
  obtain ⟨B, hBA, hB, hS⟩ := exists_subset_card_le_sqrt_div_and_le_card_restrictedSumset
    (ε := 1 / 9) (by norm_num) (by norm_num) (A := A)
    (by norm_num [largeRestrictedSumsetThreshold]; linarith)
  have hsqrt : 216 ≤ √(#A) := (le_sqrt' (by norm_num)).mpr (by linarith)
  have hB8 : 8 * #B ≤ #A := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast
    nlinarith [sq_sqrt (Nat.cast_nonneg (α := ℝ) (#A))]
  have hS8 : 8 * #A ≤ 9 * #(restrictedSumset B) := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast
    linarith
  obtain ⟨C, hBC, hCA, hC⟩ := exists_subsuperset_card_eq hBA (n := (#A + 7) / 8) (by grind)
    (by grind)
  refine ⟨C, hCA, by grind, ?_⟩
  grw [← card_le_card (restrictedSumset_mono hBC)]
  grind

end CountingSetsWithSmallSumset
