/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import SumOfSetsInSeveralDimensions.FreimanDimension
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds
import Mathlib.Tactic.Linarith

/-!
# Freiman's lemma for the restricted sumset

Let `S` be a finite subset of an abelian group with Freiman dimension `r`. Then
`|S ∔ S| ≥ r * (|S| - (r + 1) / 2)`. This is Lemma 21 of Green, *Counting sets with small sumset,
and the clique number of random Cayley graphs*, which is due to Freiman. A Freiman model `T` of `S`
in `ℚ^r ⊆ ℝ^r` has `|T + T| = |S + S|` and affine dimension `r`, so Freiman's lemma for the full
sumset gives `|S + S| ≥ (r + 1) * |S| - r * (r + 1) / 2`. The full sumset has at most `|S|`
elements more than the restricted one.

## Main statements

* `freimanDim_mul_le_card_restrictedSumset`: Lemma 21 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

variable {G : Type*} [DecidableEq G]

/-- **Lemma 21** of Green (Freiman). If `S` is a finite subset of an abelian group with Freiman
dimension `r`, then `|S ∔ S| ≥ r * (|S| - (r + 1) / 2)`. -/
lemma freimanDim_mul_le_card_restrictedSumset [AddCommMonoid G] (S : Finset G) :
    (freimanDim S : ℝ) * (#S - (freimanDim S + 1) / 2) ≤ #(restrictedSumset S) := by
  obtain hS | hS := S.eq_empty_or_nonempty
  · simp [hS, freimanDim]
  by_cases hr : freimanDim S = 0
  · simp [hr]
  obtain ⟨f, hf, hdim⟩ := exists_isAddFreimanIso_of_freimanDim_eq rfl hr
  have h : (2 * (#S + freimanDim S * #S) : ℝ) ≤ 2 * #(S + S) + freimanDim S * (freimanDim S + 1) :=
    mod_cast two_mul_card_add_mul_card_le_of_isAddFreimanIso hS hf hdim
  linarith [(mod_cast card_add_le_card_restrictedSumset_add_card S :
    (#(S + S) : ℝ) ≤ #(restrictedSumset S) + #S)]

end CountingSetsWithSmallSumset
