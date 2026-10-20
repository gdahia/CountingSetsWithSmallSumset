/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import SumOfSetsInSeveralDimensions.FreimanDimension
import SumOfSetsInSeveralDimensions.AffineDimSumset
import SumOfSetsInSeveralDimensions.ClosedForm
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

* `freimanDim_add_one_le_card`: a nonempty set `S` has Freiman dimension at most `|S| - 1`.
* `card_add_mul_card_sub_le_card_add_of_freimanDim`: Freiman's lemma for the full sumset.
* `freimanDim_mul_le_card_restrictedSumset`: Lemma 21 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

variable {G : Type*} [DecidableEq G]

/-- A nonempty set `S` has Freiman dimension at most `|S| - 1`. -/
lemma freimanDim_add_one_le_card [AddCommMonoid G] {S : Finset G} (hS : S.Nonempty) :
    freimanDim S + 1 ≤ #S := by
  classical
  by_cases h : freimanDim S = 0
  · grind [hS.card_pos]
  obtain ⟨f, -, hdim⟩ : freimanModelDim S (freimanDim S) := Nat.findGreatest_of_ne_zero rfl h
  grind [affineDim_add_one_le_card ((hS.image f).image rationalVectorToReal),
    card_image_le (s := S) (f := f),
    card_image_le (s := S.image f) (f := rationalVectorToReal)]

/-- Freiman's lemma for the full sumset, in terms of the Freiman dimension. -/
lemma card_add_mul_card_sub_le_card_add_of_freimanDim [AddCommMonoid G] {S : Finset G}
    (hS : S.Nonempty) (hr : freimanDim S ≠ 0) :
    (#S : ℝ) + freimanDim S * #S - freimanDim S * (freimanDim S + 1) / 2 ≤ #(S + S) := by
  classical
  obtain ⟨f, hf, hdim⟩ : freimanModelDim S (freimanDim S) := Nat.findGreatest_of_ne_zero rfl hr
  have hg := isAddFreimanIso_rationalVectorToReal_comp hf
  rw [image_image] at hdim
  have h := card_add_mul_card_sub_le_card_add (hS.image _) le_rfl
    ((affineDim_le_affineDim_add_left (hS.image _) _).trans' hdim.ge)
  rwa [card_image_of_injOn hg.bijOn.injOn, card_add_image_of_isAddFreimanIso hg subset_rfl
    subset_rfl] at h

/-- **Lemma 21** of Green (Freiman). If `S` is a finite subset of an abelian group with Freiman
dimension `r`, then `|S ∔ S| ≥ r * (|S| - (r + 1) / 2)`. -/
lemma freimanDim_mul_le_card_restrictedSumset [AddCommMonoid G] (S : Finset G) :
    (freimanDim S : ℝ) * (#S - (freimanDim S + 1) / 2) ≤ #(restrictedSumset S) := by
  obtain hS | hS := S.eq_empty_or_nonempty
  · simp [hS, freimanDim]
  by_cases hr : freimanDim S = 0
  · simp [hr]
  linarith [card_add_mul_card_sub_le_card_add_of_freimanDim hS hr,
    (mod_cast card_add_le_card_restrictedSumset_add_card S :
      (#(S + S) : ℝ) ≤ #(restrictedSumset S) + #S)]

end CountingSetsWithSmallSumset
