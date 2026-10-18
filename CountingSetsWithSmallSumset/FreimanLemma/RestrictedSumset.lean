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
in `ℚ^r ⊆ ℝ^r` has `|T + T| ≤ |S + S|` and affine dimension `r`, so Freiman's lemma for the full
sumset gives `|S + S| ≥ (r + 1) * |S| - r * (r + 1) / 2`. The full sumset has at most `|S|`
elements more than the restricted one.

## Main statements

* `card_image_add_image_le_card_add`: a Freiman homomorphism of order `2` does not increase the
  size of the sumset.
* `freimanDim_add_one_le_card`: a nonempty set `S` has Freiman dimension at most `|S| - 1`.
* `card_add_mul_card_sub_le_card_add_of_freimanDim`: Freiman's lemma for the full sumset.
* `freimanDim_mul_le_card_restrictedSumset`: Lemma 21 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

variable {G H : Type*} [DecidableEq G] [DecidableEq H]

/-- A Freiman homomorphism of order `2` from `S` maps `S + S` onto the sumset of the image. -/
lemma card_image_add_image_le_card_add [AddCommMonoid G] [AddCommMonoid H] {S : Finset G}
    {f : G → H} (hf : IsAddFreimanHom 2 (S : Set G) (S.image f : Set H) f) :
    #(S.image f + S.image f) ≤ #(S + S) := by
  have h : ∀ x ∈ S + S, ∃ a ∈ S, ∃ b ∈ S, a + b = x := fun x hx ↦ mem_add.1 hx
  choose! a ha b hb hab using h
  refine card_le_card_of_surjOn (fun x ↦ f (a x) + f (b x)) ?_
  intro y hy
  simp only [mem_coe, mem_add, mem_image] at hy
  obtain ⟨_, ⟨c, hc, rfl⟩, _, ⟨d, hd, rfl⟩, rfl⟩ := hy
  have hcd : c + d ∈ S + S := add_mem_add hc hd
  exact ⟨c + d, hcd, hf.add_eq_add (ha _ hcd) (hb _ hcd) hc hd (hab _ hcd)⟩

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
  set g := rationalVectorToReal ∘ f
  have hg : IsAddFreimanHom 2 (S : Set G) (S.image g : Set (Fin (freimanDim S) → ℝ)) g := by
    refine isAddFreimanHom_two.2 ⟨fun a ha ↦ mem_coe.2 (mem_image_of_mem g ha), ?_⟩
    intro a ha b hb c hc d hd h
    simp only [g, Function.comp_apply, ← rationalVectorToReal_add,
      (hf.add_eq_add ha hb hc hd).2 h]
  have hcard : #(S.image g) = #S :=
    card_image_of_injOn (rationalVectorToReal_injective.comp_injOn hf.bijOn.injOn)
  rw [image_image] at hdim
  have h := card_add_mul_card_sub_le_card_add (A := S.image g) (B := S.image g) (hS.image g) le_rfl
    ((affineDim_le_affineDim_add_left (hS.image g) _).trans' hdim.ge)
  rw [hcard] at h
  exact h.trans (mod_cast card_image_add_image_le_card_add hg)

/-- **Lemma 21** of Green (Freiman). If `S` is a finite subset of an abelian group with Freiman
dimension `r`, then `|S ∔ S| ≥ r * (|S| - (r + 1) / 2)`. -/
theorem freimanDim_mul_le_card_restrictedSumset [AddCommMonoid G] (S : Finset G) :
    (freimanDim S : ℝ) * (#S - (freimanDim S + 1) / 2) ≤ #(restrictedSumset S) := by
  obtain hS | hS := S.eq_empty_or_nonempty
  · simp [hS, freimanDim]
  by_cases hr : freimanDim S = 0
  · simp [hr]
  linarith [card_add_mul_card_sub_le_card_add_of_freimanDim hS hr,
    (mod_cast card_add_le_card_restrictedSumset_add_card S :
      ((#(S + S) : ℕ) : ℝ) ≤ #(restrictedSumset S) + #S)]

end CountingSetsWithSmallSumset
