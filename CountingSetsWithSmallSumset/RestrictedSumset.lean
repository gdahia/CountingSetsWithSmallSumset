/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# The restricted sumset

The restricted sumset `A ∔ A` of a finite set `A` is the set of the sums `a + b` with
`a, b ∈ A` and `a ≠ b`. It lies in `A + A`, and `A + A` has at most `|A|` elements more, namely
the doubles `a + a`. In a cancellative semigroup the translate `a + (A \ {a})` lies in `A ∔ A`, so
`|A ∔ A| ≥ |A| - 1`.

## Main definitions

* `restrictedSumset A`: the restricted sumset of `A`.

## Main statements

* `mem_restrictedSumset`: `x ∈ A ∔ A` if and only if `x = a + b` with distinct `a, b ∈ A`.
* `card_add_le_card_restrictedSumset_add_card`: `|A + A| ≤ |A ∔ A| + |A|`.
* `card_sub_one_le_card_restrictedSumset`: `|A| - 1 ≤ |A ∔ A|`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset
open scoped Pointwise

variable {G : Type*} [DecidableEq G]

/-- The restricted sumset, in which the two summands must be distinct. -/
def restrictedSumset [Add G] (A : Finset G) : Finset G :=
  ((A ×ˢ A).filter fun (a, b) ↦ a ≠ b).image fun (a, b) ↦ a + b

lemma restrictedSumset_eq_image_offDiag [Add G] (A : Finset G) :
    restrictedSumset A = A.offDiag.image fun (a, b) ↦ a + b := by
  ext x
  simp [restrictedSumset, and_assoc]

lemma mem_restrictedSumset [Add G] {A : Finset G} {x : G} :
    x ∈ restrictedSumset A ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b = x := by
  simp [restrictedSumset_eq_image_offDiag, and_assoc]

lemma restrictedSumset_mono [Add G] {B C : Finset G} (h : B ⊆ C) :
    restrictedSumset B ⊆ restrictedSumset C := by
  simp_rw [restrictedSumset_eq_image_offDiag]
  exact image_subset_image (offDiag_mono h)

lemma restrictedSumset_subset_add [Add G] (A : Finset G) : restrictedSumset A ⊆ A + A := by
  intro x hx
  obtain ⟨a, ha, b, hb, -, rfl⟩ := mem_restrictedSumset.1 hx
  exact add_mem_add ha hb

lemma card_restrictedSumset_le_card_add [Add G] (A : Finset G) :
    #(restrictedSumset A) ≤ #(A + A) :=
  card_le_card (restrictedSumset_subset_add A)

lemma add_subset_restrictedSumset_union_image [Add G] (A : Finset G) :
    A + A ⊆ restrictedSumset A ∪ A.image fun a ↦ a + a := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
  rw [mem_union, mem_restrictedSumset, mem_image]
  grind

lemma card_add_le_card_restrictedSumset_add_card [Add G] (A : Finset G) :
    #(A + A) ≤ #(restrictedSumset A) + #A :=
  (card_le_card (add_subset_restrictedSumset_union_image A)).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))

lemma card_sub_one_le_card_restrictedSumset [AddLeftCancelSemigroup G] {A : Finset G}
    (hA : A.Nonempty) : #A - 1 ≤ #(restrictedSumset A) := by
  obtain ⟨a, ha⟩ := hA
  rw [← card_erase_of_mem ha, ← card_image_of_injective (A.erase a) (add_right_injective a)]
  apply card_le_card
  intro x hx
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hx
  exact mem_restrictedSumset.2 ⟨a, ha, b, mem_of_mem_erase hb, (ne_of_mem_erase hb).symm, rfl⟩

end CountingSetsWithSmallSumset
