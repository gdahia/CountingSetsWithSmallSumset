/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import SumOfSetsInSeveralDimensions.FreimanDimension
public import Mathlib.Data.ZMod.Basic
import CountingSetsWithSmallSumset.FreimanLemma.RestrictedSumset
import Mathlib.Tactic.Linarith

/-!
# Unfolding a subset of `ℤ_N` into the integers

A set `A ⊆ ℤ_N` unfolds to the set `Ā = {a.val + 1 : a ∈ A}` of integers in `{1, …, N}`. The sum
of two elements of `Ā` is `(a + b).val + 2` or `(a + b).val + 2 + N`, so `|Ā ∔ Ā| ≤ 2 * |A ∔ A|`.
With Freiman's lemma this bounds the Freiman dimension of `Ā` by `4 * |A ∔ A| / |A|`, which is
Lemma 22 of Green, *Counting sets with small sumset, and the clique number of random Cayley
graphs*.

## Main definitions

* `zmodLift A`: the unfolding `{a.val + 1 : a ∈ A} ⊆ {1, …, N}` of `A ⊆ ℤ_N`.

## Main statements

* `card_restrictedSumset_zmodLift_le`: `|Ā ∔ Ā| ≤ 2 * |A ∔ A|`.
* `freimanDim_zmodLift_le`: Lemma 22 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions

variable {N : ℕ} [NeZero N]

/-- The unfolding of `A ⊆ ℤ_N`: its image under the injection `a ↦ a.val + 1` into
`{1, …, N}`. -/
def zmodLift (A : Finset (ZMod N)) : Finset ℕ :=
  A.image fun a ↦ a.val + 1

private lemma val_add_one_injective : Function.Injective fun a : ZMod N ↦ a.val + 1 :=
  (add_left_injective 1).comp (ZMod.val_injective N)

lemma zmodLift_injective : Function.Injective (zmodLift (N := N)) :=
  image_injective val_add_one_injective

@[simp]
lemma card_zmodLift (A : Finset (ZMod N)) : #(zmodLift A) = #A :=
  card_image_of_injective A val_add_one_injective

lemma zmodLift_subset_Icc (A : Finset (ZMod N)) : zmodLift A ⊆ Icc 1 N := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_image.1 hx
  grind [ZMod.val_lt a]

lemma restrictedSumset_zmodLift_subset (A : Finset (ZMod N)) :
    restrictedSumset (zmodLift A) ⊆ (restrictedSumset A).image (fun z ↦ z.val + 2) ∪
      (restrictedSumset A).image (fun z ↦ z.val + 2 + N) := by
  intro x hx
  obtain ⟨_, ha', _, hb', hne, rfl⟩ := mem_restrictedSumset.1 hx
  obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hb'
  have hab : a + b ∈ restrictedSumset A := mem_restrictedSumset.2 ⟨a, ha, b, hb, by grind, rfl⟩
  rw [mem_union, mem_image, mem_image]
  rcases lt_or_ge (a.val + b.val) N with h | h
  · exact Or.inl ⟨a + b, hab, by grind [ZMod.val_add_of_lt h]⟩
  · exact Or.inr ⟨a + b, hab, by grind [ZMod.val_add_val_of_le h]⟩

/-- The unfolding at most doubles the size of the restricted sumset. -/
lemma card_restrictedSumset_zmodLift_le (A : Finset (ZMod N)) :
    #(restrictedSumset (zmodLift A)) ≤ 2 * #(restrictedSumset A) :=
  (card_le_card (restrictedSumset_zmodLift_subset A)).trans ((card_union_le _ _).trans
    ((add_le_add card_image_le card_image_le).trans_eq (two_mul _).symm))

/-- **Lemma 22** of Green. If `A ⊆ ℤ_N` is nonempty, then its unfolding has Freiman dimension at
most `4 * |A ∔ A| / |A|`. -/
theorem freimanDim_zmodLift_le {A : Finset (ZMod N)} (hA : A.Nonempty) :
    (freimanDim (zmodLift A) : ℝ) ≤ 4 * #(restrictedSumset A) / #A := by
  have hr : (freimanDim (zmodLift A) : ℝ) + 1 ≤ #A := by
    exact_mod_cast card_zmodLift A ▸ freimanDim_add_one_le_card (S := zmodLift A) (hA.image _)
  have h21 := freimanDim_mul_le_card_restrictedSumset (zmodLift A)
  rw [card_zmodLift] at h21
  have h22 : (#(restrictedSumset (zmodLift A)) : ℝ) ≤ 2 * #(restrictedSumset A) :=
    mod_cast card_restrictedSumset_zmodLift_le A
  rw [le_div_iff₀ (mod_cast hA.card_pos)]
  linarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) (freimanDim (zmodLift A)))]

end CountingSetsWithSmallSumset
