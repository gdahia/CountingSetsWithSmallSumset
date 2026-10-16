/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Combinatorics.Additive.FreimanHom
import Mathlib.Algebra.Module.ZMod

/-!
# Sumsets and restricted sumsets in characteristic `2`

The image of a finite set `A` under a Freiman homomorphism of order `2` has a restricted sumset
no larger than that of `A`, because a sum `f a + f b` with `f a ≠ f b` depends only on `a + b`
and `a ≠ b`. In a vector space over `𝔽₂` every element is its own negative, so `a + a = 0` and the
sumset `A + A` is the restricted sumset of `A` together with `0`.

## Main statements

* `card_restrictedSumset_image_le`: the restricted sumset of the image of `A` under a Freiman
  homomorphism of order `2` has at most `|A ∔ A|` elements.
* `card_add_le_card_restrictedSumset_add_one`: over `𝔽₂`, `|A + A| ≤ |A ∔ A| + 1`.
-/

public section

namespace CountingSetsWithSmallSumset

open Finset
open scoped Pointwise

/-- The restricted sumset of the image of `A` under a Freiman homomorphism of order `2` has at
most as many elements as the restricted sumset of `A`. -/
lemma card_restrictedSumset_image_le {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    [DecidableEq G] [DecidableEq H] {A : Finset G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanHom 2 (A : Set G) B f) :
    #(restrictedSumset (A.image f)) ≤ #(restrictedSumset A) := by
  choose! a ha b hb _ hab using fun s (hs : s ∈ restrictedSumset A) ↦ mem_restrictedSumset.1 hs
  refine card_le_card_of_surjOn (fun s ↦ f (a s) + f (b s)) ?_
  intro y hy
  obtain ⟨_, hc', _, hd', hne, rfl⟩ := mem_restrictedSumset.1 hy
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hc'
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hd'
  have hcd : c + d ∈ restrictedSumset A :=
    mem_restrictedSumset.2 ⟨c, hc, d, hd, ne_of_apply_ne f hne, rfl⟩
  exact ⟨c + d, hcd, hf.add_eq_add (ha _ hcd) (hb _ hcd) hc hd (hab _ hcd)⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

/-- Over `𝔽₂`, the sumset `A + A` is contained in the restricted sumset together with `0`. -/
lemma add_subset_insert_zero_restrictedSumset (A : Finset V) :
    A + A ⊆ insert 0 (restrictedSumset A) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
  rcases eq_or_ne a b with rfl | hab
  · simp [ZModModule.add_self]
  · exact mem_insert_of_mem (mem_restrictedSumset.2 ⟨a, ha, b, hb, hab, rfl⟩)

/-- Over `𝔽₂`, `|A + A| ≤ |A ∔ A| + 1`. -/
lemma card_add_le_card_restrictedSumset_add_one (A : Finset V) :
    #(A + A) ≤ #(restrictedSumset A) + 1 :=
  (card_le_card (add_subset_insert_zero_restrictedSumset A)).trans (card_insert_le _ _)

end CountingSetsWithSmallSumset
