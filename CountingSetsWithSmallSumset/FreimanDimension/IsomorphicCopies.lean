/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanDimension.HomSpace
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Covers
public import SumOfSetsInSeveralDimensions.FreimanDimension
import CountingSetsWithSmallSumset.FreimanDimension.Basis
import CountingSetsWithSmallSumset.FreimanDimension.Integers

/-!
# Freiman isomorphic copies of a set

A set `B` that is Freiman isomorphic to a finite nonempty set `X` is the image of a Freiman
homomorphism from `X`. By Lemma 13 (i) of Green, *Counting sets with small sumset, and the clique
number of random Cayley graphs*, such a homomorphism is determined by its values at `r_F(X) + 1`
points. So at most `|F^n| ^ (r_F(X) + 1)` subsets of `F^n` are Freiman isomorphic to `X` when `F`
is a finite field. For a set `X` of natural numbers, the homomorphisms into `ℚ` give the same
bound with `F^n` replaced by any finite set `S` of natural numbers and `r_F(X)` by
`freimanDim X`.

## Main statements

* `ncard_isAddFreimanIso_le`: at most `(|F| ^ n) ^ (r_F(X) + 1)` subsets of `F^n` are Freiman
  isomorphic of order `2` to `X`.
* `ncard_freimanIsomorphic_subset_le`: at most `|S| ^ (freimanDim X + 1)` subsets of a finite set
  `S` of natural numbers are Freiman isomorphic of order `2` to a set `X` of natural numbers.
-/

public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions

variable {G : Type*} [AddCommMonoid G]

/-- At most `(|F| ^ n) ^ (r_F(X) + 1)` subsets of `F^n` are Freiman isomorphic of order `2` to a
nonempty set `X`. -/
lemma ncard_isAddFreimanIso_le (F : Type*) [Field F] [Finite F] (n : ℕ) {X : Finset G}
    (hX : X.Nonempty) :
    {B : Finset (Fin n → F) | ∃ f : G → (Fin n → F),
      IsAddFreimanIso 2 (X : Set G) (B : Set (Fin n → F)) f}.ncard ≤
      (Nat.card F ^ n) ^ (freimanDimOver F X + 1) := by
  classical
  let g : freimanHomSpace F (Fin n → F) X → Finset (Fin n → F) :=
    fun φ ↦ univ.image (φ : X → Fin n → F)
  have hsub : {B : Finset (Fin n → F) | ∃ f : G → (Fin n → F),
      IsAddFreimanIso 2 (X : Set G) (B : Set (Fin n → F)) f} ⊆ Set.range g := by
    rintro B ⟨f, hf⟩
    refine ⟨⟨fun x ↦ f x, mem_freimanHomSpace_of_isAddFreimanHom F hf.isAddFreimanHom⟩, ?_⟩
    ext y
    simp [g, ← mem_coe (s := B), ← hf.bijOn.image_eq]
  refine (Set.ncard_le_ncard hsub (Set.finite_range g)).trans ?_
  rw [← Set.image_univ]
  refine (Set.ncard_image_le Set.finite_univ).trans ?_
  rw [Set.ncard_univ, card_freimanHomSpace F _ hX, Nat.card_fun]
  simp

/-- A Freiman isomorphism of order `2` from a set of natural numbers, followed by the inclusion
`ℕ → ℚ`, is a Freiman homomorphism into `ℚ`. -/
private lemma natCast_comp_mem_freimanHomSpace {X Y : Finset ℕ} {f : ℕ → ℕ}
    (hf : IsAddFreimanIso 2 (X : Set ℕ) (Y : Set ℕ) f) :
    (fun x : X ↦ (f x : ℚ)) ∈ freimanHomSpace ℚ ℚ X := by
  intro a b c d h
  dsimp only
  exact_mod_cast hf.isAddFreimanHom.add_eq_add a.prop b.prop c.prop d.prop h

/-- At most `|S| ^ (freimanDim X + 1)` subsets of a finite set `S` of natural numbers are Freiman
isomorphic of order `2` to a nonempty set `X` of natural numbers. -/
lemma ncard_freimanIsomorphic_subset_le {X : Finset ℕ} (hX : X.Nonempty) (S : Finset ℕ) :
    {Y : Finset ℕ | Y ⊆ S ∧ FreimanIsomorphic 2 X Y}.ncard ≤ #S ^ (freimanDim X + 1) := by
  classical
  obtain ⟨a, ha⟩ := exists_isFreimanBasis ℚ hX
  have hiso : ∀ Y ∈ {Y : Finset ℕ | Y ⊆ S ∧ FreimanIsomorphic 2 X Y}, FreimanIsomorphic 2 X Y :=
    fun _ ⟨_, h⟩ ↦ h
  choose! f hf using hiso
  rw [← freimanDimOver_rat_eq_freimanDim_nat, ← Fintype.card_piFinset_const, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun Y i ↦ f Y (a i)) ?_ ?_
  · rintro Y ⟨hYS, hXY⟩
    rw [mem_coe, Fintype.mem_piFinset]
    intro i
    exact hYS ((hf Y ⟨hYS, hXY⟩).bijOn.mapsTo (a i).prop)
  · intro Y hY Z hZ hYZ
    have h := ha.injective ℚ (a₁ := ⟨_, natCast_comp_mem_freimanHomSpace (hf Y hY)⟩)
      (a₂ := ⟨_, natCast_comp_mem_freimanHomSpace (hf Z hZ)⟩)
      (by ext i; simpa using congrArg ((↑) : ℕ → ℚ) (congrFun hYZ i))
    have hfg : Set.EqOn (f Y) (f Z) X := by
      intro x hx
      exact Nat.cast_injective (R := ℚ) (by simpa using congrFun (congrArg Subtype.val h) ⟨x, hx⟩)
    rw [← coe_inj, ← (hf Y hY).bijOn.image_eq, ← (hf Z hZ).bijOn.image_eq, hfg.image_eq]

end CountingSetsWithSmallSumset
