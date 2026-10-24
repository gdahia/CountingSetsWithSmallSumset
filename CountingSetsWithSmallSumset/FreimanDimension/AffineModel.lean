/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanDimension.HomSpace
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import CountingSetsWithSmallSumset.FreimanDimension.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine models of a set and the Freiman dimension

By Lemma 13 (ii) of Green, the image of a finite set `A` under a Freiman homomorphism into an
`F`-vector space lies in the affine span of the images of `r_F(A) + 1` points, so its affine
dimension is at most `r_F(A)`. Conversely, if the additive relations of `A` are those of a subset
of an `F`-vector space, then by Lemma 13 (i) a homomorphism sending a Freiman basis to the
vertices `0, e₁, …, e_r` of the standard simplex of `F^r` is a Freiman isomorphism from `A` onto a
subset of `F^r` of affine dimension `r = r_F(A)`. Hence `r_F(A)` is the largest `d` such that `A`
is Freiman isomorphic to a subset of `F^d` that is not contained in a proper affine subspace. This
is Corollary 14 of Green, *Counting sets with small sumset, and the clique number of random Cayley
graphs*.

## Main statements

* `finrank_vectorSpan_image_le_freimanDimOver`: the image of `A` under a Freiman homomorphism has
  affine dimension at most `r_F(A)`.
* `finrank_vectorSpan_le_freimanDimOver`: a set in an `F`-vector space has affine dimension at
  most `r_F(A)`.
* `exists_isAddFreimanIso_finrank_vectorSpan_eq`: `A` is Freiman isomorphic to a subset of `F^r`
  of affine dimension `r = r_F(A)`.
* `isGreatest_freimanDimOver_of_isAddFreimanIso`, `isGreatest_freimanDimOver`: Corollary 14 of
  Green.
-/

public section

namespace CountingSetsWithSmallSumset

open Module

variable (F : Type*) [Field F] {G : Type*} [AddCommMonoid G] {V : Type*} [AddCommGroup V]
  [Module F V] {W : Type*} [AddCommGroup W] [Module F W]

/-- The image of `A` under a Freiman homomorphism into an `F`-vector space has affine dimension at
most `r_F(A)`. -/
lemma finrank_vectorSpan_image_le_freimanDimOver {A : Finset G} {f : G → V}
    (hf : IsAddFreimanHom 2 (A : Set G) Set.univ f) :
    finrank F (vectorSpan F (f '' A)) ≤ freimanDimOver F A := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.coe_empty, Set.image_empty, vectorSpan_empty, finrank_bot]
    exact Nat.zero_le _
  obtain ⟨a, ha⟩ := exists_isFreimanBasis F hA
  have hsub : f '' A ⊆ affineSpan F (Set.range fun i ↦ f (a i)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hφ⟩ := ha.exists_sum_eq_one_and_eq_sum_smul ⟨x, hx⟩
    rw [(hφ V _ (mem_freimanHomSpace_of_isAddFreimanHom F hf) : f x = ∑ i, c i • f (a i)),
      ← Finset.affineCombination_eq_linear_combination _ _ _ hc]
    exact affineCombination_mem_affineSpan hc _
  refine (Submodule.finrank_mono ?_).trans
    (finrank_vectorSpan_range_le F (fun i ↦ f (a i)) (Fintype.card_fin _))
  simpa [direction_affineSpan] using AffineSubspace.direction_le (affineSpan_le.2 hsub)

/-- A finite set `A` in an `F`-vector space has affine dimension at most `r_F(A)`. -/
lemma finrank_vectorSpan_le_freimanDimOver (A : Finset W) :
    finrank F (vectorSpan F (A : Set W)) ≤ freimanDimOver F A := by
  rw [← Set.image_id (A : Set W)]
  exact finrank_vectorSpan_image_le_freimanDimOver F
    (isAddFreimanHom_id (Set.subset_univ (A : Set W)))

/-- The vertices `0, e₁, …, e_r` of the standard simplex of `F^r` are affinely independent. -/
private lemma affineIndependent_cons_zero_single (r : ℕ) :
    AffineIndependent F (Fin.cons 0 fun j ↦ Pi.single j 1 : Fin (r + 1) → Fin r → F) := by
  rw [affineIndependent_iff_of_fintype]
  intro u hu hw
  rw [Finset.weightedVSub_eq_linear_combination _ hu, Fin.sum_univ_succ] at hw
  have hs (j : Fin r) : u j.succ = 0 := by
    simpa [Finset.sum_apply, Pi.single_apply] using congrFun hw j
  intro i
  cases i using Fin.cases with
  | zero => simpa [Fin.sum_univ_succ, hs] using hu
  | succ j => exact hs j

/-- If the additive relations of `A` are those of a subset of an `F`-vector space, then `A` is
Freiman isomorphic to a subset of `F^r` of affine dimension `r = r_F(A)`. -/
lemma exists_isAddFreimanIso_finrank_vectorSpan_eq {A : Finset G} (hA : A.Nonempty) {g : G → V}
    (hg : IsAddFreimanIso 2 (A : Set G) (g '' A) g) :
    ∃ f : G → (Fin (freimanDimOver F A) → F), IsAddFreimanIso 2 (A : Set G) (f '' A) f ∧
      finrank F (vectorSpan F (f '' A)) = freimanDimOver F A := by
  classical
  obtain ⟨a, ha⟩ := exists_isFreimanBasis F hA
  let w : Fin (freimanDimOver F A + 1) → Fin (freimanDimOver F A) → F :=
    Fin.cons 0 fun j ↦ Pi.single j 1
  obtain ⟨φ, hφ⟩ := (ha.bijective (Fin (freimanDimOver F A) → F)).surjective w
  let f : G → Fin (freimanDimOver F A) → F := fun x ↦
    if h : x ∈ A then (φ : A → Fin (freimanDimOver F A) → F) ⟨x, h⟩ else 0
  have hfφ : (fun x : A ↦ f x) = φ := funext fun x ↦ dite_eq_left x.prop
  have hfa (i) : f (a i) = w i := (dite_eq_left (a i).prop).trans (congrFun hφ i)
  have hind : AffineIndependent F fun i ↦ f (a i) := by
    simpa [hfa] using affineIndependent_cons_zero_single F (freimanDimOver F A)
  refine ⟨f, ha.isAddFreimanIso_of_affineIndependent hg
    (mem_freimanHomSpace_iff_isAddFreimanHom.1 (hfφ ▸ φ.prop)) hind, le_antisymm ?_ ?_⟩
  · simpa using (vectorSpan F (f '' A)).finrank_le
  · refine (hind.finrank_vectorSpan (Fintype.card_fin _)).symm.trans_le
      (Submodule.finrank_mono (vectorSpan_mono F ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, (a i).prop, rfl⟩

/-- **Corollary 14** of Green, for a set whose additive relations are those of a subset of an
`F`-vector space: `r_F(A)` is the largest `d` such that `A` is Freiman isomorphic to a subset of
`F^d` of affine dimension `d`. -/
lemma isGreatest_freimanDimOver_of_isAddFreimanIso {A : Finset G} (hA : A.Nonempty)
    {g : G → V} (hg : IsAddFreimanIso 2 (A : Set G) (g '' A) g) :
    IsGreatest {d | ∃ f : G → (Fin d → F), IsAddFreimanIso 2 (A : Set G) (f '' A) f ∧
      finrank F (vectorSpan F (f '' A)) = d} (freimanDimOver F A) := by
  refine ⟨exists_isAddFreimanIso_finrank_vectorSpan_eq F hA hg, ?_⟩
  rintro d ⟨f, hf, hd⟩
  rw [← hd]
  exact finrank_vectorSpan_image_le_freimanDimOver F
    (hf.isAddFreimanHom.superset (Set.subset_univ _))

/-- **Corollary 14** of Green. For a finite nonempty subset `A` of an `F`-vector space, `r_F(A)`
is the largest `d` such that `A` is Freiman isomorphic to a subset of `F^d` that is not contained
in a proper affine subspace. -/
lemma isGreatest_freimanDimOver {A : Finset W} (hA : A.Nonempty) :
    IsGreatest {d | ∃ f : W → (Fin d → F), IsAddFreimanIso 2 A (f '' A) f ∧
      finrank F (vectorSpan F (f '' A)) = d} (freimanDimOver F A) :=
  isGreatest_freimanDimOver_of_isAddFreimanIso F hA (g := id) (by simpa using isAddFreimanIso_id)

end CountingSetsWithSmallSumset
