/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanDimension.HomSpace
public import SumOfSetsInSeveralDimensions.FreimanDimension
import CountingSetsWithSmallSumset.FreimanDimension.AffineModel
import CountingSetsWithSmallSumset.FreimanDimension.RationalVectors
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Covers

/-!
# Green's Freiman dimension of a set of integers

Freiman's dimension `freimanDim X` of a finite set `X` is the largest `d ≤ |X|` such that `X` is
Freiman isomorphic to a subset of `ℚ^d` whose image in `ℝ^d` has affine dimension `d`. The real
affine dimension of a set of rational vectors is its rational affine dimension. So, by Corollary 14
of Green, *Counting sets with small sumset, and the clique number of random Cayley graphs*,
Green's dimension `r_ℚ(X)` is Freiman's dimension of `X` whenever `X` is Freiman isomorphic to a
subset of a `ℚ`-vector space. This holds for sets of integers and of natural numbers.

## Main statements

* `freimanModelDim_iff`: Freiman models in terms of the rational affine dimension.
* `freimanDimOver_rat_eq_freimanDim_of_isAddFreimanIso`: `r_ℚ(X) = freimanDim X` when `X` is
  Freiman isomorphic to a subset of a `ℚ`-vector space.
* `freimanDimOver_rat_eq_freimanDim_int`, `freimanDimOver_rat_eq_freimanDim_nat`:
  `r_ℚ(X) = freimanDim X` for sets of integers and of natural numbers.
-/

public section

namespace CountingSetsWithSmallSumset

open Module SumOfSetsInSeveralDimensions

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- `X` has a Freiman model of dimension `d` if and only if it is Freiman isomorphic to a subset of
`ℚ^d` of rational affine dimension `d`. -/
lemma freimanModelDim_iff {X : Finset G} {d : ℕ} :
    freimanModelDim X d ↔ ∃ f : G → (Fin d → ℚ), IsAddFreimanIso 2 (X : Set G) (f '' X) f ∧
      finrank ℚ (vectorSpan ℚ (f '' X)) = d := by
  refine exists_congr ?_
  intro f
  rw [affineDim_image_rationalVectorToReal, Finset.coe_image]

/-- **Corollary 14** of Green, last part. If `X` is Freiman isomorphic to a subset of a
`ℚ`-vector space, then `r_ℚ(X)` is Freiman's dimension of `X`. -/
lemma freimanDimOver_rat_eq_freimanDim_of_isAddFreimanIso {V : Type*} [AddCommGroup V]
    [Module ℚ V] {X : Finset G} {g : G → V} (hg : IsAddFreimanIso 2 (X : Set G) (g '' X) g) :
    freimanDimOver ℚ X = freimanDim X := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp [freimanDim, Nat.le_zero.1 (freimanDimOver_le_card_sub_one ℚ (∅ : Finset G))]
  obtain ⟨hmem, hmax⟩ := isGreatest_freimanDimOver_of_isAddFreimanIso ℚ hX hg
  unfold freimanDim
  rw [eq_comm, Nat.findGreatest_eq_iff]
  refine ⟨(freimanDimOver_le_card_sub_one ℚ X).trans (Nat.sub_le _ _),
    fun _ ↦ freimanModelDim_iff.2 hmem, ?_⟩
  intro n hn _ hP
  grind [hmax (freimanModelDim_iff.1 hP)]

/-- **Corollary 14** of Green, last part. For a finite set `X` of integers, `r_ℚ(X)` is Freiman's
dimension of `X`. -/
lemma freimanDimOver_rat_eq_freimanDim_int (X : Finset ℤ) :
    freimanDimOver ℚ X = freimanDim X := by
  apply freimanDimOver_rat_eq_freimanDim_of_isAddFreimanIso (g := ((↑) : ℤ → ℚ))
  simpa using isAddFreimanIso_image_of_injective 2 (φ := Int.castAddHom ℚ) Int.cast_injective X

/-- **Corollary 14** of Green, last part. For a finite set `X` of natural numbers, `r_ℚ(X)` is
Freiman's dimension of `X`. -/
lemma freimanDimOver_rat_eq_freimanDim_nat (X : Finset ℕ) :
    freimanDimOver ℚ X = freimanDim X := by
  apply freimanDimOver_rat_eq_freimanDim_of_isAddFreimanIso (g := ((↑) : ℕ → ℚ))
  simpa using
    isAddFreimanIso_image_of_injective 2 (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective X

end CountingSetsWithSmallSumset
