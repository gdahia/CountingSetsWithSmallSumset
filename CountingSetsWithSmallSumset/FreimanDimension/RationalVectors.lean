/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.FreimanDimension
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Rational vectors as real vectors

The coordinatewise inclusion `rationalVectorToReal : ℚ^d → ℝ^d` is an injective `ℚ`-linear map.
Rational vectors that are linearly independent over `ℚ` stay linearly independent over `ℝ`, so
the real span of a set of rational vectors has the dimension of its rational span, and the real
affine dimension of a finite set of rational vectors is its rational affine dimension.

## Main definitions

* `rationalVectorToRealLinearMap d`: the inclusion `ℚ^d → ℝ^d` as a `ℚ`-linear map.

## Main statements

* `rationalVectorToReal_injective`: the inclusion is injective.
* `finrank_span_image_rationalVectorToReal`: the real span of a set of rational vectors has the
  dimension of its rational span.
* `finsetAffineDim_image_rationalVectorToReal`: the real affine dimension of a finite set of
  rational vectors is its rational affine dimension.
-/

public section

namespace CountingSetsWithSmallSumset

open Module SumOfSetsInSeveralDimensions

variable {d : ℕ}

/-- The coordinatewise inclusion `ℚ^d → ℝ^d` as a `ℚ`-linear map. -/
noncomputable def rationalVectorToRealLinearMap (d : ℕ) : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℝ) :=
  LinearMap.compLeft (Algebra.linearMap ℚ ℝ) (Fin d)

@[simp]
lemma coe_rationalVectorToRealLinearMap :
    ⇑(rationalVectorToRealLinearMap d) = rationalVectorToReal := by
  ext
  simp [rationalVectorToRealLinearMap, rationalVectorToReal]

@[simp]
lemma rationalVectorToReal_add (u v : Fin d → ℚ) :
    rationalVectorToReal (u + v) = rationalVectorToReal u + rationalVectorToReal v := by
  simp [← coe_rationalVectorToRealLinearMap]

@[simp]
lemma rationalVectorToReal_sub (u v : Fin d → ℚ) :
    rationalVectorToReal (u - v) = rationalVectorToReal u - rationalVectorToReal v := by
  simp [← coe_rationalVectorToRealLinearMap]

lemma rationalVectorToReal_injective : Function.Injective (rationalVectorToReal (d := d)) := by
  intro u v h
  ext i
  simpa [rationalVectorToReal] using congrFun h i

/-- The real span of a set of rational vectors has the dimension of its rational span. -/
lemma finrank_span_image_rationalVectorToReal (T : Set (Fin d → ℚ)) :
    finrank ℝ (Submodule.span ℝ (rationalVectorToReal '' T)) =
      finrank ℚ (Submodule.span ℚ T) := by
  obtain ⟨b, -, hspan, hli⟩ := exists_linearIndependent ℚ T
  have : Fintype b := have := hli.finite; Fintype.ofFinite b
  have hreal : LinearIndependent ℝ (rationalVectorToReal ∘ ((↑) : b → Fin d → ℚ)) := by
    convert (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 hli using 1
    ext
    simp [rationalVectorToReal]
  have hspanR : Submodule.span ℝ (rationalVectorToReal '' T) =
      Submodule.span ℝ (Set.range (rationalVectorToReal ∘ ((↑) : b → Fin d → ℚ))) := by
    rw [Set.range_comp, Subtype.range_coe, ← Submodule.span_span_of_tower ℚ ℝ,
      ← Submodule.span_span_of_tower ℚ ℝ (rationalVectorToReal '' b),
      ← coe_rationalVectorToRealLinearMap, Submodule.span_image, Submodule.span_image, hspan]
  rw [hspanR, finrank_span_eq_card hreal, ← hspan, finrank_span_set_eq_card hli,
    Set.toFinset_card]

/-- The real affine dimension of a finite set of rational vectors is its rational affine
dimension. -/
lemma finsetAffineDim_image_rationalVectorToReal (S : Finset (Fin d → ℚ)) :
    finsetAffineDim (S.image rationalVectorToReal) =
      finrank ℚ (vectorSpan ℚ (S : Set (Fin d → ℚ))) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [Finset.image_empty, finsetAffineDim_empty, Finset.coe_empty, vectorSpan_empty, finrank_bot]
  have hset : (fun x ↦ x -ᵥ rationalVectorToReal p) '' (rationalVectorToReal '' S) =
      rationalVectorToReal '' ((fun x ↦ x -ᵥ p) '' S) := by
    simp [Set.image_image, vsub_eq_sub]
  rw [finsetAffineDim_eq_finrank_vectorSpan, Finset.coe_image,
    vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_image_of_mem _ (Finset.mem_coe.2 hp)),
    vectorSpan_eq_span_vsub_set_right ℚ (Finset.mem_coe.2 hp), hset,
    finrank_span_image_rationalVectorToReal]

end CountingSetsWithSmallSumset
