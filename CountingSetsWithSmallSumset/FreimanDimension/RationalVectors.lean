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

* `finrank_span_image_rationalVectorToReal`: the real span of a set of rational vectors has the
  dimension of its rational span.
* `affineDim_image_rationalVectorToReal`: the real affine dimension of a finite set of
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
lemma rationalVectorToReal_sub (u v : Fin d → ℚ) :
    rationalVectorToReal (u - v) = rationalVectorToReal u - rationalVectorToReal v := by
  simp [← coe_rationalVectorToRealLinearMap]

/-- The real span of a set of rational vectors has the dimension of its rational span. -/
lemma finrank_span_image_rationalVectorToReal (T : Set (Fin d → ℚ)) :
    finrank ℝ (Submodule.span ℝ (rationalVectorToReal '' T)) =
      finrank ℚ (Submodule.span ℚ T) := by
  obtain ⟨b, -, hspan, hli⟩ := exists_linearIndependent ℚ T
  have := hli.setFinite.fintype
  have hreal : LinearIndependent ℝ (rationalVectorToReal ∘ ((↑) : b → Fin d → ℚ)) := by
    convert (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 hli using 1
    ext
    simp [rationalVectorToReal]
  rw [← Submodule.span_span_of_tower ℚ ℝ, ← coe_rationalVectorToRealLinearMap,
    Submodule.span_image, ← hspan, ← Submodule.span_image, Submodule.span_span_of_tower,
    coe_rationalVectorToRealLinearMap, ← Subtype.range_coe (s := b), ← Set.range_comp,
    finrank_span_eq_card hreal, finrank_span_eq_card hli]

/-- The real affine dimension of a finite set of rational vectors is its rational affine
dimension. -/
lemma affineDim_image_rationalVectorToReal (S : Finset (Fin d → ℚ)) :
    (S.image rationalVectorToReal).affineDim =
      finrank ℚ (vectorSpan ℚ (S : Set (Fin d → ℚ))) := by
  rw [Finset.affineDim_eq_finrank_vectorSpan, Finset.coe_image, vectorSpan_def, vectorSpan_def,
    ← coe_rationalVectorToRealLinearMap, ← LinearMap.coe_toAffineMap,
    AffineMap.image_vsub_image, LinearMap.toAffineMap_linear, coe_rationalVectorToRealLinearMap,
    finrank_span_image_rationalVectorToReal]

end CountingSetsWithSmallSumset
