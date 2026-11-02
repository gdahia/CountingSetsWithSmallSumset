/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independence of disjoint blocks of random variables

This file complements `Mathlib.Probability.Independence.InfinitePi` with a converse to
`iIndepFun_uncurry`: if the random variables `Xᵢⱼ` indexed by pairs `(i, j)` are independent, then
so are the families `(Xᵢⱼ)ⱼ`. As a consequence, independent random variables grouped along
pairwise disjoint sets of indices give independent random vectors.

## Main statements

* `ProbabilityTheory.iIndepFun.curry`: independent random variables indexed by pairs `(i, j)` give
  independent families `(Xᵢⱼ)ⱼ`.
* `ProbabilityTheory.iIndepFun.restrict_of_pairwiseDisjoint`: independent random variables,
  grouped along pairwise disjoint sets of indices, give independent random vectors.
-/

public section

open MeasureTheory Measure Function

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section curry

variable {κ : ι → Type*} {𝓧 : (i : ι) → κ i → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}

/-- If the random variables `Xᵢⱼ` indexed by pairs `(i, j)` are independent, then the families
`(Xᵢⱼ)ⱼ` are independent. This is a converse to `iIndepFun_uncurry`. -/
lemma iIndepFun.curry {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j} (mX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun (p : (i : ι) × κ i) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := h.isProbabilityMeasure
  have hcurry : P.map (fun ω i j ↦ X i j ω) =
      infinitePi fun i ↦ infinitePi fun j ↦ P.map (X i j) := by
    rw [← infinitePi_map_piCurry, ← (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h,
      map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), hcurry]
  congrm infinitePi fun i ↦ ?_
  change _ = P.map ((fun x ↦ x i) ∘ fun ω i j ↦ X i j ω)
  rw [← map_map (by fun_prop) (by fun_prop), hcurry, infinitePi_map_eval]

end curry

/-- Independent random variables, grouped along pairwise disjoint sets of indices, give
independent random vectors. -/
lemma iIndepFun.restrict_of_pairwiseDisjoint {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {X : (i : ι) → Ω → β i} (mX : ∀ i, Measurable (X i)) (h : iIndepFun X P) {κ : Type*}
    {t : κ → Set ι} (ht : Pairwise (Disjoint on t)) :
    iIndepFun (fun k ω (j : t k) ↦ X j ω) P := by
  refine iIndepFun.curry (X := fun k (j : t k) ↦ X j) (fun _ _ ↦ mX _) (h.precomp ?_)
  rintro ⟨k, j⟩ ⟨l, j'⟩ (hjj' : (j : ι) = j')
  obtain rfl : k = l := by
    by_contra hkl
    exact Set.disjoint_left.mp (ht hkl) j.2 (hjj' ▸ j'.2)
  obtain rfl := Subtype.ext hjj'
  rfl

end ProbabilityTheory
