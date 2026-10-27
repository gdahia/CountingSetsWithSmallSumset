/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Relations
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Relation spaces and the number of Freiman isomorphism classes

This file follows Section 3 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*. Let `W` be a vector space over a field `F` and let `a : Fin t → W`. A
relation `p` of order `s` has the coefficient vector `e_{i₁} + ⋯ + e_{iₛ} - e_{j₁} - ⋯ - e_{jₛ}` in
`F^t`, and `a` satisfies `p` exactly when this vector lies in the kernel of the linear map
`λ ↦ ∑ λᵢ aᵢ`. Hence `a` satisfies a relation exactly when its vector lies in the span of the
vectors of the relations that `a` satisfies, which is equation (273) of the paper. This span has
dimension at most `t`, so it is spanned by the vectors of `t` relations. By Lemma 10, a set of `k`
elements of `W` therefore lies in one of at most `k ^ (2 * s * k)` Freiman isomorphism classes of
order `s`, which is Lemma 11.

## Main definitions

* `freimanRelationVector F p`: the coefficient vector of the relation `p` in `Fin t →₀ F`.
* `freimanRelationSpace F s a`: the span of the vectors of the relations of order `s` that `a`
  satisfies.

## Main statements

* `freimanRelationHolds_iff_mem_freimanRelationSpace`: equation (273) of Green.
* `exists_isAddFreimanIso_range_of_freimanRelationSpace_eq`: Lemma 10 of Green.
* `exists_span_freimanRelationVector_eq_freimanRelationSpace`: the span is spanned by the vectors
  of `t` relations.
* `exists_representsFreimanIsoClasses_card_le_pow`: Lemma 11 of Green, at most `k ^ (2 * s * k)`
  classes of order `s` of sets of `k` elements of `W`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

noncomputable section

/-- There are `t ^ (2 * s * t)` tuples of `t` relations of order `s`. In Lemma 11 of Green, the
class of a set is encoded by such a tuple whose relations span its relation space. -/
lemma card_freimanRelationTuples (s t : ℕ) :
    Fintype.card (Fin t → FreimanRelationIndex s t) = t ^ (2 * s * t) := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  ring

variable (F : Type*) {W W' : Type*} [Field F] [AddCommGroup W] [AddCommGroup W']

/-- The coefficient vector `e_{i₁} + ⋯ + e_{iₛ} - e_{j₁} - ⋯ - e_{jₛ}` of the relation
`(i, j)`. -/
def freimanRelationVector {s t : ℕ} : FreimanRelationIndex s t → Fin t →₀ F :=
  fun (i, j) ↦ ∑ k, Finsupp.single (i k) 1 - ∑ k, Finsupp.single (j k) 1

/-- The span of the vectors of the relations of order `s` that `a` satisfies. -/
def freimanRelationSpace (s : ℕ) {t : ℕ} (a : Fin t → W) : Submodule F (Fin t →₀ F) :=
  Submodule.span F
    (freimanRelationVector F '' {p : FreimanRelationIndex s t | freimanRelationHolds a p})

private lemma finrank_freimanRelationSpace_le (s : ℕ) {t : ℕ} (a : Fin t → W) :
    Module.finrank F (freimanRelationSpace F s a) ≤ t := by
  simpa using (freimanRelationSpace F s a).finrank_le

/-- The span of the vectors of the relations of order `s` of a tuple of length `t` is spanned by
the vectors of `t` of these relations. The family is padded with trivial relations so that it has
exactly `t` entries. -/
lemma exists_span_freimanRelationVector_eq_freimanRelationSpace (s : ℕ) {t : ℕ}
    (a : Fin t → W) :
    ∃ rels : Fin t → FreimanRelationIndex s t,
      Submodule.span F (freimanRelationVector F '' Set.range rels) =
        freimanRelationSpace F s a := by
  obtain ⟨basis, hmem, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq F
    (freimanRelationVector F '' {p : FreimanRelationIndex s t | freimanRelationHolds a p})
  choose index _ hindex using hmem
  refine ⟨fun i ↦ if hi : i.val < _ then index ⟨i, hi⟩ else (fun _ ↦ i, fun _ ↦ i),
    Eq.trans (le_antisymm ?_ ?_) hspan⟩ <;> rw [Submodule.span_le]
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    dsimp only
    split
    · exact Submodule.subset_span ⟨_, (hindex _).symm⟩
    · simp [freimanRelationVector]
  · rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨index i,
      ⟨⟨i, i.isLt.trans_le (finrank_freimanRelationSpace_le F s a)⟩, ?_⟩, hindex i⟩
    simp

variable [Module F W] [Module F W']

/-- The tuple `a` satisfies `p` exactly when the vector of `p` lies in the kernel of the linear map
`λ ↦ ∑ λᵢ aᵢ`. -/
lemma freimanRelationVector_mem_ker_iff {s t : ℕ} (a : Fin t → W)
    (p : FreimanRelationIndex s t) :
    freimanRelationVector F p ∈ LinearMap.ker (Finsupp.linearCombination F a) ↔
      freimanRelationHolds a p := by
  obtain ⟨i, j⟩ := p
  simp [freimanRelationVector, freimanRelationHolds, sub_eq_zero]

/-- Equation (273) of Green. The tuple `a` satisfies a relation of order `s` exactly when its
vector lies in the span of the vectors of the relations of order `s` that `a` satisfies. -/
lemma freimanRelationHolds_iff_mem_freimanRelationSpace {s t : ℕ} (a : Fin t → W)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds a p ↔ freimanRelationVector F p ∈ freimanRelationSpace F s a := by
  refine ⟨fun hp ↦ Submodule.subset_span ⟨p, hp, rfl⟩, ?_⟩
  intro hp
  rw [← freimanRelationVector_mem_ker_iff F]
  refine Submodule.span_le.mpr ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact (freimanRelationVector_mem_ker_iff F a q).mpr hq

variable {F} in
/-- Two tuples whose relations of order `s` span the same space satisfy the same relations of
order `s`. -/
lemma freimanRelationHolds_iff_of_freimanRelationSpace_eq {s t : ℕ} {a : Fin t → W}
    {b : Fin t → W'} (h : freimanRelationSpace F s a = freimanRelationSpace F s b)
    (p : FreimanRelationIndex s t) : freimanRelationHolds a p ↔ freimanRelationHolds b p := by
  rw [freimanRelationHolds_iff_mem_freimanRelationSpace F, h,
    ← freimanRelationHolds_iff_mem_freimanRelationSpace]

variable {F} in
/-- **Lemma 10** of Green. If the relations of order `s` of two injective tuples span the same
space, then their ranges are Freiman isomorphic of order `s`. -/
lemma exists_isAddFreimanIso_range_of_freimanRelationSpace_eq {s t : ℕ} {a : Fin t → W}
    {b : Fin t → W'} (ha : Function.Injective a) (hb : Function.Injective b)
    (h : freimanRelationSpace F s a = freimanRelationSpace F s b) :
    ∃ f : W → W', IsAddFreimanIso s (Set.range a) (Set.range b) f :=
  exists_isAddFreimanIso_range ha hb (freimanRelationHolds_iff_of_freimanRelationSpace_eq h)

include F in
/-- A family of sets of `k` elements of a vector space over `F` is represented by at
most `k ^ (2 * s * k)` of its members up to Freiman isomorphism of order `s`. -/
lemma exists_subset_representsFreimanIsoClasses_card_le_pow (s : ℕ) {k : ℕ}
    {family : Set (Finset W)} (hfamily : ∀ A ∈ family, #A = k) :
    ∃ representatives : Finset (Finset W), ↑representatives ⊆ family ∧
      RepresentsFreimanIsoClasses s family representatives ∧
        #representatives ≤ k ^ (2 * s * k) := by
  rw [← card_freimanRelationTuples]
  refine exists_subset_representsFreimanIsoClasses_card_le_of_pattern
    (fun A pattern ↦ ∃ a : Fin k → W, Function.Injective a ∧ Set.range a = A ∧
      Submodule.span F (freimanRelationVector F '' Set.range pattern) = freimanRelationSpace F s a)
    ?_ ?_
  · intro A hA
    obtain ⟨a, ha, hrange⟩ := exists_injective_range_eq (hfamily A hA)
    obtain ⟨pattern, hpattern⟩ := exists_span_freimanRelationVector_eq_freimanRelationSpace F s a
    exact ⟨pattern, a, ha, hrange, hpattern⟩
  · rintro A - B - pattern ⟨a, ha, hA, hapattern⟩ ⟨b, hb, hB, hbpattern⟩
    exact freimanIsomorphic_of_freimanRelationHolds_iff ha hA hb hB
      (freimanRelationHolds_iff_of_freimanRelationSpace_eq (hapattern.symm.trans hbpattern))

variable (W)

include F in
/-- **Lemma 11** of Green. Let `W` be a vector space over a field `F`. There is a family of at most
`k ^ (2 * s * k)` sets of `k` elements of `W` such that every set of `k` elements of `W` is Freiman
isomorphic of order `s` to a member of the family. -/
lemma exists_representsFreimanIsoClasses_card_le_pow (s k : ℕ) :
    ∃ representatives : Finset (Finset W),
      RepresentsFreimanIsoClasses s {A : Finset W | #A = k} representatives ∧
        #representatives ≤ k ^ (2 * s * k) := by
  obtain ⟨representatives, -, hrep, hcard⟩ :=
    exists_subset_representsFreimanIsoClasses_card_le_pow F s fun (_ : Finset W) hA ↦ hA
  exact ⟨representatives, hrep, hcard⟩

end

end CountingSetsWithSmallSumset
