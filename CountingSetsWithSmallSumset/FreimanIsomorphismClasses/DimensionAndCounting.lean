/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationAndExtensionCodes
public import SumOfSetsInSeveralDimensions.FreimanDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Freiman dimension of an isomorphism class and the number of classes

This file follows Section 3 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*.

Let `a : Fin t → ℕ` be an injective tuple. The relations `aᵢ + aⱼ = aₖ + aₗ` that `a` satisfies
span a subspace of the space of the vectors of `ℚ^t` with zero coefficient sum. The quotient by
this subspace contains a Freiman isomorphic copy of the range of `a` that spans it, so its
dimension `relationModelDim a` is at most the Freiman dimension of the range of `a`. A tuple
with the same relations as `a` is determined by its values at `relationModelDim a + 1` suitable
coordinates. The relations of a `t`-tuple are spanned by `t` of them, so there are at most
`n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with `t` elements and Freiman dimension at most `r`.

The file also attaches to a set of `t` natural numbers a canonical code of its relations with
`s` terms on each side, which does not depend on an enumeration of the set, and bounds the number
of canonical codes in two families of sets.

## Main definitions

* `relationSpace a`: the span of the relations that the tuple `a` satisfies.
* `relationModelDim a`: the dimension of the zero-sum space modulo the relations of `a`.
* `FreimanRelationEquivalent X Y`: the sets `X` and `Y` satisfy the same relations with `s` terms
  on each side, up to a permutation of the indices.
* `canonicalFreimanRelationCode ht X`: a code of the relations of `X` that is the same for
  equivalent sets.
* `boundedFreimanDimSets n r t`: the sets `X ⊆ [n]` with `t` elements and Freiman dimension at
  most `r`.

## Main statements

* `relationModelDim_le_freimanDim`: `relationModelDim` of the increasing enumeration of `X` is at
  most `freimanDim X`.
* `exists_determiningCoordinates`, `tuple_eq_of_relations_of_determiningCoordinates`: a tuple is
  determined by its relations and by its values at `relationModelDim a + 1` coordinates.
* `card_boundedFreimanDimSets`: there are at most `n ^ (r + 1) * t ^ (4 * t)` sets in
  `boundedFreimanDimSets n r t`.
* `card_canonicalFreimanRelationCode_image_of_fixed_extensionBase`: the number of canonical codes
  of sets of `l + d` elements whose first `l` elements have fixed relations.
* `ncard_restrictedSumset_subset_class_image_le`: the number of canonical codes of sets of `u`
  elements of the restricted sumsets of sets with a fixed canonical code.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open SumOfSetsInSeveralDimensions
open scoped Pointwise

noncomputable section

/-! ### The relations of a tuple -/

/-- The coefficient vector of the relation `aᵢ + aⱼ = aₖ + aₗ`, where `p = (i, j, k, l)`. -/
def relationVector {t : ℕ} (p : RelationIndex t) : Fin t →₀ ℚ :=
  Finsupp.single p.1 1 + Finsupp.single p.2.1 1 -
    Finsupp.single p.2.2.1 1 - Finsupp.single p.2.2.2 1

/-- The tuple `a` satisfies the relation `aᵢ + aⱼ = aₖ + aₗ`, where `p = (i, j, k, l)`. -/
def relationHolds {t : ℕ} (a : Fin t → ℕ) (p : RelationIndex t) : Prop :=
  a p.1 + a p.2.1 = a p.2.2.1 + a p.2.2.2

private def tupleEval {t : ℕ} (a : Fin t → ℕ) : (Fin t →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun i ↦ (a i : ℚ)

/-- The linear form on `ℚ^t` that sums the coefficients of a vector. -/
def coefficientSum (t : ℕ) : (Fin t →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun _ ↦ 1

/-- The space of the vectors of `ℚ^t` whose coefficients sum to zero. -/
def zeroSumSpace (t : ℕ) : Submodule ℚ (Fin t →₀ ℚ) :=
  LinearMap.ker (coefficientSum t)

private lemma relationVector_mem_ker_iff {t : ℕ} (a : Fin t → ℕ) (p : RelationIndex t) :
    relationVector p ∈ LinearMap.ker (tupleEval a) ↔ relationHolds a p := by
  simp only [LinearMap.mem_ker, tupleEval, relationVector, map_sub, map_add,
    Finsupp.linearCombination_single, one_smul, relationHolds, ← @Nat.cast_inj ℚ, Nat.cast_add]
  grind

private lemma coefficientSum_relationVector {t : ℕ} (p : RelationIndex t) :
    coefficientSum t (relationVector p) = 0 := by
  simp [coefficientSum, relationVector]

/-- The rational span of the coefficient vectors of the relations that `a` satisfies. -/
def relationSpace {t : ℕ} (a : Fin t → ℕ) : Submodule ℚ (Fin t →₀ ℚ) :=
  Submodule.span ℚ (relationVector '' {p | relationHolds a p})

private lemma relationSpace_le_zeroSumSpace {t : ℕ} (a : Fin t → ℕ) :
    relationSpace a ≤ zeroSumSpace t := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, -, rfl⟩
  exact coefficientSum_relationVector p

private lemma relationSpace_le_ker_tupleEval {t : ℕ} {a b : Fin t → ℕ}
    (h : ∀ p, relationHolds a p → relationHolds b p) :
    relationSpace a ≤ LinearMap.ker (tupleEval b) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  exact (relationVector_mem_ker_iff b p).mpr (h p hp)

/-- The relation space of `a` as a subspace of the zero-sum space. -/
def relationSpaceInZeroSum {t : ℕ} (a : Fin t → ℕ) :
    Submodule ℚ (zeroSumSpace t) :=
  (relationSpace a).comap (zeroSumSpace t).subtype

private lemma finrank_relationSpaceInZeroSum {t : ℕ} (a : Fin t → ℕ) :
    Module.finrank ℚ (relationSpaceInZeroSum a) = Module.finrank ℚ (relationSpace a) := by
  rw [← Submodule.finrank_map_subtype_eq (zeroSumSpace t) (relationSpaceInZeroSum a),
    relationSpaceInZeroSum, Submodule.map_comap_subtype,
    inf_eq_right.mpr (relationSpace_le_zeroSumSpace a)]

/-- The dimension of the quotient of the zero-sum space by the relations of `a`. For `t > 0` it
is `t - 1` minus the rank of the relations. -/
def relationModelDim {t : ℕ} (a : Fin t → ℕ) : ℕ :=
  Module.finrank ℚ (zeroSumSpace t ⧸ relationSpaceInZeroSum a)

private lemma coefficientSum_surjective {t : ℕ} (ht : 0 < t) :
    Function.Surjective (coefficientSum t) := by
  intro x
  exact ⟨Finsupp.single ⟨0, ht⟩ x, by simp [coefficientSum]⟩

private lemma finrank_zeroSumSpace {t : ℕ} (ht : 0 < t) :
    Module.finrank ℚ (zeroSumSpace t) = t - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (coefficientSum t)
  rw [LinearMap.range_eq_top.mpr (coefficientSum_surjective ht), finrank_top,
    Module.finrank_self, Module.finrank_finsupp_self, Fintype.card_fin] at h
  grind [zeroSumSpace]

private lemma relationModelDim_add_relationRank {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    relationModelDim a + Module.finrank ℚ (relationSpace a) = t - 1 := by
  rw [relationModelDim, ← finrank_relationSpaceInZeroSum,
    Submodule.finrank_quotient_add_finrank, finrank_zeroSumSpace ht]

private lemma relation_iff_mem_relationSpace {t : ℕ} (a : Fin t → ℕ)
    (p : RelationIndex t) :
    relationHolds a p ↔ relationVector p ∈ relationSpace a := by
  refine ⟨fun hp ↦ Submodule.subset_span ⟨p, hp, rfl⟩, fun hp ↦ ?_⟩
  rw [← relationVector_mem_ker_iff]
  exact relationSpace_le_ker_tupleEval (fun _ hq ↦ hq) hp

private lemma finrank_relationSpace_le {t : ℕ} (a : Fin t → ℕ) :
    Module.finrank ℚ (relationSpace a) ≤ t :=
  (relationSpace a).finrank_le.trans_eq (by simp)

/-- At most `t` relations span all the relations of a `t`-tuple. The family is padded with the
trivial relation so that it has exactly `t` entries. -/
private lemma exists_relation_code {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    ∃ code : Fin t → RelationIndex t,
      Submodule.span ℚ (relationVector '' Set.range code) = relationSpace a := by
  obtain ⟨basis, hmem, hspan, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (relationVector '' {p | relationHolds a p})
  choose index hindex using hmem
  refine ⟨fun i ↦ if hi : i.val < _ then index ⟨i, hi⟩ else (⟨0, ht⟩, ⟨0, ht⟩, ⟨0, ht⟩, ⟨0, ht⟩),
    le_antisymm (Submodule.span_le.mpr ?_) (hspan.ge.trans (Submodule.span_le.mpr ?_))⟩
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    dsimp only
    split
    · exact Submodule.subset_span ⟨_, (hindex _).1, rfl⟩
    · simp [relationVector]
  · rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span
      ⟨index i, ⟨⟨i, i.isLt.trans_le (finrank_relationSpace_le a)⟩, ?_⟩, (hindex i).2⟩
    simp

private noncomputable def relationCode {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Fin t → RelationIndex t :=
  (exists_relation_code ht a).choose

private lemma relationCode_span {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Submodule.span ℚ (relationVector '' Set.range (relationCode ht a)) = relationSpace a :=
  (exists_relation_code ht a).choose_spec

private lemma relations_iff_of_relationCode_eq {t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ} (hcode : relationCode ht a = relationCode ht b)
    (p : RelationIndex t) :
    relationHolds a p ↔ relationHolds b p := by
  rw [relation_iff_mem_relationSpace, relation_iff_mem_relationSpace,
    ← relationCode_span ht a, ← relationCode_span ht b, hcode]

private lemma card_relation_codes (t : ℕ) :
    Fintype.card (Fin t → RelationIndex t) = t ^ (4 * t) := by
  simp only [RelationIndex, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  ring

/-! ### The relation model -/

private def baseDifference {t : ℕ} (i₀ i : Fin t) : zeroSumSpace t :=
  ⟨Finsupp.single i 1 - Finsupp.single i₀ 1, by simp [zeroSumSpace, coefficientSum]⟩

private noncomputable def relationModelEquiv {t : ℕ} (a : Fin t → ℕ) :
    (zeroSumSpace t ⧸ relationSpaceInZeroSum a) ≃ₗ[ℚ] (Fin (relationModelDim a) → ℚ) :=
  LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun ℚ).symm

private noncomputable def relationModel {t : ℕ} (a : Fin t → ℕ) (i₀ i : Fin t) :
    Fin (relationModelDim a) → ℚ :=
  relationModelEquiv a ((relationSpaceInZeroSum a).mkQ (baseDifference i₀ i))

private lemma relationVector_eq_baseDifferences {t : ℕ} (i₀ : Fin t)
    (p : RelationIndex t) :
    relationVector p =
      (baseDifference i₀ p.1 : Fin t →₀ ℚ) + baseDifference i₀ p.2.1 -
        baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2 := by
  simp only [relationVector, baseDifference]
  abel

private lemma relationModel_add_eq_add_iff {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t)
    (p : RelationIndex t) :
    relationModel a i₀ p.1 + relationModel a i₀ p.2.1 =
        relationModel a i₀ p.2.2.1 + relationModel a i₀ p.2.2.2 ↔
      relationHolds a p := by
  simp only [relationModel, ← map_add]
  rw [(relationModelEquiv a).injective.eq_iff, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, relation_iff_mem_relationSpace,
    relationVector_eq_baseDifferences i₀, sub_sub]
  rfl

private lemma span_baseDifferences {t : ℕ} (i₀ : Fin t) :
    Submodule.span ℚ (Set.range (baseDifference i₀)) = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  have hsum : ∑ i, x.1 i = 0 := by
    simpa [zeroSumSpace, coefficientSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      using x.2
  have hx : x = ∑ i, x.1 i • baseDifference i₀ i := by
    ext j
    simp [baseDifference, mul_sub, hsum, Finsupp.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma span_relationModel {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t) :
    Submodule.span ℚ (Set.range (relationModel a i₀)) = ⊤ := by
  have hrange : Set.range (relationModel a i₀) =
      ((relationModelEquiv a).toLinearMap ∘ₗ (relationSpaceInZeroSum a).mkQ) ''
        Set.range (baseDifference i₀) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span, span_baseDifferences, Submodule.map_top,
    LinearMap.range_eq_top]
  exact (relationModelEquiv a).surjective.comp (relationSpaceInZeroSum a).mkQ_surjective

private def rationalVectorToRealLinear (d : ℕ) : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℝ) where
  toFun := rationalVectorToReal
  map_add' x y := by
    ext i
    simp [rationalVectorToReal]
  map_smul' q x := by
    ext i
    simp [rationalVectorToReal, Rat.smul_def]

private lemma real_span_of_rational_span {d t : ℕ} (v : Fin t → (Fin d → ℚ))
    (hspan : Submodule.span ℚ (Set.range v) = ⊤) :
    Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v)) = ⊤ := by
  have hle : Submodule.span ℚ (Set.range v) ≤
      ((Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v))).restrictScalars ℚ).comap
        (rationalVectorToRealLinear d) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin d)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : Pi.basisFun ℝ (Fin d) j = rationalVectorToReal (Pi.single j 1) := by
    ext i
    simp [rationalVectorToReal, Pi.single_apply, apply_ite (Rat.cast : ℚ → ℝ)]
  rw [hj]
  exact hle (hspan ▸ Submodule.mem_top)

private lemma relationModel_zero {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t) :
    relationModel a i₀ i₀ = 0 := by
  have hbase : baseDifference i₀ i₀ = 0 := Subtype.ext (sub_self _)
  rw [relationModel, hbase, map_zero, map_zero]

private lemma relationModel_affineDim {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t) :
    finsetAffineDim (((Finset.univ.image (relationModel a i₀)).image
      rationalVectorToReal)) = relationModelDim a := by
  have hset : (((Finset.univ.image (relationModel a i₀)).image rationalVectorToReal :
      Finset (Fin (relationModelDim a) → ℝ)) : Set (Fin (relationModelDim a) → ℝ)) =
      Set.range (rationalVectorToReal ∘ relationModel a i₀) := by
    simp [Set.range_comp]
  rw [finsetAffineDim, direction_affineSpan, hset, vectorSpan_eq_span_vsub_set_right ℝ (p := 0)]
  · have htranslate : (fun x ↦ x -ᵥ (0 : Fin (relationModelDim a) → ℝ)) ''
        Set.range (rationalVectorToReal ∘ relationModel a i₀) =
        Set.range (rationalVectorToReal ∘ relationModel a i₀) := by
      simp
    rw [htranslate, real_span_of_rational_span _ (span_relationModel a i₀), finrank_top,
      Module.finrank_fin_fun]
  · refine ⟨i₀, ?_⟩
    ext i
    simp [relationModel_zero, rationalVectorToReal]

/-! ### Enumerations of finite sets and canonical relation codes -/

/-- The increasing enumeration of a set of `t` natural numbers. -/
def finsetTuple {t : ℕ} (X : Finset ℕ) (hX : X.card = t) : Fin t → ℕ :=
  fun i ↦ X.orderIsoOfFin hX i

lemma finsetTuple_injective {t : ℕ} (X : Finset ℕ) (hX : X.card = t) :
    Function.Injective (finsetTuple X hX) :=
  (X.orderEmbOfFin hX).injective

lemma range_finsetTuple {t : ℕ} (X : Finset ℕ) (hX : X.card = t) :
    Set.range (finsetTuple X hX) = X :=
  X.range_orderEmbOfFin hX

private lemma finsetTuple_mem {t : ℕ} (X : Finset ℕ) (hX : X.card = t) (i : Fin t) :
    finsetTuple X hX i ∈ X :=
  (X.orderIsoOfFin hX i).2

/-- The sets of `t` natural numbers. -/
abbrev SizedNatFinset (t : ℕ) :=
  {X : Finset ℕ // X.card = t}

/-- The enumeration of `X` obtained from the increasing one by the permutation `e`. -/
def permutedFinsetTuple {t : ℕ} (X : SizedNatFinset t)
    (e : Equiv.Perm (Fin t)) :
    Fin t → ℕ :=
  finsetTuple X.1 X.2 ∘ e

lemma permutedFinsetTuple_injective {t : ℕ} (X : SizedNatFinset t)
    (e : Equiv.Perm (Fin t)) : Function.Injective (permutedFinsetTuple X e) :=
  (finsetTuple_injective X.1 X.2).comp e.injective

lemma range_permutedFinsetTuple {t : ℕ} (X : SizedNatFinset t)
    (e : Equiv.Perm (Fin t)) : Set.range (permutedFinsetTuple X e) = X.1 := by
  rw [permutedFinsetTuple, Set.range_comp, e.surjective.range_eq, Set.image_univ,
    range_finsetTuple X.1 X.2]

private lemma permutedFinsetTuple_mem {t : ℕ} (X : SizedNatFinset t) (e : Equiv.Perm (Fin t))
    (i : Fin t) : permutedFinsetTuple X e i ∈ X.1 :=
  finsetTuple_mem X.1 X.2 (e i)

private def tupleRange {t : ℕ} (a : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image a

private lemma card_tupleRange {t : ℕ} (a : Fin t → ℕ) (ha : Function.Injective a) :
    (tupleRange a).card = t := by
  simp [tupleRange, Finset.card_image_of_injective _ ha]

private def tupleRangeSized {t : ℕ} (a : Fin t → ℕ) (ha : Function.Injective a) :
    SizedNatFinset t :=
  ⟨tupleRange a, card_tupleRange a ha⟩

private lemma tupleRangeSized_eq {t : ℕ} {a : Fin t → ℕ} (ha : Function.Injective a)
    {X : SizedNatFinset t} (h : Set.range a = X.1) : tupleRangeSized a ha = X := by
  apply Subtype.ext
  apply Finset.coe_injective
  simpa [tupleRangeSized, tupleRange] using h

private noncomputable def tupleRangePermutation {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) : Equiv.Perm (Fin t) :=
  Equiv.ofBijective
    (fun i ↦ ((tupleRange a).orderIsoOfFin (card_tupleRange a ha)).symm
      ⟨a i, by simp [tupleRange]⟩)
    (Finite.injective_iff_bijective.mp fun _ _ hij ↦
      ha (Subtype.mk.inj ((OrderIso.injective _) hij)))

private lemma permutedFinsetTuple_tupleRangePermutation {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) :
    permutedFinsetTuple (tupleRangeSized a ha) (tupleRangePermutation a ha) = a := by
  funext i
  simp [permutedFinsetTuple, finsetTuple, tupleRangePermutation, tupleRangeSized]

private lemma finsetTuple_tupleRangeSized {t : ℕ} (a : Fin t → ℕ) (ha : Function.Injective a) :
    finsetTuple (tupleRangeSized a ha).1 (tupleRangeSized a ha).2 =
      a ∘ (tupleRangePermutation a ha).symm :=
  (Equiv.eq_comp_symm _ _ _).mpr (permutedFinsetTuple_tupleRangePermutation a ha)

private lemma permutedFinsetTuple_trans_tupleRangePermutation {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) (e : Equiv.Perm (Fin t)) :
    permutedFinsetTuple (tupleRangeSized a ha) (e.trans (tupleRangePermutation a ha)) = a ∘ e :=
  congrArg (· ∘ ⇑e) (permutedFinsetTuple_tupleRangePermutation a ha)

/-- The relation obtained from `p` by applying the permutation `e` to its indices. -/
def permuteFreimanRelation {s t : ℕ} (e : Equiv.Perm (Fin t))
    (p : FreimanRelationIndex s t) : FreimanRelationIndex s t :=
  (e ∘ p.1, e ∘ p.2)

lemma freimanRelationHolds_comp_perm {s t : ℕ} (a : Fin t → ℕ)
    (e : Equiv.Perm (Fin t)) (p : FreimanRelationIndex s t) :
    freimanRelationHolds (a ∘ e) p ↔
      freimanRelationHolds a (permuteFreimanRelation e p) :=
  Iff.rfl

/-- Two sets of `t` natural numbers satisfy the same relations with `s` terms on each side, up
to a permutation of the indices. This is Green's `s`-isomorphism, stated for the increasing
enumerations of the sets. -/
def FreimanRelationEquivalent {s t : ℕ} (X Y : SizedNatFinset t) : Prop :=
  ∃ e : Equiv.Perm (Fin t),
    ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds (finsetTuple X.1 X.2) p ↔
        freimanRelationHolds (permutedFinsetTuple Y e) p

private lemma FreimanRelationEquivalent.symm {s t : ℕ} {X Y : SizedNatFinset t}
    (h : FreimanRelationEquivalent (s := s) X Y) : FreimanRelationEquivalent (s := s) Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun p ↦ ?_⟩
  simpa [permutedFinsetTuple, freimanRelationHolds, permuteFreimanRelation] using
    (he (permuteFreimanRelation e.symm p)).symm

private lemma freimanRelationEquivalent_tupleRange {s t : ℕ} {a b : Fin t → ℕ}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hrelations : ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    FreimanRelationEquivalent (s := s) (tupleRangeSized a ha) (tupleRangeSized b hb) := by
  refine ⟨(tupleRangePermutation a ha).symm.trans (tupleRangePermutation b hb), fun p ↦ ?_⟩
  rw [finsetTuple_tupleRangeSized, permutedFinsetTuple_trans_tupleRangePermutation]
  exact hrelations (permuteFreimanRelation _ p)

/-- The relation codes of all the enumerations of `X`. -/
def finsetFreimanRelationCodes {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : Finset (Fin t → FreimanRelationIndex s t) :=
  Finset.univ.image fun e : Equiv.Perm (Fin t) ↦
    freimanRelationCode (s := s) ht (permutedFinsetTuple X e)

lemma finsetFreimanRelationCodes_nonempty {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : (finsetFreimanRelationCodes (s := s) ht X).Nonempty :=
  Finset.univ_nonempty.image _

private lemma finsetFreimanRelationCodes_subset_of_equivalent {s t : ℕ} (ht : 0 < t)
    {X Y : SizedNatFinset t} (hXY : FreimanRelationEquivalent (s := s) X Y) :
    finsetFreimanRelationCodes (s := s) ht X ⊆ finsetFreimanRelationCodes (s := s) ht Y := by
  obtain ⟨e, he⟩ := hXY
  intro code hcode
  simp only [finsetFreimanRelationCodes, Finset.mem_image, Finset.mem_univ, true_and] at hcode ⊢
  obtain ⟨f, rfl⟩ := hcode
  exact ⟨f.trans e, freimanRelationCode_eq_of_relations_iff ht fun p ↦
    (he (permuteFreimanRelation f p)).symm⟩

/-- The least relation code of an enumeration of `X`. Sets that are `FreimanRelationEquivalent`
have the same canonical code. -/
noncomputable def canonicalFreimanRelationCode {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : Fin t → FreimanRelationIndex s t :=
  (finsetFreimanRelationCodes (s := s) ht X).min'
    (finsetFreimanRelationCodes_nonempty (s := s) ht X)

lemma canonicalFreimanRelationCode_mem {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) :
    canonicalFreimanRelationCode (s := s) ht X ∈
      finsetFreimanRelationCodes (s := s) ht X :=
  Finset.min'_mem _ _

lemma canonicalFreimanRelationCode_eq_of_equivalent {s t : ℕ} (ht : 0 < t)
    {X Y : SizedNatFinset t} (hXY : FreimanRelationEquivalent (s := s) X Y) :
    canonicalFreimanRelationCode (s := s) ht X =
      canonicalFreimanRelationCode (s := s) ht Y := by
  simp only [canonicalFreimanRelationCode,
    (finsetFreimanRelationCodes_subset_of_equivalent ht hXY).antisymm
      (finsetFreimanRelationCodes_subset_of_equivalent ht hXY.symm)]

/-- Let the sets `full x`, for `x ∈ S`, have `l + d` elements, with enumerations `label x` whose
first `l` entries satisfy the same relations with four terms on each side. Then the sets `full x`
have at most `(1 + l ^ 4) ^ ((d + 1) ^ 4)` canonical codes of relations with two terms on each
side. -/
lemma card_canonicalFreimanRelationCode_image_of_fixed_extensionBase
    {α : Type*} {l d : ℕ} (hl : 0 < l) (S : Finset α)
    (full : α → SizedNatFinset (l + d)) (label : α → Fin (l + d) → ℕ)
    (hlabelInjective : ∀ x ∈ S, Function.Injective (label x))
    (hlabelRange : ∀ x ∈ S, Set.range (label x) = (full x).1)
    (hbase : ∀ x ∈ S, ∀ y ∈ S, ∀ p : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple (label x)) p ↔
        freimanRelationHolds (extensionBaseTuple (label y)) p) :
    (S.image fun x ↦ canonicalFreimanRelationCode (s := 2) (Nat.add_pos_left hl d)
      (full x)).card ≤ (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
  rw [← card_extensionCodeType]
  apply card_image_le_fintype_of_eq_imp_eq S _ fun x ↦ extensionCode (label x)
  intro x hx y hy hcode
  rw [← tupleRangeSized_eq (hlabelInjective x hx) (hlabelRange x hx),
    ← tupleRangeSized_eq (hlabelInjective y hy) (hlabelRange y hy)]
  exact canonicalFreimanRelationCode_eq_of_equivalent _ (freimanRelationEquivalent_tupleRange _ _
    (freimanRelations_iff_of_extensionCode_eq ⟨0, hl⟩ _ _ hcode (hbase x hx y hy)))

lemma exists_canonicalLabeling {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) :
    ∃ e : Equiv.Perm (Fin t),
      freimanRelationCode (s := s) ht (permutedFinsetTuple X e) =
        canonicalFreimanRelationCode (s := s) ht X := by
  simpa [finsetFreimanRelationCodes] using
    canonicalFreimanRelationCode_mem (s := s) ht X

private noncomputable def canonicalLabeling {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : Equiv.Perm (Fin t) :=
  (exists_canonicalLabeling (s := s) ht X).choose

private lemma canonicalLabeling_code {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) :
    freimanRelationCode (s := s) ht
      (permutedFinsetTuple X (canonicalLabeling (s := s) ht X)) =
      canonicalFreimanRelationCode (s := s) ht X :=
  (exists_canonicalLabeling (s := s) ht X).choose_spec

private lemma canonicalLabelings_relations_iff {s t : ℕ} (ht : 0 < t)
    (X Y : SizedNatFinset t)
    (hcode : canonicalFreimanRelationCode (s := s) ht X =
      canonicalFreimanRelationCode (s := s) ht Y)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds
        (permutedFinsetTuple X (canonicalLabeling (s := s) ht X)) p ↔
      freimanRelationHolds
        (permutedFinsetTuple Y (canonicalLabeling (s := s) ht Y)) p := by
  refine freimanRelations_iff_of_code_eq ht ?_ p
  rw [canonicalLabeling_code, canonicalLabeling_code, hcode]

private def permutedRestrictedSumRepresentation {l u : ℕ} (A : SizedNatFinset l)
    (B : SizedNatFinset u) (hBA : B.1 ⊆ restrictedSumset A.1) (e : Equiv.Perm (Fin l)) :
    Fin u → Fin l × Fin l :=
  fun i ↦ (e.symm (restrictedSumRepresentation A.1 B.1 A.2 B.2 hBA i).1,
    e.symm (restrictedSumRepresentation A.1 B.1 A.2 B.2 hBA i).2)

private lemma pairSumTuple_permutedRestrictedSumRepresentation {l u : ℕ} (A : SizedNatFinset l)
    (B : SizedNatFinset u) (hBA : B.1 ⊆ restrictedSumset A.1) (e : Equiv.Perm (Fin l)) :
    pairSumTuple (permutedFinsetTuple A e) (permutedRestrictedSumRepresentation A B hBA e) =
      finsetTuple B.1 B.2 := by
  refine Eq.trans ?_ (pairSumTuple_restrictedSumRepresentation A.1 B.1 A.2 B.2 hBA)
  funext i
  simp [pairSumTuple, permutedFinsetTuple, permutedRestrictedSumRepresentation, finsetTuple]

private lemma permutedRestrictedSumRepresentation_ne {l u : ℕ} (A : SizedNatFinset l)
    (B : SizedNatFinset u) (hBA : B.1 ⊆ restrictedSumset A.1) (e : Equiv.Perm (Fin l))
    (i : Fin u) :
    (permutedRestrictedSumRepresentation A B hBA e i).1 ≠
      (permutedRestrictedSumRepresentation A B hBA e i).2 :=
  e.symm.injective.ne (restrictedSumRepresentation_ne A.1 B.1 A.2 B.2 hBA i)

/-- The enumeration of `A` that lists `A₁` in the order given by `e` and then `A \ A₁` in
increasing order. -/
def extensionFinsetTuple {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u)) :
    Fin (u + d) → ℕ :=
  fun i ↦ match finSumFinEquiv.symm i with
  | Sum.inl j => permutedFinsetTuple ⟨A₁, hA₁⟩ e j
  | Sum.inr j => finsetTuple (A \ A₁) hZ j

private lemma extensionFinsetTuple_left {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u))
    (i : Fin u) :
    extensionFinsetTuple A A₁ hA₁ hZ e (finSumFinEquiv (Sum.inl i)) =
      permutedFinsetTuple ⟨A₁, hA₁⟩ e i := by
  simp [extensionFinsetTuple]

private lemma extensionFinsetTuple_right {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u))
    (i : Fin d) :
    extensionFinsetTuple A A₁ hA₁ hZ e (finSumFinEquiv (Sum.inr i)) =
      finsetTuple (A \ A₁) hZ i := by
  simp [extensionFinsetTuple]

lemma extensionBaseTuple_extensionFinsetTuple {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u)) :
    extensionBaseTuple (extensionFinsetTuple A A₁ hA₁ hZ e) =
      permutedFinsetTuple ⟨A₁, hA₁⟩ e :=
  funext (extensionFinsetTuple_left A A₁ hA₁ hZ e)

lemma extensionFinsetTuple_injective {u d : ℕ} {A A₁ : Finset ℕ}
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d)
    (e : Equiv.Perm (Fin u)) :
    Function.Injective (extensionFinsetTuple A A₁ hA₁ hZ e) := by
  have hne (i : Fin u) (j : Fin d) :
      permutedFinsetTuple ⟨A₁, hA₁⟩ e i ≠ finsetTuple (A \ A₁) hZ j := fun h ↦
    (Finset.mem_sdiff.mp (finsetTuple_mem _ hZ j)).2 (h ▸ permutedFinsetTuple_mem ⟨A₁, hA₁⟩ e i)
  intro i j hij
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [extensionFinsetTuple_left, extensionFinsetTuple_right] at hij
  · rw [permutedFinsetTuple_injective _ e hij]
  · exact (hne i j hij).elim
  · exact (hne j i hij.symm).elim
  · rw [finsetTuple_injective _ hZ hij]

lemma range_extensionFinsetTuple {u d : ℕ} {A A₁ : Finset ℕ}
    (hA₁A : A₁ ⊆ A) (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d)
    (e : Equiv.Perm (Fin u)) :
    Set.range (extensionFinsetTuple A A₁ hA₁ hZ e) = A := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
    · rw [extensionFinsetTuple_left]
      exact hA₁A (permutedFinsetTuple_mem ⟨A₁, hA₁⟩ e i)
    · rw [extensionFinsetTuple_right]
      exact (Finset.mem_sdiff.mp (finsetTuple_mem _ hZ i)).1
  · intro hx
    by_cases hxA₁ : x ∈ A₁
    · obtain ⟨i, rfl⟩ : x ∈ Set.range (permutedFinsetTuple ⟨A₁, hA₁⟩ e) := by
        rwa [range_permutedFinsetTuple]
      exact ⟨finSumFinEquiv (Sum.inl i), extensionFinsetTuple_left A A₁ hA₁ hZ e i⟩
    · obtain ⟨i, rfl⟩ : x ∈ Set.range (finsetTuple (A \ A₁) hZ) := by
        rw [range_finsetTuple]
        exact Finset.mem_sdiff.mpr ⟨hx, hxA₁⟩
      exact ⟨finSumFinEquiv (Sum.inr i), extensionFinsetTuple_right A A₁ hA₁ hZ e i⟩

/-- Lemma 17 of Green, in the form used to count classes. Let `A` and `C` be sets of `l` natural
numbers with the same canonical code of relations with eight terms on each side. For every set
`B` of `u` elements of the restricted sumset of `A`, there is a set `D` of `u` elements of the
restricted sumset of `C` with the same canonical code of relations with four terms on each side
as `B`. -/
lemma exists_restrictedSumset_subset_equivalent {l u : ℕ}
    (hl : 0 < l) (hu : 0 < u) (A C : SizedNatFinset l) (B : SizedNatFinset u)
    (hBA : B.1 ⊆ restrictedSumset A.1)
    (hcoreCode : canonicalFreimanRelationCode (s := 8) hl A =
      canonicalFreimanRelationCode (s := 8) hl C) :
    ∃ D : SizedNatFinset u, D.1 ⊆ restrictedSumset C.1 ∧
      canonicalFreimanRelationCode (s := 4) hu B =
        canonicalFreimanRelationCode (s := 4) hu D := by
  let eA := canonicalLabeling (s := 8) hl A
  let c := permutedFinsetTuple C (canonicalLabeling (s := 8) hl C)
  let representation := permutedRestrictedSumRepresentation A B hBA eA
  have hrelations (p : FreimanRelationIndex 4 u) :
      freimanRelationHolds (finsetTuple B.1 B.2) p ↔
        freimanRelationHolds (pairSumTuple c representation) p := by
    rw [← pairSumTuple_permutedRestrictedSumRepresentation A B hBA eA]
    exact pairSumTuple_relations_iff (canonicalLabelings_relations_iff hl A C hcoreCode)
      representation p
  have hinjective : Function.Injective (pairSumTuple c representation) :=
    injective_of_four_relations_iff (finsetTuple_injective B.1 B.2) hrelations
  refine ⟨tupleRangeSized _ hinjective, ?_, ?_⟩
  · have hsubset := pairSumRange_subset_restrictedSumset c
      (permutedFinsetTuple_injective C _) representation
      (permutedRestrictedSumRepresentation_ne A B hBA eA)
    have hrange : Finset.univ.image c = C.1 := by
      apply Finset.coe_injective
      simpa using range_permutedFinsetTuple C (canonicalLabeling (s := 8) hl C)
    rwa [hrange] at hsubset
  · have hcode := canonicalFreimanRelationCode_eq_of_equivalent hu
      (freimanRelationEquivalent_tupleRange (finsetTuple_injective B.1 B.2) hinjective hrelations)
    rwa [tupleRangeSized_eq _ (range_finsetTuple B.1 B.2)] at hcode

/-- Let `C` be a set of `l` natural numbers, and let every member `B` of `family` lie in the
restricted sumset of a set with the same canonical code of relations with eight terms on each
side as `C`. Then the members of `family` have at most `(|C ∔ C| choose u)` canonical codes of
relations with four terms on each side, where `C ∔ C` is the restricted sumset of `C`. -/
lemma ncard_restrictedSumset_subset_class_image_le {l u : ℕ}
    (hl : 0 < l) (hu : 0 < u) (C : SizedNatFinset l)
    (family : Set (SizedNatFinset u))
    (hfamily : ∀ B ∈ family, ∃ A : SizedNatFinset l,
      B.1 ⊆ restrictedSumset A.1 ∧
        canonicalFreimanRelationCode (s := 8) hl A =
          canonicalFreimanRelationCode (s := 8) hl C) :
    (canonicalFreimanRelationCode (s := 4) hu '' family).ncard ≤
      (restrictedSumset C.1).card.choose u := by
  let encode : ↑((restrictedSumset C.1).powersetCard u) → (Fin u → FreimanRelationIndex 4 u) :=
    fun D ↦ canonicalFreimanRelationCode (s := 4) hu ⟨D.1, (Finset.mem_powersetCard.mp D.2).2⟩
  have hsubset : canonicalFreimanRelationCode (s := 4) hu '' family ⊆ Set.range encode := by
    rintro _ ⟨B, hB, rfl⟩
    obtain ⟨A, hBA, hcode⟩ := hfamily B hB
    obtain ⟨D, hDC, hBD⟩ := exists_restrictedSumset_subset_equivalent hl hu A C B hBA hcode
    exact ⟨⟨D.1, Finset.mem_powersetCard.mpr ⟨hDC, D.2⟩⟩, hBD.symm⟩
  apply (Set.ncard_le_ncard hsubset (Set.toFinite _)).trans
  rw [← Set.image_univ]
  apply (Set.ncard_image_le (s := Set.univ)).trans_eq
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard]

/-! ### The relation model is a Freiman model -/

/-- Two injective tuples that satisfy the same relations `xᵢ + xⱼ = xₖ + xₗ` have Freiman
isomorphic ranges. -/
lemma tuple_freimanIso {t : ℕ} {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    {a : Fin t → G} {b : Fin t → H} (ht : 0 < t)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hrelations : ∀ i j k l, a i + a j = a k + a l ↔ b i + b j = b k + b l) :
    ∃ f : G → H, IsAddFreimanIso 2 (Set.range a) (Set.range b) f := by
  have : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  let f : G → H := fun x ↦ b (Function.invFun a x)
  have hf (i : Fin t) : f (a i) = b i := congrArg b (Function.leftInverse_invFun ha i)
  refine ⟨f, isAddFreimanIso_two.mpr ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨i, (hf i).symm⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [hf i, hf j] at hij
    exact congrArg a (hb hij)
  · rintro _ ⟨i, rfl⟩
    exact ⟨a i, ⟨i, rfl⟩, hf i⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    rw [hf i, hf j, hf k, hf l]
    exact (hrelations i j k l).symm

private lemma relationModel_injective {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) (i₀ : Fin t) :
    Function.Injective (relationModel a i₀) := by
  intro i j hij
  exact ha (Nat.add_right_cancel ((relationModel_add_eq_add_iff a i₀ (i, i₀, j, i₀)).mp
    (congrArg (· + relationModel a i₀ i₀) hij)))

private lemma freimanModelDim_relationModel {t : ℕ} (ht : 0 < t) (X : SizedNatFinset t) :
    freimanModelDim X.1 (relationModelDim (finsetTuple X.1 X.2)) := by
  obtain ⟨f, hf⟩ := tuple_freimanIso ht (finsetTuple_injective X.1 X.2)
    (relationModel_injective _ (finsetTuple_injective X.1 X.2) ⟨0, ht⟩)
    fun i j k l ↦ (relationModel_add_eq_add_iff _ ⟨0, ht⟩ (i, j, k, l)).symm
  rw [range_finsetTuple] at hf
  have himage : X.1.image f =
      Finset.univ.image (relationModel (finsetTuple X.1 X.2) ⟨0, ht⟩) := by
    apply Finset.coe_injective
    rw [Finset.coe_image, hf.bijOn.image_eq, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨f, ?_, ?_⟩
  · rwa [himage, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · rw [himage]
    exact relationModel_affineDim _ _

/-- The relation model of a set shows that its Freiman dimension is at least
`relationModelDim`. -/
lemma relationModelDim_le_freimanDim {t : ℕ} (ht : 0 < t)
    (X : {X : Finset ℕ // X.card = t}) :
    relationModelDim (finsetTuple X X.2) ≤ freimanDim X.1 := by
  classical
  unfold freimanDim
  refine Nat.le_findGreatest ?_ (freimanModelDim_relationModel ht X)
  rw [X.2]
  grind [relationModelDim_add_relationRank ht (finsetTuple X X.2)]

/-! ### Determining coordinates -/

/-- The class of the `i`-th coordinate vector in the quotient of `ℚ^t` by the relations of
`a`. -/
def coordinateClass {t : ℕ} (a : Fin t → ℕ) (i : Fin t) :
    (Fin t →₀ ℚ) ⧸ relationSpace a :=
  (relationSpace a).mkQ (Finsupp.single i 1)

private lemma finrank_relationQuotient {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Module.finrank ℚ ((Fin t →₀ ℚ) ⧸ relationSpace a) = relationModelDim a + 1 := by
  have h := Submodule.finrank_quotient_add_finrank (relationSpace a)
  rw [Module.finrank_finsupp_self, Fintype.card_fin] at h
  grind [relationModelDim_add_relationRank ht a]

private lemma span_coordinateClass {t : ℕ} (a : Fin t → ℕ) :
    Submodule.span ℚ (Set.range (coordinateClass a)) = ⊤ := by
  have hrange : Set.range (coordinateClass a) =
      (relationSpace a).mkQ '' Set.range (Finsupp.basisSingleOne (R := ℚ)) := by
    rw [Finsupp.coe_basisSingleOne, ← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
    LinearMap.range_eq_top]
  exact (relationSpace a).mkQ_surjective

/-- If `relationModelDim a ≤ r`, then the classes of some `r + 1` coordinate vectors span the
quotient of `ℚ^t` by the relations of `a`. -/
lemma exists_determiningCoordinates {t r : ℕ} (ht : 0 < t) (a : Fin t → ℕ)
    (hdr : relationModelDim a ≤ r) :
    ∃ anchor : Fin (r + 1) → Fin t,
      Submodule.span ℚ (Set.range (coordinateClass a ∘ anchor)) = ⊤ := by
  obtain ⟨basis, hmem, hspan, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range (coordinateClass a))
  choose index hindex using hmem
  have hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range (coordinateClass a))) ≤ r + 1 := by
    rw [span_coordinateClass, finrank_top, finrank_relationQuotient ht]
    grind
  refine ⟨fun i ↦ if hi : i.val < _ then index ⟨i, hi⟩ else ⟨0, ht⟩, ?_⟩
  rw [eq_top_iff]
  refine (span_coordinateClass a).ge.trans (hspan.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castLE hrank i, by simp [hindex]⟩

/-- Two tuples that satisfy the same relations as `a` and agree at coordinates whose classes span
the quotient by the relations of `a` are equal. -/
lemma tuple_eq_of_relations_of_determiningCoordinates {t r : ℕ}
    (a b c : Fin t → ℕ) (anchor : Fin (r + 1) → Fin t)
    (hspan : Submodule.span ℚ (Set.range (coordinateClass a ∘ anchor)) = ⊤)
    (hb : ∀ p, relationHolds a p ↔ relationHolds b p)
    (hc : ∀ p, relationHolds a p ↔ relationHolds c p)
    (hanchor : ∀ i, b (anchor i) = c (anchor i)) : b = c := by
  have hf : (relationSpace a).liftQ (tupleEval b)
        (relationSpace_le_ker_tupleEval fun p ↦ (hb p).mp) =
      (relationSpace a).liftQ (tupleEval c) (relationSpace_le_ker_tupleEval fun p ↦ (hc p).mp) := by
    apply LinearMap.ext_on hspan
    rintro _ ⟨i, rfl⟩
    simpa [coordinateClass, tupleEval] using hanchor i
  funext i
  simpa [coordinateClass, tupleEval] using LinearMap.congr_fun hf (coordinateClass a i)

/-! ### Counting sets of bounded Freiman dimension -/

/-- The sets `X ⊆ [n]` with `t` elements and Freiman dimension at most `r`. -/
def boundedFreimanDimSets (n r t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ | X ⊆ Finset.Icc 1 n ∧ X.card = t ∧ freimanDim X ≤ r}

/-- The sets `X` of `boundedFreimanDimSets n r t` with `|X + X| ≤ s`. -/
def smallSumsetFreimanDimSets (n r s t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ |
    X ⊆ Finset.Icc 1 n ∧ X.card = t ∧ freimanDim X ≤ r ∧ (X + X).card ≤ s}

private abbrev BoundedFreimanDimMember (n r t : ℕ) :=
  {X : Finset ℕ // X ∈ boundedFreimanDimSets n r t}

private def memberTuple {n r t : ℕ} (X : BoundedFreimanDimMember n r t) : Fin t → ℕ :=
  finsetTuple X.1 X.2.2.1

private lemma relationModelDim_memberTuple_le {n r t : ℕ} (ht : 0 < t)
    (X : BoundedFreimanDimMember n r t) : relationModelDim (memberTuple X) ≤ r :=
  (relationModelDim_le_freimanDim ht ⟨X.1, X.2.2.1⟩).trans X.2.2.2

/-- The pair `p` consists of a tuple with relation code `code` and of `r + 1` coordinates whose
classes span the quotient by the relations of that tuple. -/
private def IsClassRepresentative {r t : ℕ} (ht : 0 < t) (code : Fin t → RelationIndex t)
    (p : (Fin t → ℕ) × (Fin (r + 1) → Fin t)) : Prop :=
  relationCode ht p.1 = code ∧ Submodule.span ℚ (Set.range (coordinateClass p.1 ∘ p.2)) = ⊤

private noncomputable def classRepresentative (r : ℕ) {t : ℕ} (ht : 0 < t)
    (code : Fin t → RelationIndex t) : (Fin t → ℕ) × (Fin (r + 1) → Fin t) :=
  @Classical.epsilon _ ⟨(fun _ ↦ 0, fun _ ↦ ⟨0, ht⟩)⟩ (IsClassRepresentative ht code)

private lemma isClassRepresentative_classRepresentative {r t : ℕ} (ht : 0 < t) {a : Fin t → ℕ}
    (ha : relationModelDim a ≤ r) :
    IsClassRepresentative ht (relationCode ht a)
      (classRepresentative r ht (relationCode ht a)) := by
  obtain ⟨anchor, hanchor⟩ := exists_determiningCoordinates ht a ha
  exact Classical.epsilon_spec ⟨(a, anchor), rfl, hanchor⟩

/-- A member `X` is encoded by the relation code of its increasing enumeration and by the values
of that enumeration at the `r + 1` coordinates attached to the code. -/
private noncomputable def freimanClassEncoding (n r t : ℕ) (ht : 0 < t)
    (X : BoundedFreimanDimMember n r t) :
    (Fin t → RelationIndex t) × (Fin (r + 1) → ↑(Finset.Icc 1 n)) :=
  (relationCode ht (memberTuple X), fun i ↦
    ⟨memberTuple X ((classRepresentative r ht (relationCode ht (memberTuple X))).2 i),
      X.2.1 (finsetTuple_mem X.1 X.2.2.1 _)⟩)

private lemma freimanClassEncoding_injective (n r t : ℕ) (ht : 0 < t) :
    Function.Injective (freimanClassEncoding n r t ht) := by
  intro X Y hXY
  have hcode : relationCode ht (memberTuple X) = relationCode ht (memberTuple Y) :=
    congrArg Prod.fst hXY
  have hvalues (i : Fin (r + 1)) := congrArg Subtype.val (congrFun (congrArg Prod.snd hXY) i)
  dsimp only [freimanClassEncoding] at hvalues
  rw [← hcode] at hvalues
  obtain ⟨hrep, hspan⟩ :=
    isClassRepresentative_classRepresentative ht (relationModelDim_memberTuple_le ht X)
  have htuple : memberTuple X = memberTuple Y :=
    tuple_eq_of_relations_of_determiningCoordinates _ _ _ _ hspan
      (relations_iff_of_relationCode_eq ht hrep)
      (relations_iff_of_relationCode_eq ht (hrep.trans hcode)) hvalues
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← range_finsetTuple X.1 X.2.2.1, ← range_finsetTuple Y.1 Y.2.2.1]
  exact congrArg Set.range htuple

private lemma ncard_boundedFreimanDimSets_le (n r t : ℕ) (ht : 0 < t) :
    (boundedFreimanDimSets n r t).ncard ≤ n ^ (r + 1) * t ^ (4 * t) := by
  have hfinite : (boundedFreimanDimSets n r t).Finite :=
    (Finset.Icc 1 n).powerset.finite_toSet.subset fun X hX ↦ Finset.mem_powerset.mpr hX.1
  let : Fintype (BoundedFreimanDimMember n r t) := hfinite.fintype
  have hcard := Fintype.card_le_of_injective _ (freimanClassEncoding_injective n r t ht)
  rw [Set.fintypeCard_eq_ncard, Fintype.card_prod, card_relation_codes, Fintype.card_fun,
    Fintype.card_coe] at hcard
  simpa [mul_comm] using hcard

/-- There are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with `t` elements and Freiman
dimension at most `r`. -/
theorem card_boundedFreimanDimSets (n r t : ℕ) (ht : 0 < t) :
    ((boundedFreimanDimSets n r t).ncard : ℝ) ≤
      (n : ℝ) ^ (r + 1) * (t : ℝ) ^ (4 * t) :=
  mod_cast ncard_boundedFreimanDimSets_le n r t ht

end

end CountingSetsWithSmallSumset
