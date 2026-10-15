/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Relation codes and extension codes for Freiman isomorphism classes

Two tuples of natural numbers are Freiman isomorphic of order `s` when they satisfy the same
additive relations with `s` summands on each side. This file encodes the relations of a tuple by
a finite amount of data and bounds the number of codes, following Section 3 of Green,
*Counting sets with small sumset, and the clique number of random Cayley graphs*. It also proves
the decomposition of a set with small restricted sumset used in Section 4 of that paper.

The source of version 2 of the paper is available at <https://arxiv.org/e-print/math/0304183>.

## Main definitions

* `freimanRelationHolds`: the tuple `a` satisfies a relation with `s` summands on each side.
* `freimanRelationCode`: `t` relations of a tuple of length `t` that determine all its relations.
* `restrictedSumset`: the set of sums of two distinct elements of a set.
* `extensionCode`: for a tuple of length `l + d` and each pattern of new coordinates in a
  relation with two summands, one relation of the tuple with that pattern.
* `pairSumTuple`: the tuple of sums of prescribed pairs of coordinates of a tuple.

## Main statements

* `freimanRelations_iff_of_code_eq`: tuples with the same relation code satisfy the same
  relations. There are `t ^ (2 * s * t)` codes by `card_freimanRelationCodes`.
* `exists_core_decomposition`: a finite set `A` with small restricted sumset has an element `a`
  and subsets `A₀` and `Z` such that `a + (A \ Z)` lies in the restricted sumset of `A₀`, with a
  bound on `|A₀| + R |Z|`.
* `freimanRelations_iff_of_extensionCode_eq`: two tuples of length `l + d` with the same
  extension code, whose first `l` coordinates satisfy the same relations with four summands,
  satisfy the same relations with two summands.
* `pairSumTuple_relations_iff`: if two tuples satisfy the same relations with eight summands,
  their tuples of pair sums satisfy the same relations with four summands.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset
open scoped Pointwise

noncomputable section

/-! ### Freiman relation systems and finite codes -/

/-- A pair of `s`-tuples of indices in `Fin t`. The pair `(i, j)` stands for the relation
`a (i 1) + ⋯ + a (i s) = a (j 1) + ⋯ + a (j s)` between the coordinates of a tuple `a`. -/
abbrev FreimanRelationIndex (s t : ℕ) :=
  (Fin s → Fin t) × (Fin s → Fin t)

/-- A linear order on tuples of relations. It is used to choose a least code. -/
noncomputable instance freimanRelationCodeLinearOrder (s t : ℕ) :
    LinearOrder (Fin t → FreimanRelationIndex s t) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

private def freimanRelationVector {s t : ℕ} (p : FreimanRelationIndex s t) :
    Fin t →₀ ℚ :=
  (∑ i, Finsupp.single (p.1 i) 1) - ∑ i, Finsupp.single (p.2 i) 1

/-- The tuple `a` satisfies the relation `p`: the sum of the coordinates of `a` indexed by `p.1`
equals the sum of those indexed by `p.2`. -/
def freimanRelationHolds {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) : Prop :=
  ∑ i, a (p.1 i) = ∑ i, a (p.2 i)

private def rationalTupleEval {t : ℕ} (a : Fin t → ℕ) :
    (Fin t →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun i ↦ (a i : ℚ)

private lemma freimanRelationVector_mem_ker_iff {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) :
    freimanRelationVector p ∈ LinearMap.ker (rationalTupleEval a) ↔
      freimanRelationHolds a p := by
  simp only [LinearMap.mem_ker, rationalTupleEval, freimanRelationVector, map_sub, map_sum,
    Finsupp.linearCombination_single, one_smul, sub_eq_zero, freimanRelationHolds]
  exact_mod_cast Iff.rfl

private def freimanRelationSpace {s t : ℕ} (a : Fin t → ℕ) :
    Submodule ℚ (Fin t →₀ ℚ) :=
  Submodule.span ℚ (freimanRelationVector (s := s) ''
    {p : FreimanRelationIndex s t | freimanRelationHolds a p})

private lemma freimanRelation_iff_mem_space {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds a p ↔
      freimanRelationVector p ∈ freimanRelationSpace (s := s) a := by
  refine ⟨fun hp ↦ Submodule.subset_span ⟨p, hp, rfl⟩, ?_⟩
  intro hp
  rw [← freimanRelationVector_mem_ker_iff]
  refine Submodule.span_le.mpr ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact (freimanRelationVector_mem_ker_iff a q).mpr hq

private lemma finrank_freimanRelationSpace_le {s t : ℕ} (a : Fin t → ℕ) :
    Module.finrank ℚ (freimanRelationSpace (s := s) a) ≤ t := by
  simpa using (freimanRelationSpace (s := s) a).finrank_le

/-- The coefficient vectors of the relations satisfied by `a` span a space of dimension at most
`t`, so `t` of these relations span it. -/
private lemma exists_freimanRelationCode {s t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    ∃ code : Fin t → FreimanRelationIndex s t,
      Submodule.span ℚ (freimanRelationVector '' Set.range code) =
        freimanRelationSpace (s := s) a := by
  obtain ⟨basis, hmem, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (freimanRelationVector (s := s) '' {p | freimanRelationHolds a p})
  choose index _ hindex using hmem
  refine ⟨fun i ↦ if hi : i.val < _ then index ⟨i, hi⟩ else (fun _ ↦ ⟨0, ht⟩, fun _ ↦ ⟨0, ht⟩),
    Eq.trans (le_antisymm ?_ ?_) hspan⟩ <;> rw [Submodule.span_le]
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    dsimp only
    split
    · exact Submodule.subset_span ⟨_, (hindex _).symm⟩
    · simp [freimanRelationVector]
  · rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨index i,
      ⟨⟨i, i.2.trans_le (finrank_freimanRelationSpace_le (s := s) a)⟩, ?_⟩, hindex i⟩
    simp

private def freimanRelationCodes {s t : ℕ} (a : Fin t → ℕ) :
    Finset (Fin t → FreimanRelationIndex s t) :=
  univ.filter fun code ↦
    Submodule.span ℚ (freimanRelationVector '' Set.range code) =
      freimanRelationSpace (s := s) a

private lemma freimanRelationCodes_nonempty {s t : ℕ} (ht : 0 < t)
    (a : Fin t → ℕ) : (freimanRelationCodes (s := s) a).Nonempty := by
  obtain ⟨code, hcode⟩ := exists_freimanRelationCode (s := s) ht a
  exact ⟨code, by simp [freimanRelationCodes, hcode]⟩

/-- The least tuple of `t` relations of order `s` satisfied by `a` whose coefficient vectors
span, over `ℚ`, the coefficient vectors of all relations of order `s` satisfied by `a`. Two
tuples satisfy the same relations of order `s` exactly when they have the same code. -/
@[no_expose] noncomputable def freimanRelationCode {s t : ℕ} (ht : 0 < t)
    (a : Fin t → ℕ) : Fin t → FreimanRelationIndex s t :=
  (freimanRelationCodes (s := s) a).min'
    (freimanRelationCodes_nonempty (s := s) ht a)

private lemma freimanRelationCode_span {s t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Submodule.span ℚ
      (freimanRelationVector '' Set.range (freimanRelationCode (s := s) ht a)) =
        freimanRelationSpace (s := s) a :=
  (mem_filter.mp (min'_mem _ (freimanRelationCodes_nonempty ht a))).2

lemma freimanRelationCode_eq_of_relations_iff {s t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ}
    (hrelations : ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    freimanRelationCode (s := s) ht a = freimanRelationCode ht b := by
  have hspace : freimanRelationSpace (s := s) a = freimanRelationSpace (s := s) b := by
    simp [freimanRelationSpace, hrelations]
  simp [freimanRelationCode, freimanRelationCodes, hspace]

/-- Two tuples with the same relation code satisfy the same relations. -/
lemma freimanRelations_iff_of_code_eq {s t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ}
    (hcode : freimanRelationCode (s := s) ht a = freimanRelationCode ht b)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds a p ↔ freimanRelationHolds b p := by
  rw [freimanRelation_iff_mem_space, freimanRelation_iff_mem_space,
    ← freimanRelationCode_span ht a, ← freimanRelationCode_span ht b, hcode]

/-- The number `t^(2*s*t)` in Green's Lemma 11. -/
lemma card_freimanRelationCodes (s t : ℕ) :
    Fintype.card (Fin t → FreimanRelationIndex s t) = t ^ (2 * s * t) := by
  simp [FreimanRelationIndex]
  ring

/-! ### Restricted sumsets and popular representations -/

/-- The restricted sumset, in which the two summands must be distinct. -/
def restrictedSumset {G : Type*} [DecidableEq G] [Add G] (A : Finset G) : Finset G :=
  ((A ×ˢ A).filter fun (a, b) ↦ a ≠ b).image fun (a, b) ↦ a + b

private lemma restrictedSumset_eq_image_offDiag {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) :
    restrictedSumset A = A.offDiag.image fun (a, b) ↦ a + b := by
  ext x
  simp [restrictedSumset, and_assoc]

lemma restrictedSumset_subset_add {G : Type*} [DecidableEq G] [Add G] (A : Finset G) :
    restrictedSumset A ⊆ A + A := by
  rw [restrictedSumset, image_subset_iff]
  rintro ⟨a, b⟩ hp
  rw [mem_filter, mem_product] at hp
  obtain ⟨⟨ha, hb⟩, -⟩ := hp
  exact add_mem_add ha hb

lemma card_restrictedSumset_le_card_add {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) :
    #(restrictedSumset A) ≤ #(A + A) :=
  card_le_card (restrictedSumset_subset_add A)

lemma card_sub_one_le_card_restrictedSumset {G : Type*} [DecidableEq G]
    [AddLeftCancelSemigroup G] {A : Finset G} (hA : A.Nonempty) :
    #A - 1 ≤ #(restrictedSumset A) := by
  obtain ⟨a, ha⟩ := hA
  rw [← card_erase_of_mem ha, ← card_image_of_injective (A.erase a) (add_right_injective a)]
  apply card_le_card
  rw [restrictedSumset_eq_image_offDiag, image_subset_iff]
  intro b hb
  exact mem_image.mpr
    ⟨(a, b), mem_offDiag.mpr ⟨ha, mem_of_mem_erase hb, (ne_of_mem_erase hb).symm⟩, rfl⟩

/-- The ordered representations of `x` as a sum of two distinct elements of `A`. -/
private def restrictedRepresentationPairs {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) (x : G) : Finset (G × G) :=
  A.offDiag.filter fun (a, b) ↦ a + b = x

private lemma mem_restrictedRepresentationPairs {G : Type*} [DecidableEq G] [Add G]
    {A : Finset G} {x a b : G} :
    (a, b) ∈ restrictedRepresentationPairs A x ↔ a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = x := by
  simp [restrictedRepresentationPairs, and_assoc]

private lemma mem_restrictedSumset_iff_representationPairs_nonempty
    {G : Type*} [DecidableEq G] [Add G] {A : Finset G} {x : G} :
    x ∈ restrictedSumset A ↔ (restrictedRepresentationPairs A x).Nonempty := by
  simp [restrictedSumset_eq_image_offDiag, Finset.Nonempty, restrictedRepresentationPairs]

/-- The representations `x = b + c` with `b < c` and `b, c ∈ A`. -/
private def increasingRestrictedRepresentationPairs (A : Finset ℕ) (x : ℕ) :
    Finset (ℕ × ℕ) :=
  (restrictedRepresentationPairs A x).filter fun (b, c) ↦ b < c

private lemma mem_increasingRestrictedRepresentationPairs {A : Finset ℕ} {x b c : ℕ} :
    (b, c) ∈ increasingRestrictedRepresentationPairs A x ↔ b ∈ A ∧ c ∈ A ∧ b < c ∧ b + c = x := by
  rw [increasingRestrictedRepresentationPairs, mem_filter, mem_restrictedRepresentationPairs]
  grind

private lemma card_restrictedRepresentationPairs_le (A : Finset ℕ) (x : ℕ) :
    #(restrictedRepresentationPairs A x) ≤
      2 * #(increasingRestrictedRepresentationPairs A x) := by
  have hsub : restrictedRepresentationPairs A x ⊆ increasingRestrictedRepresentationPairs A x ∪
      (increasingRestrictedRepresentationPairs A x).image Prod.swap := by
    rintro ⟨b, c⟩ hp
    obtain ⟨hb, hc, hbc, hx⟩ := mem_restrictedRepresentationPairs.mp hp
    rw [mem_union, mem_image]
    obtain h | h := lt_or_gt_of_ne hbc
    · left
      exact mem_increasingRestrictedRepresentationPairs.mpr ⟨hb, hc, h, hx⟩
    · right
      exact ⟨(c, b), mem_increasingRestrictedRepresentationPairs.mpr ⟨hc, hb, h, by grind⟩, rfl⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [two_mul]
  exact Nat.add_le_add_left card_image_le _

private lemma half_le_card_increasing_of_popular {A : Finset ℕ} {x Q : ℕ}
    (hpopular : Q ≤ #(restrictedRepresentationPairs A x)) :
    Q / 2 ≤ #(increasingRestrictedRepresentationPairs A x) :=
  Nat.div_le_of_le_mul (hpopular.trans (card_restrictedRepresentationPairs_le A x))

private lemma mem_restrictedSumset_iff_increasing_nonempty {A : Finset ℕ} {x : ℕ} :
    x ∈ restrictedSumset A ↔ (increasingRestrictedRepresentationPairs A x).Nonempty := by
  rw [mem_restrictedSumset_iff_representationPairs_nonempty, ← card_pos, ← card_pos]
  grind [card_restrictedRepresentationPairs_le A x, increasingRestrictedRepresentationPairs,
    card_filter_le]

private def unpopularOrderedPairs (A : Finset ℕ) (Q : ℕ) : Finset (ℕ × ℕ) :=
  A.offDiag.filter fun (a, b) ↦ #(restrictedRepresentationPairs A (a + b)) < Q

private def unpopularNeighbors (A : Finset ℕ) (Q : ℕ) (a : ℕ) : Finset ℕ :=
  (A.erase a).filter fun b ↦ #(restrictedRepresentationPairs A (a + b)) < Q

private lemma card_unpopularOrderedPairs_le (A : Finset ℕ) (Q : ℕ) :
    #(unpopularOrderedPairs A Q) ≤ Q * #(restrictedSumset A) := by
  rw [restrictedSumset_eq_image_offDiag]
  refine (card_le_mul_card_image (f := fun ((a, b) : ℕ × ℕ) ↦ a + b) _ Q ?_).trans
    (Nat.mul_le_mul_left Q (card_le_card (image_subset_image (filter_subset _ _))))
  intro x hx
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.mp hx
  exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (mem_filter.mp hp).2.le

private lemma sum_card_unpopularNeighbors_eq (A : Finset ℕ) (Q : ℕ) :
    ∑ a ∈ A, #(unpopularNeighbors A Q a) = #(unpopularOrderedPairs A Q) := by
  rw [card_eq_sum_card_fiberwise (s := unpopularOrderedPairs A Q) (f := Prod.fst) (t := A)
    fun p hp ↦ (mem_offDiag.mp (mem_filter.mp hp).1).1]
  apply sum_congr rfl
  intro a ha
  rw [← card_image_of_injective _ (Prod.mk_right_injective a)]
  congr 1
  ext ⟨c, b⟩
  simp only [unpopularNeighbors, unpopularOrderedPairs, mem_image, mem_filter, mem_erase,
    mem_offDiag, Prod.mk.injEq]
  grind

private lemma exists_low_unpopular_degree {A : Finset ℕ} {t m Q : ℕ}
    (hA : #A = t) (hA0 : A.Nonempty) (hm : #(restrictedSumset A) ≤ m) :
    ∃ a ∈ A, t * #(unpopularNeighbors A Q a) ≤ Q * m := by
  apply exists_le_of_sum_le hA0
  rw [← mul_sum, sum_card_unpopularNeighbors_eq, sum_const_nat fun _ _ ↦ rfl, hA]
  exact Nat.mul_le_mul_left t
    ((card_unpopularOrderedPairs_le A Q).trans (Nat.mul_le_mul_left Q hm))

/-! ### A finite Bernoulli alteration for core decompositions -/

/-- The probability of the assignment `ω` when each index is selected independently with
probability `q`. -/
private def assignmentWeight {ι : Type*} [Fintype ι] (q : ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then q else 1 - q

private def selectedIndices {ι : Type*} [Fintype ι] (ω : ι → Bool) : Finset ι :=
  univ.filter fun i ↦ ω i

private lemma sum_assignmentWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) :
    ∑ ω : ι → Bool, assignmentWeight q ω = 1 := by
  unfold assignmentWeight
  rw [← Fintype.prod_sum (f := fun (_ : ι) (b : Bool) ↦ if b then q else 1 - q)]
  simp

private lemma sum_assignmentWeight_selectedIndicator {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ℝ) (i : ι) :
    ∑ ω : ι → Bool, assignmentWeight q ω * (if ω i then 1 else 0) = q := by
  unfold assignmentWeight
  conv_lhs =>
    enter [2, ω]
    rw [← Fintype.prod_ite_eq' i (fun j ↦ if ω j then 1 else 0), ← prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun j (b : Bool) ↦
    (if b then q else 1 - q) * if j = i then (if b then 1 else 0) else 1)]
  simp

private lemma sum_assignmentWeight_selectedCard {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ℝ) :
    ∑ ω : ι → Bool, assignmentWeight q ω * #(selectedIndices ω) = q * Fintype.card ι := by
  simp_rw [selectedIndices, natCast_card_filter, mul_sum]
  rw [sum_comm]
  simp_rw [sum_assignmentWeight_selectedIndicator]
  simp [mul_comm]

/-- The weight of an assignment on `κ ⊕ C` is the product of the weights of its two parts, so
summing over the part on `C` leaves the weight of the part on `κ`. -/
private lemma sum_assignmentWeight_comp_inl {κ C : Type*} [Fintype κ] [Fintype C]
    [DecidableEq κ] [DecidableEq C] (q : ℝ) (F : (κ → Bool) → ℝ) :
    ∑ ω : κ ⊕ C → Bool, assignmentWeight q ω * F (fun x ↦ ω (Sum.inl x)) =
      ∑ v : κ → Bool, assignmentWeight q v * F v := by
  have hweight (v : κ → Bool) (y : C → Bool) :
      assignmentWeight q ((Equiv.sumArrowEquivProdArrow κ C Bool).symm (v, y)) =
        assignmentWeight q v * assignmentWeight q y :=
    Fintype.prod_sum_type _
  rw [← (Equiv.sumArrowEquivProdArrow κ C Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [hweight, mul_right_comm, ← mul_sum, sum_assignmentWeight]

/-- For an injective `f : κ → ι`, the restriction along `f` of a random assignment on `ι` is a
random assignment on `κ`. -/
private lemma sum_assignmentWeight_marginal {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] [DecidableEq ι] (q : ℝ) (f : κ → ι)
    (hf : Function.Injective f) (F : (κ → Bool) → ℝ) :
    ∑ ω : ι → Bool, assignmentWeight q ω * F (ω ∘ f) =
      ∑ v : κ → Bool, assignmentWeight q v * F v := by
  classical
  let e : κ ⊕ ((Set.range f)ᶜ : Set ι) ≃ ι :=
    ((Equiv.ofInjective f hf).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range f))
  rw [← sum_assignmentWeight_comp_inl (C := ((Set.range f)ᶜ : Set ι)) q F,
    ← (e.arrowCongr (Equiv.refl Bool)).symm.sum_comp]
  congr with ω
  congr 1
  exact (e.prod_comp _).symm

/-- The two endpoints of the increasing representations of `x`, as elements of `A`. -/
private def increasingRepresentationEndpoint (A : Finset ℕ) (x : ℕ)
    (u : (increasingRestrictedRepresentationPairs A x) × Fin 2) : A :=
  if u.2 = 0 then
    ⟨u.1.1.1, (mem_increasingRestrictedRepresentationPairs.mp u.1.2).1⟩
  else
    ⟨u.1.1.2, (mem_increasingRestrictedRepresentationPairs.mp u.1.2).2.1⟩

private lemma increasingRepresentationEndpoint_injective (A : Finset ℕ) (x : ℕ) :
    Function.Injective (increasingRepresentationEndpoint A x) := by
  rintro ⟨⟨⟨p₁, p₂⟩, hp⟩, i⟩ ⟨⟨⟨q₁, q₂⟩, hq⟩, j⟩ h
  have hp' := mem_increasingRestrictedRepresentationPairs.mp hp
  have hq' := mem_increasingRestrictedRepresentationPairs.mp hq
  fin_cases i <;> fin_cases j <;> simp [increasingRepresentationEndpoint] at h ⊢ <;> grind

private abbrev pairAssignmentAvoids (v : Fin 2 → Bool) : Prop :=
  ¬(v 0 ∧ v 1)

private lemma sum_assignmentWeight_pairAssignmentAvoids (q : ℝ) :
    ∑ v : Fin 2 → Bool, assignmentWeight q v *
      (if pairAssignmentAvoids v then 1 else 0) = 1 - q ^ 2 := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [assignmentWeight, pairAssignmentAvoids, finTwoArrowEquiv, piFinTwoEquiv]
  ring

private def allPairAssignmentsAvoidIndicator {ρ : Type*} [Fintype ρ]
    (v : ρ × Fin 2 → Bool) : ℝ :=
  ∏ p : ρ, if pairAssignmentAvoids (fun i ↦ v (p, i)) then 1 else 0

private lemma sum_assignmentWeight_allPairAssignmentsAvoid {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] (q : ℝ) :
    ∑ v : ρ × Fin 2 → Bool, assignmentWeight q v * allPairAssignmentsAvoidIndicator v =
      (1 - q ^ 2) ^ Fintype.card ρ := by
  rw [← card_univ, ← prod_const, ← sum_assignmentWeight_pairAssignmentAvoids q,
    Fintype.prod_sum, ← (Equiv.curry ρ (Fin 2) Bool).symm.sum_comp]
  congr with g
  rw [assignmentWeight, Fintype.prod_prod_type, allPairAssignmentsAvoidIndicator,
    ← prod_mul_distrib]
  rfl

private def representationAvoidanceIndicator (A : Finset ℕ) (x : ℕ)
    (ω : A → Bool) : ℝ :=
  allPairAssignmentsAvoidIndicator fun u ↦
    ω (increasingRepresentationEndpoint A x u)

private lemma sum_assignmentWeight_representationAvoidanceIndicator
    (A : Finset ℕ) (x : ℕ) (q : ℝ) :
    ∑ ω : A → Bool, assignmentWeight q ω * representationAvoidanceIndicator A x ω =
      (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A x) := by
  rw [← Fintype.card_coe, ← sum_assignmentWeight_allPairAssignmentsAvoid]
  exact sum_assignmentWeight_marginal q _ (increasingRepresentationEndpoint_injective A x) _

private def selectedElements (A : Finset ℕ) (ω : A → Bool) : Finset ℕ :=
  (selectedIndices ω).image Subtype.val

private lemma card_selectedElements (A : Finset ℕ) (ω : A → Bool) :
    #(selectedElements A ω) = #(selectedIndices ω) :=
  card_image_of_injective _ Subtype.val_injective

private lemma selectedElements_subset (A : Finset ℕ) (ω : A → Bool) :
    selectedElements A ω ⊆ A :=
  image_subset_iff.mpr fun a _ ↦ a.2

private lemma mem_selectedElements {A : Finset ℕ} {ω : A → Bool} {a : ℕ} :
    a ∈ selectedElements A ω ↔ ∃ h : a ∈ A, ω ⟨a, h⟩ := by
  simp [selectedElements, selectedIndices]

private lemma mem_increasing_selectedElements_iff {A : Finset ℕ} {x : ℕ} {ω : A → Bool}
    {b c : ℕ} :
    (b, c) ∈ increasingRestrictedRepresentationPairs (selectedElements A ω) x ↔
      ∃ h : (b, c) ∈ increasingRestrictedRepresentationPairs A x,
        ω (increasingRepresentationEndpoint A x (⟨(b, c), h⟩, 0)) ∧
          ω (increasingRepresentationEndpoint A x (⟨(b, c), h⟩, 1)) := by
  simp only [mem_increasingRestrictedRepresentationPairs, mem_selectedElements,
    increasingRepresentationEndpoint]
  grind

private lemma representationAvoidanceIndicator_eq_boole
    (A : Finset ℕ) (x : ℕ) (ω : A → Bool) :
    representationAvoidanceIndicator A x ω =
      if x ∉ restrictedSumset (selectedElements A ω) then 1 else 0 := by
  rw [representationAvoidanceIndicator, allPairAssignmentsAvoidIndicator, Fintype.prod_boole]
  refine if_congr ?_ rfl rfl
  simp [mem_restrictedSumset_iff_increasing_nonempty, not_nonempty_iff_eq_empty,
    eq_empty_iff_forall_notMem, mem_increasing_selectedElements_iff]

private def missedTranslateElements (A : Finset ℕ) (a : ℕ)
    (ω : A → Bool) : Finset ℕ :=
  A.filter fun b ↦ a + b ∉ restrictedSumset (selectedElements A ω)

private lemma sum_assignmentWeight_missedTranslateCard (A : Finset ℕ)
    (a : ℕ) (q : ℝ) :
    ∑ ω : A → Bool, assignmentWeight q ω * #(missedTranslateElements A a ω) =
      ∑ b ∈ A, (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) := by
  simp_rw [missedTranslateElements, natCast_card_filter, mul_sum]
  rw [sum_comm]
  simp_rw [← representationAvoidanceIndicator_eq_boole,
    sum_assignmentWeight_representationAvoidanceIndicator]

private lemma pow_card_increasing_le {A : Finset ℕ} {a b : ℕ} (hb : b ∈ A) (Q : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) ≤
      (if b = a then 1 else 0) + (if b ∈ unpopularNeighbors A Q a then 1 else 0) +
        (1 - q ^ 2) ^ (Q / 2) := by
  have hbase0 : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hbase1 : 1 - q ^ 2 ≤ 1 := by nlinarith
  by_cases hpopular : Q ≤ #(restrictedRepresentationPairs A (a + b))
  · grind [pow_le_pow_of_le_one hbase0 hbase1 (half_le_card_increasing_of_popular hpopular),
      pow_nonneg hbase0 (Q / 2)]
  · grind [pow_le_one₀ (n := #(increasingRestrictedRepresentationPairs A (a + b))) hbase0 hbase1,
      pow_nonneg hbase0 (Q / 2), unpopularNeighbors]

private lemma sum_representationAvoidance_le {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (Q : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ b ∈ A, (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) ≤
      1 + #(unpopularNeighbors A Q a) + #A * (1 - q ^ 2) ^ (Q / 2) := by
  have hsub : unpopularNeighbors A Q a ⊆ A := (filter_subset _ _).trans (erase_subset _ _)
  refine (sum_le_sum fun b hb ↦ pow_card_increasing_le hb Q hq0 hq1).trans_eq ?_
  simp [sum_add_distrib, ha, inter_eq_right.mpr hsub]

private lemma assignmentWeight_pos {ι : Type*} [Fintype ι]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ω : ι → Bool) :
    0 < assignmentWeight q ω := by
  apply prod_pos
  intro i _
  split <;> linarith

private lemma exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {q B : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (F : (ι → Bool) → ℝ)
    (hsum : ∑ ω : ι → Bool, assignmentWeight q ω * F ω ≤ B) :
    ∃ ω, F ω ≤ B := by
  rw [← one_mul B, ← sum_assignmentWeight (ι := ι) q, sum_mul] at hsum
  obtain ⟨ω, -, hω⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨ω, le_of_mul_le_mul_left hω (assignmentWeight_pos hq0 hq1 ω)⟩

private lemma exists_sample_with_bounded_cost {A : Finset ℕ} {a : ℕ} (ha : a ∈ A)
    (Q : ℕ) {q R : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hR : 0 ≤ R) :
    ∃ ω : A → Bool,
      (#(selectedElements A ω) : ℝ) + R * #(missedTranslateElements A a ω) ≤
        q * #A + R * (1 + #(unpopularNeighbors A Q a) + #A * (1 - q ^ 2) ^ (Q / 2)) := by
  apply exists_le_of_weighted_sum_le hq0 hq1
  simp_rw [mul_add (assignmentWeight q _), sum_add_distrib, mul_left_comm _ R, ← mul_sum,
    card_selectedElements, sum_assignmentWeight_selectedCard,
    sum_assignmentWeight_missedTranslateCard, Fintype.card_coe]
  gcongr
  exact sum_representationAvoidance_le ha Q hq0.le hq1.le

private lemma missedTranslateElements_compl_image_subset (A : Finset ℕ) (a : ℕ)
    (ω : A → Bool) :
    (A \ missedTranslateElements A a ω).image (a + ·) ⊆
      restrictedSumset (selectedElements A ω) := by
  rw [image_subset_iff]
  intro b hb
  rw [missedTranslateElements, mem_sdiff, mem_filter] at hb
  grind

/-- Let `A` be a set of `t` natural numbers whose restricted sumset has at most `m` elements, and
let `0 < q < 1` and `R ≥ 0`. There are `a ∈ A` and `A₀, Z ⊆ A` such that `a + (A \ Z)` is
contained in the restricted sumset of `A₀` and
`|A₀| + R |Z| ≤ q t + R (1 + Q m / t + t (1 - q ^ 2) ^ (Q / 2))`. This is the combinatorial part of
Green's Proposition 15, before its numerical parameters are fixed. -/
lemma exists_core_decomposition {A : Finset ℕ} {t m : ℕ} (hA : #A = t)
    (hA0 : A.Nonempty) (hm : #(restrictedSumset A) ≤ m) (Q : ℕ)
    {q R : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hR : 0 ≤ R) :
    ∃ a A₀ Z, a ∈ A ∧ A₀ ⊆ A ∧ Z ⊆ A ∧
      (A \ Z).image (a + ·) ⊆ restrictedSumset A₀ ∧
      #A₀ + R * #Z ≤ q * t + R * (1 + Q * m / t + t * (1 - q ^ 2) ^ (Q / 2)) := by
  obtain ⟨a, ha, hdegree⟩ := exists_low_unpopular_degree hA hA0 hm (Q := Q)
  obtain ⟨ω, hω⟩ := exists_sample_with_bounded_cost ha Q hq0 hq1 hR
  refine ⟨a, selectedElements A ω, missedTranslateElements A a ω, ha,
    selectedElements_subset A ω, filter_subset _ _,
    missedTranslateElements_compl_image_subset A a ω, hω.trans ?_⟩
  have hunpopular : (#(unpopularNeighbors A Q a) : ℝ) ≤ Q * m / t := by
    rw [le_div_iff₀' (mod_cast hA0.card_pos.trans_eq hA)]
    exact_mod_cast hdegree
  rw [hA]
  gcongr

/-! ### Extension relation codes -/

/-- The position of an index of `Fin (l + d)` relative to the first `l` indices: `Sum.inl ()`
for one of the first `l` indices and `Sum.inr j` for the `j`-th of the last `d` indices. -/
abbrev ExtensionSlot (d : ℕ) := Unit ⊕ Fin d

/-- The positions of the four indices of a relation with two summands on each side. -/
abbrev ExtensionShape (d : ℕ) :=
  (Fin 2 → ExtensionSlot d) × (Fin 2 → ExtensionSlot d)

private def extensionSlot {l d : ℕ} (i : Fin (l + d)) : ExtensionSlot d :=
  match finSumFinEquiv.symm i with
  | Sum.inl _ => Sum.inl ()
  | Sum.inr j => Sum.inr j

private def extensionShape {l d : ℕ} (p : FreimanRelationIndex 2 (l + d)) :
    ExtensionShape d :=
  (extensionSlot ∘ p.1, extensionSlot ∘ p.2)

private def extensionBaseIndex {l d : ℕ} (i₀ : Fin l) (i : Fin (l + d)) : Fin l :=
  match finSumFinEquiv.symm i with
  | Sum.inl j => j
  | Sum.inr _ => i₀

private def extensionBaseWitness {l d : ℕ} (i₀ : Fin l)
    (p : FreimanRelationIndex 2 (l + d)) : FreimanRelationIndex 2 l :=
  (extensionBaseIndex i₀ ∘ p.1, extensionBaseIndex i₀ ∘ p.2)

private def extensionRelation {l d : ℕ} (shape : ExtensionShape d)
    (witness : FreimanRelationIndex 2 l) : FreimanRelationIndex 2 (l + d) :=
  (fun j ↦ match shape.1 j with
    | Sum.inl _ => finSumFinEquiv (Sum.inl (witness.1 j))
    | Sum.inr i => finSumFinEquiv (Sum.inr i),
   fun j ↦ match shape.2 j with
    | Sum.inl _ => finSumFinEquiv (Sum.inl (witness.2 j))
    | Sum.inr i => finSumFinEquiv (Sum.inr i))

private lemma extensionRelation_shape_witness {l d : ℕ} (i₀ : Fin l)
    (p : FreimanRelationIndex 2 (l + d)) :
    extensionRelation (extensionShape p) (extensionBaseWitness i₀ p) = p := by
  apply Prod.ext <;> funext j
  · obtain ⟨z, hz⟩ := finSumFinEquiv.surjective (p.1 j)
    cases z <;> simp [extensionRelation, extensionShape, extensionSlot, extensionBaseWitness,
      extensionBaseIndex, ← hz]
  · obtain ⟨z, hz⟩ := finSumFinEquiv.surjective (p.2 j)
    cases z <;> simp [extensionRelation, extensionShape, extensionSlot, extensionBaseWitness,
      extensionBaseIndex, ← hz]

private lemma extensionShape_extensionRelation {l d : ℕ} (shape : ExtensionShape d)
    (witness : FreimanRelationIndex 2 l) :
    extensionShape (extensionRelation shape witness) = shape := by
  apply Prod.ext <;> funext j
  · cases h : shape.1 j <;> simp [extensionShape, extensionRelation, extensionSlot, h]
  · cases h : shape.2 j <;> simp [extensionShape, extensionRelation, extensionSlot, h]

private noncomputable instance extensionWitnessLinearOrder (l : ℕ) :
    LinearOrder (FreimanRelationIndex 2 l) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

private noncomputable def extensionWitnesses {l d : ℕ} (a : Fin (l + d) → ℕ)
    (shape : ExtensionShape d) : Finset (FreimanRelationIndex 2 l) := by
  classical
  exact univ.filter fun witness ↦
    freimanRelationHolds a (extensionRelation shape witness)

/-- For each shape, the least relation on the first `l` indices whose extension by the shape is
a relation satisfied by `a`, if there is one. -/
@[no_expose] noncomputable def extensionCode {l d : ℕ} (a : Fin (l + d) → ℕ) :
    ExtensionShape d → Option (FreimanRelationIndex 2 l) :=
  fun shape ↦ if h : (extensionWitnesses a shape).Nonempty then
    some ((extensionWitnesses a shape).min' h) else none

private lemma mem_extensionWitnesses {l d : ℕ} {a : Fin (l + d) → ℕ}
    {shape : ExtensionShape d} {witness : FreimanRelationIndex 2 l} :
    witness ∈ extensionWitnesses a shape ↔
      freimanRelationHolds a (extensionRelation shape witness) := by
  simp [extensionWitnesses]

private lemma freimanRelationHolds_of_extensionCode_eq_some {l d : ℕ} {a : Fin (l + d) → ℕ}
    {shape : ExtensionShape d} {witness : FreimanRelationIndex 2 l}
    (hcode : extensionCode a shape = some witness) :
    freimanRelationHolds a (extensionRelation shape witness) := by
  unfold extensionCode at hcode
  split at hcode <;> cases hcode
  exact mem_extensionWitnesses.mp (min'_mem _ _)

private lemma exists_extensionCode_eq_some {l d : ℕ} (i₀ : Fin l) {a : Fin (l + d) → ℕ}
    {p : FreimanRelationIndex 2 (l + d)} (hp : freimanRelationHolds a p) :
    ∃ witness, extensionCode a (extensionShape p) = some witness := by
  rw [← extensionRelation_shape_witness i₀ p, ← mem_extensionWitnesses] at hp
  exact ⟨_, dite_eq_left ⟨_, hp⟩⟩

lemma card_extensionCodeType (l d : ℕ) :
    Fintype.card (ExtensionShape d → Option (FreimanRelationIndex 2 l)) =
      (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
  simp [FreimanRelationIndex]
  ring

/-- The first `l` coordinates of a tuple of length `l + d`. -/
def extensionBaseTuple {l d : ℕ} (a : Fin (l + d) → ℕ) : Fin l → ℕ :=
  fun i ↦ a (finSumFinEquiv (Sum.inl i))

private lemma extensionSlot_add_base_eq {l d : ℕ} (i₀ : Fin l)
    (a : Fin (l + d) → ℕ) {i j : Fin (l + d)}
    (hslot : extensionSlot i = extensionSlot j) :
    a i + extensionBaseTuple a (extensionBaseIndex i₀ j) =
      a j + extensionBaseTuple a (extensionBaseIndex i₀ i) := by
  obtain ⟨si, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨sj, rfl⟩ := finSumFinEquiv.surjective j
  obtain i | i := si <;> obtain j | j := sj <;>
    simp_all [extensionSlot, extensionBaseIndex, extensionBaseTuple, add_comm]

private def extensionComparison {l d : ℕ} (i₀ : Fin l)
    (p q : FreimanRelationIndex 2 (l + d)) : FreimanRelationIndex 4 l :=
  (fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => extensionBaseIndex i₀ (p.1 k)
    | Sum.inr k => extensionBaseIndex i₀ (q.2 k),
   fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => extensionBaseIndex i₀ (p.2 k)
    | Sum.inr k => extensionBaseIndex i₀ (q.1 k))

/-- For two relations of the same shape, the comparison relation on the first `l` coordinates
holds exactly when the sum of one relation and the reverse of the other holds. -/
private lemma freimanRelationHolds_extensionComparison_iff {l d : ℕ}
    (i₀ : Fin l) (a : Fin (l + d) → ℕ) {p q : FreimanRelationIndex 2 (l + d)}
    (hshape : extensionShape p = extensionShape q) :
    freimanRelationHolds (extensionBaseTuple a) (extensionComparison i₀ p q) ↔
      a (p.1 0) + a (p.1 1) + (a (q.2 0) + a (q.2 1)) =
        a (p.2 0) + a (p.2 1) + (a (q.1 0) + a (q.1 1)) := by
  have hl (j : Fin 2) :=
    extensionSlot_add_base_eq i₀ a (congrFun (congrArg Prod.fst hshape) j)
  have hr (j : Fin 2) :=
    extensionSlot_add_base_eq i₀ a (congrFun (congrArg Prod.snd hshape) j)
  rw [freimanRelationHolds, ← (finSumFinEquiv (m := 2) (n := 2)).sum_comp,
    ← (finSumFinEquiv (m := 2) (n := 2)).sum_comp]
  simp only [extensionComparison, Equiv.symm_apply_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  grind

private lemma freimanRelationHolds_of_extensionCode_eq {l d : ℕ} (i₀ : Fin l)
    {a b : Fin (l + d) → ℕ} (hcode : extensionCode a = extensionCode b)
    (hbase : ∀ r : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) r →
        freimanRelationHolds (extensionBaseTuple b) r)
    {p : FreimanRelationIndex 2 (l + d)} (hp : freimanRelationHolds a p) :
    freimanRelationHolds b p := by
  obtain ⟨witness, hwitness⟩ := exists_extensionCode_eq_some i₀ hp
  have hqa := freimanRelationHolds_of_extensionCode_eq_some hwitness
  have hqb := freimanRelationHolds_of_extensionCode_eq_some (hcode ▸ hwitness)
  have hcomparison :=
    hbase (extensionComparison i₀ p (extensionRelation (extensionShape p) witness))
  rw [freimanRelationHolds_extensionComparison_iff i₀ a
      (extensionShape_extensionRelation _ witness).symm,
    freimanRelationHolds_extensionComparison_iff i₀ b
      (extensionShape_extensionRelation _ witness).symm] at hcomparison
  simp only [freimanRelationHolds, Fin.sum_univ_two] at hp hqa hqb ⊢
  grind

/-- Two tuples of length `l + d` with the same extension code, whose first `l` coordinates
satisfy the same relations with four summands, satisfy the same relations with two summands. -/
lemma freimanRelations_iff_of_extensionCode_eq {l d : ℕ} (i₀ : Fin l)
    {a b : Fin (l + d) → ℕ} (hcode : extensionCode a = extensionCode b)
    (hbase : ∀ p : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) p ↔
        freimanRelationHolds (extensionBaseTuple b) p)
    (p : FreimanRelationIndex 2 (l + d)) :
    freimanRelationHolds a p ↔ freimanRelationHolds b p :=
  ⟨freimanRelationHolds_of_extensionCode_eq i₀ hcode fun r ↦ (hbase r).mp,
    freimanRelationHolds_of_extensionCode_eq i₀ hcode.symm fun r ↦ (hbase r).mpr⟩

/-- If `f` is determined on `S` by `g`, then `f` takes at most as many values on `S` as the
codomain of `g` has elements. -/
lemma card_image_le_fintype_of_eq_imp_eq {α β γ : Type*}
    [DecidableEq β] [Fintype γ] (S : Finset α) (f : α → β) (g : α → γ)
    (hfactor : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) :
    #(S.image f) ≤ Fintype.card γ := by
  choose pick hpick hf using fun z : S.image f ↦ mem_image.mp z.2
  rw [← Fintype.card_coe]
  apply Fintype.card_le_of_injective fun z ↦ g (pick z)
  intro z w hzw
  rw [Subtype.ext_iff, ← hf z, ← hf w]
  exact hfactor _ (hpick z) _ (hpick w) hzw

/-- The tuple whose `i`-th coordinate is the sum of the two coordinates of `a` indexed by
`representation i`. -/
def pairSumTuple {l u : ℕ} (a : Fin l → ℕ)
    (representation : Fin u → Fin l × Fin l) : Fin u → ℕ :=
  fun i ↦ a (representation i).1 + a (representation i).2

private def pairSumRelation {l u : ℕ} (representation : Fin u → Fin l × Fin l)
    (p : FreimanRelationIndex 4 u) : FreimanRelationIndex 8 l :=
  (fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => (representation (p.1 k)).1
    | Sum.inr k => (representation (p.1 k)).2,
   fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => (representation (p.2 k)).1
    | Sum.inr k => (representation (p.2 k)).2)

private lemma pairSumTuple_relation_iff {l u : ℕ} (a : Fin l → ℕ)
    (representation : Fin u → Fin l × Fin l) (p : FreimanRelationIndex 4 u) :
    freimanRelationHolds (pairSumTuple a representation) p ↔
      freimanRelationHolds a (pairSumRelation representation p) := by
  rw [freimanRelationHolds, freimanRelationHolds,
    ← (finSumFinEquiv (m := 4) (n := 4)).sum_comp,
    ← (finSumFinEquiv (m := 4) (n := 4)).sum_comp]
  simp [pairSumTuple, pairSumRelation, sum_add_distrib, Fintype.sum_sum_type]

lemma pairSumTuple_relations_iff {l u : ℕ} {a b : Fin l → ℕ}
    (hcore : ∀ p : FreimanRelationIndex 8 l,
      freimanRelationHolds a p ↔ freimanRelationHolds b p)
    (representation : Fin u → Fin l × Fin l) (p : FreimanRelationIndex 4 u) :
    freimanRelationHolds (pairSumTuple a representation) p ↔
      freimanRelationHolds (pairSumTuple b representation) p := by
  rw [pairSumTuple_relation_iff, pairSumTuple_relation_iff]
  exact hcore (pairSumRelation representation p)

private noncomputable def chosenRestrictedRepresentation (A : Finset ℕ) {x : ℕ}
    (hx : x ∈ restrictedSumset A) : ℕ × ℕ :=
  Classical.choose (mem_restrictedSumset_iff_representationPairs_nonempty.mp hx)

private lemma chosenRestrictedRepresentation_mem (A : Finset ℕ) {x : ℕ}
    (hx : x ∈ restrictedSumset A) :
    chosenRestrictedRepresentation A hx ∈ restrictedRepresentationPairs A x :=
  Classical.choose_spec (mem_restrictedSumset_iff_representationPairs_nonempty.mp hx)

/-- For `B` contained in the restricted sumset of `A`, a choice, for each element of `B`, of two
distinct elements of `A` that sum to it. Elements are named by their positions in the increasing
enumerations of `A` and `B`. -/
@[no_expose] noncomputable def restrictedSumRepresentation {l u : ℕ}
    (A B : Finset ℕ) (hA : #A = l) (hB : #B = u)
    (hBA : B ⊆ restrictedSumset A) : Fin u → Fin l × Fin l :=
  fun i ↦
    let p := chosenRestrictedRepresentation A (hBA ((B.orderIsoOfFin hB i).2))
    ((A.orderIsoOfFin hA).symm
      ⟨p.1, (mem_restrictedRepresentationPairs.mp
        (chosenRestrictedRepresentation_mem A (hBA ((B.orderIsoOfFin hB i).2)))).1⟩,
     (A.orderIsoOfFin hA).symm
      ⟨p.2, (mem_restrictedRepresentationPairs.mp
        (chosenRestrictedRepresentation_mem A (hBA ((B.orderIsoOfFin hB i).2)))).2.1⟩)

lemma restrictedSumRepresentation_ne {l u : ℕ} {A B : Finset ℕ} (hA : #A = l) (hB : #B = u)
    (hBA : B ⊆ restrictedSumset A) (i : Fin u) :
    (restrictedSumRepresentation A B hA hB hBA i).1 ≠
      (restrictedSumRepresentation A B hA hB hBA i).2 := by
  obtain ⟨-, -, hne, -⟩ := mem_restrictedRepresentationPairs.mp
    (chosenRestrictedRepresentation_mem A (hBA (B.orderIsoOfFin hB i).2))
  intro heq
  have hvalues := congrArg (fun j ↦ (A.orderIsoOfFin hA j).1) heq
  simp only [restrictedSumRepresentation, OrderIso.apply_symm_apply] at hvalues
  exact hne hvalues

lemma pairSumTuple_restrictedSumRepresentation {l u : ℕ} {A B : Finset ℕ} (hA : #A = l)
    (hB : #B = u) (hBA : B ⊆ restrictedSumset A) :
    pairSumTuple (fun i ↦ (A.orderIsoOfFin hA i).1)
        (restrictedSumRepresentation A B hA hB hBA) =
      fun i ↦ (B.orderIsoOfFin hB i).1 := by
  funext i
  obtain ⟨-, -, -, hsum⟩ := mem_restrictedRepresentationPairs.mp
    (chosenRestrictedRepresentation_mem A (hBA (B.orderIsoOfFin hB i).2))
  simp only [pairSumTuple, restrictedSumRepresentation, OrderIso.apply_symm_apply]
  exact hsum

lemma injective_of_four_relations_iff {u : ℕ} {a b : Fin u → ℕ}
    (ha : Function.Injective a)
    (hrelations : ∀ p : FreimanRelationIndex 4 u,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    Function.Injective b := by
  intro i j hij
  have hp := (hrelations (fun _ ↦ i, fun _ ↦ j)).mpr (by simp [freimanRelationHolds, hij])
  simp only [freimanRelationHolds, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hp
  apply ha
  grind

/-- The set of coordinates of `pairSumTuple b representation`. -/
def pairSumRange {l u : ℕ} (b : Fin l → ℕ)
    (representation : Fin u → Fin l × Fin l) : Finset ℕ :=
  univ.image (pairSumTuple b representation)

lemma pairSumRange_subset_restrictedSumset {l u : ℕ} {b : Fin l → ℕ}
    (hb : Function.Injective b) {representation : Fin u → Fin l × Fin l}
    (hne : ∀ i, (representation i).1 ≠ (representation i).2) :
    pairSumRange b representation ⊆ restrictedSumset (univ.image b) := by
  rw [pairSumRange, image_subset_iff, restrictedSumset_eq_image_offDiag]
  intro i _
  exact mem_image.mpr
    ⟨(b (representation i).1, b (representation i).2), by simp [hb.eq_iff, hne i], rfl⟩

/-- A quadruple `(i, j, k, l)` of indices in `Fin t`. It stands for the relation
`a i + a j = a k + a l` between the coordinates of a tuple `a`. -/
abbrev RelationIndex (t : ℕ) :=
  Fin t × Fin t × Fin t × Fin t

end

end CountingSetsWithSmallSumset
