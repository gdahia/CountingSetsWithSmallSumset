/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Basic.Real.Basic
import CountingSetsWithSmallSumset.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Average

/-!
# The core of a set with small restricted sumset

This file contains the combinatorial part of Proposition 15 of Green, *Counting sets with small
sumset, and the clique number of random Cayley graphs*. Let `A` be a set of `t` elements of a
commutative monoid with cancellation whose restricted sumset has at most `m` elements. There is
`a ∈ A` such that few sums `a + b` have fewer than `Q` representations as a sum of two distinct
elements of `A`. A random subset `A₀ ⊆ A`, drawn from `setBer(A, q)`, then contains both summands
of one representation of most of the sums `a + b`. The paper uses `Q / 3` disjoint representations
of each popular sum. Here the representations `b + c` with `b` before `c` in a fixed well-order
are used: they are pairwise disjoint and there are at least `Q / 2` of them.

## Main statements

* `exists_image_add_subset_restrictedSumset_card_add_mul_le`: a finite set `A` with small
  restricted sumset has an element `a` and subsets `A₀` and `Z` such that `a + (A \ Z)` lies in
  the restricted sumset of `A₀`, with a bound on `|A₀| + R |Z|`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Function MeasureTheory ProbabilityTheory unitInterval

noncomputable section

variable {G : Type*} [AddCancelCommMonoid G] [DecidableEq G]

/-! ### Popular representations -/

/-- The ordered representations of `x` as a sum of two distinct elements of `A`. -/
private def restrictedRepresentationPairs (A : Finset G) (x : G) : Finset (G × G) :=
  A.offDiag.filter fun (a, b) ↦ a + b = x

private lemma mem_restrictedRepresentationPairs {A : Finset G} {x a b : G} :
    (a, b) ∈ restrictedRepresentationPairs A x ↔ a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b = x := by
  simp [restrictedRepresentationPairs, and_assoc]

/-- The representations `x = b + c` with `b, c ∈ A` and `b` before `c` in a fixed well-order
of `G`. -/
private def increasingRestrictedRepresentationPairs (A : Finset G) (x : G) :
    Finset (G × G) := by
  classical
  exact (restrictedRepresentationPairs A x).filter fun (b, c) ↦ WellOrderingRel b c

private lemma mem_increasingRestrictedRepresentationPairs {A : Finset G} {x b c : G} :
    (b, c) ∈ increasingRestrictedRepresentationPairs A x ↔
      b ∈ A ∧ c ∈ A ∧ WellOrderingRel b c ∧ b + c = x := by
  simp only [increasingRestrictedRepresentationPairs, mem_filter,
    mem_restrictedRepresentationPairs]
  grind [ne_of_irrefl (r := WellOrderingRel) (x := b) (y := c)]

private lemma card_restrictedRepresentationPairs_le (A : Finset G) (x : G) :
    #(restrictedRepresentationPairs A x) ≤
      2 * #(increasingRestrictedRepresentationPairs A x) := by
  have hsub : restrictedRepresentationPairs A x ⊆ increasingRestrictedRepresentationPairs A x ∪
      (increasingRestrictedRepresentationPairs A x).image Prod.swap := by
    rintro ⟨b, c⟩ hp
    obtain ⟨hb, hc, hbc, hx⟩ := mem_restrictedRepresentationPairs.mp hp
    rw [mem_union, mem_image]
    obtain h | h | h := trichotomous_of WellOrderingRel b c
    · left
      exact mem_increasingRestrictedRepresentationPairs.mpr ⟨hb, hc, h, hx⟩
    · exact (hbc h).elim
    · right
      exact ⟨(c, b), mem_increasingRestrictedRepresentationPairs.mpr
        ⟨hc, hb, h, by rw [add_comm, hx]⟩, rfl⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [two_mul]
  exact Nat.add_le_add_left card_image_le _

private lemma div_two_le_card_increasingRestrictedRepresentationPairs {A : Finset G} {x : G}
    {Q : ℕ} (hpopular : Q ≤ #(restrictedRepresentationPairs A x)) :
    Q / 2 ≤ #(increasingRestrictedRepresentationPairs A x) :=
  Nat.div_le_of_le_mul (hpopular.trans (card_restrictedRepresentationPairs_le A x))

/-- For `S ⊆ A`, a sum lies in the restricted sumset of `S` exactly when it has an increasing
representation in `A` with both summands in `S`. -/
private lemma mem_restrictedSumset_iff_exists_increasing {A S : Finset G} (hS : S ⊆ A) {x : G} :
    x ∈ restrictedSumset S ↔
      ∃ b c, (b, c) ∈ increasingRestrictedRepresentationPairs A x ∧ b ∈ S ∧ c ∈ S := by
  simp only [mem_restrictedSumset, mem_increasingRestrictedRepresentationPairs]
  constructor
  · rintro ⟨b, hb, c, hc, hbc, rfl⟩
    obtain h | h | h := trichotomous_of WellOrderingRel b c
    · exact ⟨b, c, ⟨hS hb, hS hc, h, rfl⟩, hb, hc⟩
    · exact (hbc h).elim
    · exact ⟨c, b, ⟨hS hc, hS hb, h, add_comm c b⟩, hc, hb⟩
  · rintro ⟨b, c, ⟨-, -, h, rfl⟩, hb, hc⟩
    exact ⟨b, hb, c, hc, ne_of_irrefl h, rfl⟩

private def unpopularOrderedPairs (A : Finset G) (Q : ℕ) : Finset (G × G) :=
  A.offDiag.filter fun (a, b) ↦ #(restrictedRepresentationPairs A (a + b)) < Q

private def unpopularNeighbors (A : Finset G) (Q : ℕ) (a : G) : Finset G :=
  (A.erase a).filter fun b ↦ #(restrictedRepresentationPairs A (a + b)) < Q

private lemma unpopularNeighbors_subset (A : Finset G) (Q : ℕ) (a : G) :
    unpopularNeighbors A Q a ⊆ A :=
  (filter_subset _ _).trans (erase_subset _ _)

private lemma card_unpopularOrderedPairs_le (A : Finset G) (Q : ℕ) :
    #(unpopularOrderedPairs A Q) ≤ Q * #(restrictedSumset A) := by
  rw [restrictedSumset_eq_image_offDiag]
  refine (card_le_mul_card_image (f := fun ((a, b) : G × G) ↦ a + b) _ Q ?_).trans
    (Nat.mul_le_mul_left Q (card_le_card (image_subset_image (filter_subset _ _))))
  intro x hx
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.mp hx
  obtain ⟨-, hQ⟩ := mem_filter.mp hp
  exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans hQ.le

private lemma sum_card_unpopularNeighbors_eq (A : Finset G) (Q : ℕ) :
    ∑ a ∈ A, #(unpopularNeighbors A Q a) = #(unpopularOrderedPairs A Q) := by
  rw [card_eq_sum_card_fiberwise (s := unpopularOrderedPairs A Q) (f := Prod.fst) (t := A)
    fun _ hp ↦ by simp_all [unpopularOrderedPairs]]
  congr! 1 with a ha
  rw [← card_image_of_injective _ (Prod.mk_right_injective a)]
  congr 1
  ext ⟨c, b⟩
  simp only [unpopularNeighbors, unpopularOrderedPairs, mem_image, mem_filter, mem_erase,
    mem_offDiag, Prod.mk.injEq]
  grind

private lemma exists_mul_card_unpopularNeighbors_le {A : Finset G} {t m Q : ℕ}
    (hA : #A = t) (hA0 : A.Nonempty) (hm : #(restrictedSumset A) ≤ m) :
    ∃ a ∈ A, t * #(unpopularNeighbors A Q a) ≤ Q * m := by
  apply exists_le_of_sum_le hA0
  rw [← mul_sum, sum_card_unpopularNeighbors_eq, sum_const_nat fun _ _ ↦ rfl, hA]
  exact Nat.mul_le_mul_left t
    ((card_unpopularOrderedPairs_le A Q).trans (Nat.mul_le_mul_left Q hm))

/-! ### The random subset -/

/-- The representations `b + c` of `x` in `increasingRestrictedRepresentationPairs`, as pairs of
elements of `A`. -/
private def representationBlock (A : Finset G) (x : G)
    (r : increasingRestrictedRepresentationPairs A x) : Finset A :=
  {⟨r.1.1, (mem_increasingRestrictedRepresentationPairs.mp r.2).1⟩,
    ⟨r.1.2, (mem_increasingRestrictedRepresentationPairs.mp r.2).2.1⟩}

private lemma card_representationBlock (A : Finset G) (x : G)
    (r : increasingRestrictedRepresentationPairs A x) : #(representationBlock A x r) = 2 := by
  obtain ⟨-, -, hr, -⟩ := mem_increasingRestrictedRepresentationPairs.mp r.2
  exact card_pair fun h ↦ ne_of_irrefl hr (congr_arg Subtype.val h)

private lemma pairwise_disjoint_representationBlock (A : Finset G) (x : G) :
    Pairwise (Disjoint on representationBlock A x) := by
  rintro ⟨⟨b, c⟩, hr⟩ ⟨⟨b', c'⟩, hr'⟩ hne
  obtain ⟨-, -, hbc, hx⟩ := mem_increasingRestrictedRepresentationPairs.mp hr
  obtain ⟨-, -, hbc', hx'⟩ := mem_increasingRestrictedRepresentationPairs.mp hr'
  have hcancel (u v w : G) (huv : u + v = x) (huw : u + w = x) : v = w :=
    add_left_cancel (huv.trans huw.symm)
  simp only [Function.onFun, representationBlock, disjoint_insert_left, disjoint_insert_right,
    disjoint_singleton, mem_insert, mem_singleton, ne_eq, Subtype.ext_iff]
  grind [add_comm, asymm (r := WellOrderingRel) hbc]

/-- The elements of `A` selected by `S : Set A`. -/
private def selectedElements (A : Finset G) (S : Set A) : Finset G := by
  classical
  exact (univ.filter (· ∈ S)).map (Function.Embedding.subtype _)

omit [AddCancelCommMonoid G] [DecidableEq G] in
private lemma mem_selectedElements {A : Finset G} {S : Set A} {a : G} :
    a ∈ selectedElements A S ↔ ∃ h : a ∈ A, ⟨a, h⟩ ∈ S := by
  simp [selectedElements]

omit [AddCancelCommMonoid G] [DecidableEq G] in
private lemma selectedElements_subset (A : Finset G) (S : Set A) : selectedElements A S ⊆ A :=
  fun _ ha ↦ (mem_selectedElements.mp ha).1

omit [AddCancelCommMonoid G] [DecidableEq G] in
private lemma card_selectedElements (A : Finset G) (S : Set A) :
    #(selectedElements A S) = S.ncard := by
  classical
  rw [selectedElements, card_map, ← Set.ncard_coe_finset]
  congr
  ext
  simp

private def missedTranslateElements (A : Finset G) (a : G) (S : Set A) : Finset G :=
  A.filter fun b ↦ a + b ∉ restrictedSumset (selectedElements A S)

omit [AddCancelCommMonoid G] [DecidableEq G] in
private lemma integral_card_selectedElements (A : Finset G) (p : I) :
    ∫ S, (#(selectedElements A S) : ℝ) ∂setBer((Set.univ : Set A), p) = p * #A := by
  have h := integral_ncard_inter_setBernoulli (u := Set.univ) (p := p) (t := (univ : Finset A))
    (Set.subset_univ _)
  rw [coe_univ, card_univ, Fintype.card_coe] at h
  simp_rw [Set.inter_univ] at h
  simp_rw [card_selectedElements]
  exact h

private lemma setBernoulli_real_notMem_restrictedSumset (A : Finset G) (x : G) (p : I) :
    setBer((Set.univ : Set A), p).real {S | x ∉ restrictedSumset (selectedElements A S)} =
      (1 - (p : ℝ) ^ 2) ^ #(increasingRestrictedRepresentationPairs A x) := by
  have : {S : Set A | x ∉ restrictedSumset (selectedElements A S)} =
      {S | ∀ r, ¬↑(representationBlock A x r) ⊆ S} := by
    ext S
    simp only [mem_restrictedSumset_iff_exists_increasing (selectedElements_subset A S),
      mem_selectedElements, representationBlock, coe_insert, coe_singleton,
      Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_ofPred_eq, Subtype.forall,
      Prod.forall]
    grind [mem_increasingRestrictedRepresentationPairs]
  rw [this, setBernoulli_real_setOf_forall_not_subset (pairwise_disjoint_representationBlock A x)
    fun _ ↦ by simp]
  simp [card_representationBlock]

private lemma integral_card_missedTranslateElements (A : Finset G) (a : G) (p : I) :
    ∫ S, (#(missedTranslateElements A a S) : ℝ) ∂setBer((Set.univ : Set A), p) =
      ∑ b ∈ A, (1 - (p : ℝ) ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) := by
  simp_rw [missedTranslateElements, natCast_card_filter]
  rw [integral_finsetSum _ fun _ _ ↦ .of_finite]
  congr with b
  rw [← setBernoulli_real_notMem_restrictedSumset, ← integral_indicator_one .of_discrete]
  congr with S
  simp [Set.indicator_apply]

private lemma one_sub_sq_pow_card_increasingRestrictedRepresentationPairs_le {A : Finset G}
    {a b : G} (hb : b ∈ A) (Q : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) ≤
      (if b = a then 1 else 0) + (if b ∈ unpopularNeighbors A Q a then 1 else 0) +
        (1 - q ^ 2) ^ (Q / 2) := by
  have hbase0 : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hbase1 : 1 - q ^ 2 ≤ 1 := by nlinarith
  by_cases hpopular : Q ≤ #(restrictedRepresentationPairs A (a + b))
  · grind [pow_le_pow_of_le_one hbase0 hbase1
        (div_two_le_card_increasingRestrictedRepresentationPairs hpopular),
      pow_nonneg hbase0 (Q / 2)]
  · grind [pow_le_one₀ (n := #(increasingRestrictedRepresentationPairs A (a + b))) hbase0 hbase1,
      pow_nonneg hbase0 (Q / 2), unpopularNeighbors]

private lemma sum_one_sub_sq_pow_card_increasingRestrictedRepresentationPairs_le {A : Finset G}
    {a : G} (ha : a ∈ A) (Q : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ b ∈ A, (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) ≤
      1 + #(unpopularNeighbors A Q a) + #A * (1 - q ^ 2) ^ (Q / 2) := by
  apply (sum_le_sum fun b hb ↦
    one_sub_sq_pow_card_increasingRestrictedRepresentationPairs_le hb Q hq0 hq1).trans_eq
  simp [sum_add_distrib, ha, inter_eq_right.mpr (unpopularNeighbors_subset A Q a)]

private lemma exists_card_selectedElements_add_mul_card_missedTranslateElements_le {A : Finset G}
    {a : G} (ha : a ∈ A) (Q : ℕ) {q R : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hR : 0 ≤ R) :
    ∃ S : Set A,
      (#(selectedElements A S) : ℝ) + R * #(missedTranslateElements A a S) ≤
        q * #A + R * (1 + #(unpopularNeighbors A Q a) + #A * (1 - q ^ 2) ^ (Q / 2)) := by
  obtain ⟨S, hS⟩ := exists_le_integral (μ := setBer((Set.univ : Set A), ⟨q, hq0, hq1⟩))
    (f := fun S ↦ (#(selectedElements A S) : ℝ) + R * #(missedTranslateElements A a S)) .of_finite
  refine ⟨S, hS.trans ?_⟩
  rw [integral_add .of_finite .of_finite, integral_const_mul, integral_card_selectedElements,
    integral_card_missedTranslateElements]
  gcongr
  exact sum_one_sub_sq_pow_card_increasingRestrictedRepresentationPairs_le ha Q hq0 hq1

private lemma missedTranslateElements_compl_image_subset (A : Finset G) (a : G) (S : Set A) :
    (A \ missedTranslateElements A a S).image (a + ·) ⊆
      restrictedSumset (selectedElements A S) := by
  rw [image_subset_iff]
  intro b hb
  rw [missedTranslateElements, mem_sdiff, mem_filter] at hb
  grind

/-- Let `A` be a set of `t` elements whose restricted sumset has at most `m` elements, and let
`0 < q < 1` and `R ≥ 0`. There are `a ∈ A` and `A₀, Z ⊆ A` such that `a + (A \ Z)` is contained in
the restricted sumset of `A₀` and
`|A₀| + R |Z| ≤ q t + R (1 + Q m / t + t (1 - q ^ 2) ^ (Q / 2))`. This is the combinatorial part of
Green's Proposition 15, before its numerical parameters are fixed. -/
lemma exists_image_add_subset_restrictedSumset_card_add_mul_le {A : Finset G} {t m : ℕ}
    (hA : #A = t) (hA0 : A.Nonempty) (hm : #(restrictedSumset A) ≤ m) (Q : ℕ) {q R : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hR : 0 ≤ R) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ Z ⊆ A, (A \ Z).image (a + ·) ⊆ restrictedSumset A₀ ∧
      #A₀ + R * #Z ≤ q * t + R * (1 + Q * m / t + t * (1 - q ^ 2) ^ (Q / 2)) := by
  obtain ⟨a, ha, hdegree⟩ := exists_mul_card_unpopularNeighbors_le hA hA0 hm (Q := Q)
  obtain ⟨S, hS⟩ :=
    exists_card_selectedElements_add_mul_card_missedTranslateElements_le ha Q hq0.le hq1.le hR
  refine ⟨a, ha, selectedElements A S, selectedElements_subset A S,
    missedTranslateElements A a S, filter_subset _ _,
    missedTranslateElements_compl_image_subset A a S, hS.trans ?_⟩
  have hunpopular : (#(unpopularNeighbors A Q a) : ℝ) ≤ Q * m / t := by
    rw [le_div_iff₀' (mod_cast hA0.card_pos.trans_eq hA)]
    exact_mod_cast hdegree
  rw [hA]
  gcongr

end

end CountingSetsWithSmallSumset
