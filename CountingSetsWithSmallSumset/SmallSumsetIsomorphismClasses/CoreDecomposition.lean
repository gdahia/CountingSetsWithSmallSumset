/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The core of a set with small restricted sumset

This file contains the combinatorial part of Proposition 15 of Green, *Counting sets with small
sumset, and the clique number of random Cayley graphs*. Let `A` be a set of `t` elements of a
commutative monoid with cancellation whose restricted sumset has at most `m` elements. There is
`a ∈ A` such that few sums `a + b` have fewer than `Q` representations as a sum of two distinct
elements of `A`. A random subset `A₀ ⊆ A`, which contains every element independently with
probability `q`, then contains both summands of one representation of most of the sums `a + b`.
The paper uses `Q / 3` disjoint representations of each popular sum. Here the representations
`b + c` with `b` before `c` in a fixed well-order are used: they are pairwise disjoint and there
are at least `Q / 2` of them. The expectation is a finite sum over the functions from `A` to
`Bool` with product weights.

## Main statements

* `exists_image_add_subset_restrictedSumset_card_add_mul_le`: a finite set `A` with small
  restricted sumset has an element `a` and subsets `A₀` and `Z` such that `a + (A \ Z)` lies in
  the restricted sumset of `A₀`, with a bound on `|A₀| + R |Z|`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

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
  have := ne_of_irrefl (r := WellOrderingRel) (x := b) (y := c)
  grind

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

private lemma half_le_card_increasing_of_popular {A : Finset G} {x : G} {Q : ℕ}
    (hpopular : Q ≤ #(restrictedRepresentationPairs A x)) :
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

private lemma card_unpopularOrderedPairs_le (A : Finset G) (Q : ℕ) :
    #(unpopularOrderedPairs A Q) ≤ Q * #(restrictedSumset A) := by
  rw [restrictedSumset_eq_image_offDiag]
  refine (card_le_mul_card_image (f := fun ((a, b) : G × G) ↦ a + b) _ Q ?_).trans
    (Nat.mul_le_mul_left Q (card_le_card (image_subset_image (filter_subset _ _))))
  intro x hx
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.mp hx
  obtain ⟨-, hQ⟩ := mem_filter.mp hp
  exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans hQ.le

private lemma fst_mem_of_mem_unpopularOrderedPairs {A : Finset G} {Q : ℕ} {a b : G}
    (h : (a, b) ∈ unpopularOrderedPairs A Q) : a ∈ A := by
  obtain ⟨hab, -⟩ := mem_filter.mp h
  obtain ⟨ha, -⟩ := mem_offDiag.mp hab
  exact ha

private lemma sum_card_unpopularNeighbors_eq (A : Finset G) (Q : ℕ) :
    ∑ a ∈ A, #(unpopularNeighbors A Q a) = #(unpopularOrderedPairs A Q) := by
  rw [card_eq_sum_card_fiberwise (s := unpopularOrderedPairs A Q) (f := Prod.fst) (t := A)
    fun _ hp ↦ fst_mem_of_mem_unpopularOrderedPairs hp]
  apply sum_congr rfl
  intro a ha
  rw [← card_image_of_injective _ (Prod.mk_right_injective a)]
  congr 1
  ext ⟨c, b⟩
  simp only [unpopularNeighbors, unpopularOrderedPairs, mem_image, mem_filter, mem_erase,
    mem_offDiag, Prod.mk.injEq]
  grind

private lemma exists_low_unpopular_degree {A : Finset G} {t m Q : ℕ}
    (hA : #A = t) (hA0 : A.Nonempty) (hm : #(restrictedSumset A) ≤ m) :
    ∃ a ∈ A, t * #(unpopularNeighbors A Q a) ≤ Q * m := by
  apply exists_le_of_sum_le hA0
  rw [← mul_sum, sum_card_unpopularNeighbors_eq, sum_const_nat fun _ _ ↦ rfl, hA]
  exact Nat.mul_le_mul_left t
    ((card_unpopularOrderedPairs_le A Q).trans (Nat.mul_le_mul_left Q hm))

/-! ### A finite Bernoulli alteration -/

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

private lemma left_mem_of_mem_increasingRestrictedRepresentationPairs {A : Finset G} {x b c : G}
    (h : (b, c) ∈ increasingRestrictedRepresentationPairs A x) : b ∈ A := by
  obtain ⟨hb, -⟩ := mem_increasingRestrictedRepresentationPairs.mp h
  exact hb

private lemma right_mem_of_mem_increasingRestrictedRepresentationPairs {A : Finset G} {x b c : G}
    (h : (b, c) ∈ increasingRestrictedRepresentationPairs A x) : c ∈ A := by
  obtain ⟨-, hc, -⟩ := mem_increasingRestrictedRepresentationPairs.mp h
  exact hc

/-- The two endpoints of the increasing representations of `x`, as elements of `A`. -/
private def increasingRepresentationEndpoint (A : Finset G) (x : G) :
    (increasingRestrictedRepresentationPairs A x) × Fin 2 → A
  | (⟨(b, c), h⟩, i) =>
    if i = 0 then ⟨b, left_mem_of_mem_increasingRestrictedRepresentationPairs h⟩
    else ⟨c, right_mem_of_mem_increasingRestrictedRepresentationPairs h⟩

private lemma increasingRepresentationEndpoint_injective (A : Finset G) (x : G) :
    Function.Injective (increasingRepresentationEndpoint A x) := by
  rintro ⟨⟨⟨p₁, p₂⟩, hp⟩, i⟩ ⟨⟨⟨q₁, q₂⟩, hq⟩, j⟩ h
  obtain ⟨-, -, hpr, hpx⟩ := mem_increasingRestrictedRepresentationPairs.mp hp
  obtain ⟨-, -, hqr, hqx⟩ := mem_increasingRestrictedRepresentationPairs.mp hq
  have hasymm := asymm (r := WellOrderingRel) hpr
  have hcancel (u v w : G) (huv : u + v = x) (huw : u + w = x) : v = w :=
    add_left_cancel (huv.trans huw.symm)
  fin_cases i <;> fin_cases j <;> simp [increasingRepresentationEndpoint] at h ⊢ <;>
    grind [add_comm]

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

private def representationAvoidanceIndicator (A : Finset G) (x : G)
    (ω : A → Bool) : ℝ :=
  allPairAssignmentsAvoidIndicator fun u ↦
    ω (increasingRepresentationEndpoint A x u)

private lemma sum_assignmentWeight_representationAvoidanceIndicator
    (A : Finset G) (x : G) (q : ℝ) :
    ∑ ω : A → Bool, assignmentWeight q ω * representationAvoidanceIndicator A x ω =
      (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A x) := by
  rw [← Fintype.card_coe, ← sum_assignmentWeight_allPairAssignmentsAvoid]
  exact sum_assignmentWeight_marginal q _ (increasingRepresentationEndpoint_injective A x) _

private def selectedElements (A : Finset G) (ω : A → Bool) : Finset G :=
  (selectedIndices ω).image Subtype.val

omit [AddCancelCommMonoid G] in
private lemma card_selectedElements (A : Finset G) (ω : A → Bool) :
    #(selectedElements A ω) = #(selectedIndices ω) :=
  card_image_of_injective _ Subtype.val_injective

omit [AddCancelCommMonoid G] in
private lemma selectedElements_subset (A : Finset G) (ω : A → Bool) :
    selectedElements A ω ⊆ A :=
  image_subset_iff.mpr fun a _ ↦ a.2

omit [AddCancelCommMonoid G] in
private lemma mem_selectedElements {A : Finset G} {ω : A → Bool} {a : G} :
    a ∈ selectedElements A ω ↔ ∃ h : a ∈ A, ω ⟨a, h⟩ := by
  simp [selectedElements, selectedIndices]

private lemma representationAvoidanceIndicator_eq_boole
    (A : Finset G) (x : G) (ω : A → Bool) :
    representationAvoidanceIndicator A x ω =
      if x ∉ restrictedSumset (selectedElements A ω) then 1 else 0 := by
  rw [representationAvoidanceIndicator, allPairAssignmentsAvoidIndicator, Fintype.prod_boole]
  refine if_congr ?_ rfl rfl
  simp only [mem_restrictedSumset_iff_exists_increasing (selectedElements_subset A ω),
    mem_selectedElements]
  simp [increasingRepresentationEndpoint]
  grind

private def missedTranslateElements (A : Finset G) (a : G)
    (ω : A → Bool) : Finset G :=
  A.filter fun b ↦ a + b ∉ restrictedSumset (selectedElements A ω)

private lemma sum_assignmentWeight_missedTranslateCard (A : Finset G)
    (a : G) (q : ℝ) :
    ∑ ω : A → Bool, assignmentWeight q ω * #(missedTranslateElements A a ω) =
      ∑ b ∈ A, (1 - q ^ 2) ^ #(increasingRestrictedRepresentationPairs A (a + b)) := by
  simp_rw [missedTranslateElements, natCast_card_filter, mul_sum]
  rw [sum_comm]
  simp_rw [← representationAvoidanceIndicator_eq_boole,
    sum_assignmentWeight_representationAvoidanceIndicator]

private lemma pow_card_increasing_le {A : Finset G} {a b : G} (hb : b ∈ A) (Q : ℕ) {q : ℝ}
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

private lemma sum_representationAvoidance_le {A : Finset G} {a : G}
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

private lemma exists_sample_with_bounded_cost {A : Finset G} {a : G} (ha : a ∈ A)
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

private lemma missedTranslateElements_compl_image_subset (A : Finset G) (a : G)
    (ω : A → Bool) :
    (A \ missedTranslateElements A a ω).image (a + ·) ⊆
      restrictedSumset (selectedElements A ω) := by
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
  obtain ⟨a, ha, hdegree⟩ := exists_low_unpopular_degree hA hA0 hm (Q := Q)
  obtain ⟨ω, hω⟩ := exists_sample_with_bounded_cost ha Q hq0 hq1 hR
  refine ⟨a, ha, selectedElements A ω, selectedElements_subset A ω,
    missedTranslateElements A a ω, filter_subset _ _,
    missedTranslateElements_compl_image_subset A a ω, hω.trans ?_⟩
  have hunpopular : (#(unpopularNeighbors A Q a) : ℝ) ≤ Q * m / t := by
    rw [le_div_iff₀' (mod_cast hA0.card_pos.trans_eq hA)]
    exact_mod_cast hdegree
  rw [hA]
  gcongr

end

end CountingSetsWithSmallSumset
