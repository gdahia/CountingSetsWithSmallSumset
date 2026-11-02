/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.MeasureTheory.MeasurableSpace.Constructions
public import CountingSetsWithSmallSumset.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Independence in the product of Bernoulli distributions on a set

This file complements `Mathlib.Probability.Distributions.SetBernoulli`. Under `setBer(u, p)`, the
events `i ∈ s` are independent, and each has probability `p` for `i ∈ u`. We deduce the probability
that the random set contains a given finite set, the probability that it contains none of a family
of pairwise disjoint finite sets, and the expected size of its intersection with a finite set.

## Main statements

* `ProbabilityTheory.iIndepFun_mem_setBernoulli`: the events `i ∈ s` are independent under
  `setBer(u, p)`.
* `ProbabilityTheory.setBernoulli_real_setOf_subset`: the random set contains a finite set
  `t ⊆ u` with probability `p ^ #t`.
* `ProbabilityTheory.setBernoulli_real_setOf_forall_not_subset`: the random set contains none of
  the pairwise disjoint finite sets `t k ⊆ u` with probability `∏ k, (1 - p ^ #(t k))`.
* `ProbabilityTheory.integral_ncard_inter_setBernoulli`: the expected size of the intersection of
  the random set with a finite set `t ⊆ u` is `p * #t`.
-/

public section

open MeasureTheory Measure unitInterval Finset Function

namespace ProbabilityTheory

variable {ι : Type*} {u : Set ι} {p : I} {i : ι}

variable (u p) in
lemma map_mem_setBernoulli (i : ι) :
    setBer(u, p).map (fun s ↦ i ∈ s) = Ber(i ∈ u, False, p) := by
  rw [setBernoulli_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  exact infinitePi_map_eval _ i

variable (u p) in
/-- Under `setBer(u, p)`, the events `i ∈ s` are independent. -/
lemma iIndepFun_mem_setBernoulli : iIndepFun (fun i (s : Set ι) ↦ i ∈ s) setBer(u, p) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  simp_rw [map_mem_setBernoulli]
  rw [setBernoulli_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  exact map_id

lemma setBernoulli_real_setOf_mem (hi : i ∈ u) : setBer(u, p).real {s | i ∈ s} = p := by
  rw [(by ext; simp : {s : Set ι | i ∈ s} = (fun s ↦ i ∈ s) ⁻¹' {True}),
    ← map_measureReal_apply (by fun_prop) .of_discrete, map_mem_setBernoulli,
    bernoulliMeasure_real_apply_of_mem_of_notMem _ .of_discrete (by simpa) (by simp)]

/-- The random set contains a finite set `t ⊆ u` with probability `p ^ #t`. -/
lemma setBernoulli_real_setOf_subset {t : Finset ι} (ht : ↑t ⊆ u) :
    setBer(u, p).real {s | ↑t ⊆ s} = p ^ #t := by
  rw [setOf_coe_finset_subset, measureReal_def,
    (iIndepFun_mem_setBernoulli u p).meas_biInter fun i _ ↦ ⟨{True}, .of_discrete, by ext; simp⟩,
    ENNReal.toReal_prod]
  simp_rw [← measureReal_def]
  rw [prod_congr rfl fun i hi ↦ setBernoulli_real_setOf_mem (ht hi), prod_const]

/-- The random set contains none of the pairwise disjoint finite sets `t k ⊆ u` with probability
`∏ k, (1 - p ^ #(t k))`. -/
lemma setBernoulli_real_setOf_forall_not_subset {κ : Type*} [Fintype κ] {t : κ → Finset ι}
    (ht : Pairwise (Disjoint on t)) (htu : ∀ k, ↑(t k) ⊆ u) :
    setBer(u, p).real {s | ∀ k, ¬↑(t k) ⊆ s} = ∏ k, (1 - (p : ℝ) ^ #(t k)) := by
  have hindep := (iIndepFun_mem_setBernoulli u p).restrict_of_pairwiseDisjoint
    (fun _ ↦ by fun_prop) (t := fun k ↦ (t k : Set ι)) fun k l hkl ↦ by simpa using ht hkl
  rw [(by ext; simp : {s : Set ι | ∀ k, ¬↑(t k) ⊆ s} = ⋂ k, {s | ↑(t k) ⊆ s}ᶜ), measureReal_def,
    hindep.meas_iInter fun k ↦ ⟨{v | ∀ j, v j}ᶜ, .of_discrete, by ext; simp [Set.subset_def]⟩,
    ENNReal.toReal_prod]
  refine prod_congr rfl fun k _ ↦ ?_
  rw [← measureReal_def, probReal_compl_eq_one_sub (measurableSet_setOf_coe_finset_subset _),
    setBernoulli_real_setOf_subset (htu k)]

/-- The expected size of the intersection of the random set with a finite set `t ⊆ u` is
`p * #t`. -/
lemma integral_ncard_inter_setBernoulli {t : Finset ι} (ht : ↑t ⊆ u) :
    ∫ s, ((s ∩ t).ncard : ℝ) ∂setBer(u, p) = p * #t := by
  classical
  have hind (i : ι) (s : Set ι) :
      (if i ∈ s then (1 : ℝ) else 0) = {s : Set ι | i ∈ s}.indicator 1 s := by
    simp [Set.indicator_apply]
  have hinter (s : Set ι) : s ∩ t = ↑{i ∈ t | i ∈ s} := by
    ext
    simp [and_comm]
  simp_rw [hinter, Set.ncard_coe_finset, natCast_card_filter, hind]
  rw [integral_finsetSum]
  · simp_rw [integral_indicator_one (measurableSet_mem _)]
    rw [sum_congr rfl fun i hi ↦ setBernoulli_real_setOf_mem (ht hi), sum_const, nsmul_eq_mul,
      mul_comm]
  · intro i _
    exact (integrable_const 1).indicator (measurableSet_mem i)

end ProbabilityTheory
