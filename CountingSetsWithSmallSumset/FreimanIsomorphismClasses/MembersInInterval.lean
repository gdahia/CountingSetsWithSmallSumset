/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Representatives
public import SumOfSetsInSeveralDimensions.FreimanDimension
import CountingSetsWithSmallSumset.FreimanDimension.IsomorphicCopies
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Members of a Freiman isomorphism class in an interval

This file proves the counting step of the proof of Proposition 23 of Green, *Counting sets with
small sumset, and the clique number of random Cayley graphs*. A Freiman isomorphism class of order
`2` of sets of Freiman dimension at most `r` has at most `n ^ (r + 1)` members in
`[n] = {1, …, n}`. So a family of such sets that lies in `K` classes has at most `K * n ^ (r + 1)`
members.

## Main statements

* `ncard_le_card_mul_pow_of_representsFreimanIsoClasses`: a family of nonempty sets `X ⊆ [n]` with
  `freimanDim X ≤ r` that lies in `K` classes has at most `K * n ^ (r + 1)` members.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions

/-- A finite family of nonempty sets `X ⊆ [n]` with `freimanDim X ≤ r` that are all Freiman
isomorphic of order `2` to `C` has at most `n ^ (r + 1)` members. -/
private lemma card_le_pow_of_forall_freimanIsomorphic {n r : ℕ} {s : Finset (Finset ℕ)}
    {C : Finset ℕ}
    (hs : ∀ X ∈ s, X.Nonempty ∧ X ⊆ Icc 1 n ∧ freimanDim X ≤ r ∧ FreimanIsomorphic 2 X C) :
    #s ≤ n ^ (r + 1) := by
  obtain rfl | ⟨X, hX⟩ := s.eq_empty_or_nonempty
  · simp
  obtain ⟨⟨x, hx⟩, hXn, hXr, hXC⟩ := hs X hX
  rw [← Set.ncard_coe_finset]
  refine (Set.ncard_le_ncard (t := {Y | Y ⊆ Icc 1 n ∧ FreimanIsomorphic 2 X Y}) ?_
    ((Icc 1 n).powerset.finite_toSet.subset fun _ ⟨hYn, _⟩ ↦ mem_powerset.2 hYn)).trans ?_
  · intro Y hY
    obtain ⟨-, hYn, -, hYC⟩ := hs Y hY
    exact ⟨hYn, hXC.trans hYC.symm⟩
  refine (ncard_freimanIsomorphic_subset_le ⟨x, hx⟩ (Icc 1 n)).trans ?_
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  exact Nat.pow_le_pow_right (by grind [mem_Icc.1 (hXn hx)]) (by grind)

/-- If a family of nonempty sets `X ⊆ [n]` with `freimanDim X ≤ r` is represented by
`representatives` up to Freiman isomorphism of order `2`, then the family has at most
`|representatives| * n ^ (r + 1)` members. -/
lemma ncard_le_card_mul_pow_of_representsFreimanIsoClasses {n r : ℕ} {family : Set (Finset ℕ)}
    {representatives : Finset (Finset ℕ)}
    (hrep : RepresentsFreimanIsoClasses 2 family representatives)
    (hfamily : ∀ X ∈ family, X.Nonempty ∧ X ⊆ Icc 1 n ∧ freimanDim X ≤ r) :
    family.ncard ≤ #representatives * n ^ (r + 1) := by
  classical
  have hfin : family.Finite := by
    refine (Icc 1 n).powerset.finite_toSet.subset ?_
    intro X hX
    obtain ⟨-, hXn, -⟩ := hfamily X hX
    exact mem_powerset.2 hXn
  choose! B hB hXB using hrep
  rw [Set.ncard_eq_toFinset_card _ hfin, mul_comm]
  refine card_le_mul_card_image_of_maps_to (fun X hX ↦ hB X (hfin.mem_toFinset.1 hX)) _ ?_
  intro C _
  refine card_le_pow_of_forall_freimanIsomorphic (C := C) ?_
  intro X hXC
  obtain ⟨hX, rfl⟩ := mem_filter.1 hXC
  rw [hfin.mem_toFinset] at hX
  obtain ⟨hXne, hXn, hXr⟩ := hfamily X hX
  exact ⟨hXne, hXn, hXr, hXB X hX⟩

end CountingSetsWithSmallSumset
