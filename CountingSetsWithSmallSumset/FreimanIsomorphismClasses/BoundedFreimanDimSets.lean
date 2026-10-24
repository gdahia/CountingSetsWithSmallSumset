/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Covers
public import SumOfSetsInSeveralDimensions.FreimanDimension
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import CountingSetsWithSmallSumset.FreimanDimension.IsomorphicCopies
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationCodes
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sets of natural numbers of bounded Freiman dimension

This file follows Section 3 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*, for sets of natural numbers. A Freiman isomorphism class of order `2` of
sets of Freiman dimension at most `r` has at most `n ^ (r + 1)` members in `[n] = {1, …, n}`. So a
family of such sets that is covered by `K` classes has at most `K * n ^ (r + 1)` members. By
Lemma 11 of Green, applied in `ℚ`, the sets of `t` natural numbers lie in at most `t ^ (4 * t)`
classes. Hence there are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with `t` elements and
Freiman dimension at most `r`.

## Main definitions

* `boundedFreimanDimSets n r t`: the sets `X ⊆ [n]` with `t` elements and Freiman dimension at
  most `r`.
* `smallSumsetFreimanDimSets n r s t`: the sets of `boundedFreimanDimSets n r t` with
  `|X + X| ≤ s`.

## Main statements

* `ncard_le_card_mul_pow_of_coversFreimanIsoClasses`: a family of nonempty sets `X ⊆ [n]` with
  `freimanDim X ≤ r` that is covered by `K` classes has at most `K * n ^ (r + 1)` members.
* `card_boundedFreimanDimSets`: there are at most `n ^ (r + 1) * t ^ (4 * t)` sets in
  `boundedFreimanDimSets n r t`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

/-- The sets `X ⊆ [n]` with `t` elements and Freiman dimension at most `r`. -/
def boundedFreimanDimSets (n r t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r}

/-- The sets `X` of `boundedFreimanDimSets n r t` with `|X + X| ≤ s`. -/
def smallSumsetFreimanDimSets (n r s t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r ∧ #(X + X) ≤ s}

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

/-- If `representatives` covers the classes of order `2` of a family of nonempty sets `X ⊆ [n]`
with `freimanDim X ≤ r`, then the family has at most `|representatives| * n ^ (r + 1)`
members. -/
lemma ncard_le_card_mul_pow_of_coversFreimanIsoClasses {n r : ℕ} {family : Set (Finset ℕ)}
    {representatives : Finset (Finset ℕ)}
    (hcover : CoversFreimanIsoClasses 2 family representatives)
    (hfamily : ∀ X ∈ family, X.Nonempty ∧ X ⊆ Icc 1 n ∧ freimanDim X ≤ r) :
    family.ncard ≤ #representatives * n ^ (r + 1) := by
  classical
  have hfin : family.Finite := by
    refine (Icc 1 n).powerset.finite_toSet.subset ?_
    intro X hX
    obtain ⟨-, hXn, -⟩ := hfamily X hX
    exact mem_powerset.2 hXn
  choose! B hB hXB using hcover
  rw [Set.ncard_eq_toFinset_card _ hfin, mul_comm]
  refine card_le_mul_card_image_of_maps_to (fun X hX ↦ hB X (hfin.mem_toFinset.1 hX)) _ ?_
  intro C _
  refine card_le_pow_of_forall_freimanIsomorphic (C := C) ?_
  intro X hXC
  obtain ⟨hX, rfl⟩ := mem_filter.1 hXC
  rw [hfin.mem_toFinset] at hX
  obtain ⟨hXne, hXn, hXr⟩ := hfamily X hX
  exact ⟨hXne, hXn, hXr, hXB X hX⟩

/-- There are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with `t` elements and Freiman
dimension at most `r`. -/
lemma card_boundedFreimanDimSets (n r : ℕ) {t : ℕ} (ht : 0 < t) :
    (boundedFreimanDimSets n r t).ncard ≤ (n : ℝ) ^ (r + 1) * t ^ (4 * t) := by
  obtain ⟨representatives, hcover, hcard⟩ := exists_coversFreimanIsoClasses_card_le_pow ℚ ℚ 2 t
  have hsub : image (Nat.castAddMonoidHom ℚ) '' boundedFreimanDimSets n r t ⊆ {A | #A = t} := by
    rintro _ ⟨X, ⟨-, hX, -⟩, rfl⟩
    simpa [card_image_of_injective _ Nat.cast_injective]
  obtain ⟨representatives', -, hcover', hcard'⟩ := exists_coversFreimanIsoClasses_card_le_of_image
    (isAddFreimanIso_image_of_injective 2 (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective)
    (hcover.subset hsub)
  rw [mul_comm]
  exact_mod_cast (ncard_le_card_mul_pow_of_coversFreimanIsoClasses hcover' fun X ⟨hXn, hX, hXr⟩ ↦
    ⟨card_pos.1 (hX ▸ ht), hXn, hXr⟩).trans (Nat.mul_le_mul_right _ (hcard'.trans hcard))

end CountingSetsWithSmallSumset
