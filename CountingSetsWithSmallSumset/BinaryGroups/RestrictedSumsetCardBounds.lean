/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CountingSetsWithSmallSumset.BinaryGroups.FreimanDimension
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationCodes
import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ClassCountBounds

/-!
# The number of subsets of `𝔽₂ⁿ` with a given size of restricted sumset

This file proves Proposition 26 of Green, *Counting sets with small sumset, and the clique number
of random Cayley graphs*: bounds for the size of `S_k^m(𝔽₂ⁿ)`. Write `N = 2 ^ n`. Every set of
`S_k^m(𝔽₂ⁿ)` is Freiman isomorphic to a member of a family of class representatives. By Lemma 25,
the sets of `S_k^m(𝔽₂ⁿ)` that are Freiman isomorphic to a given set number at most
`N ^ (4 * m * log₂ k / k)`. The number of classes is at most `k ^ (4 * k)` by Lemma 11, and at
most `(e * m / k) ^ k * exp (k ^ (31 / 32))` by Proposition 18 when `m ≤ k ^ (31 / 30)`.

## Main statements

* `card_restrictedSumsetCardSets_pi_zmod_two_le_of_le_rpow`: Proposition 26 (i) of Green.
* `card_restrictedSumsetCardSets_pi_zmod_two_le`: Proposition 26 (ii) of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real

variable {n : ℕ}

/-- A family of sets of `S_k^m(𝔽₂ⁿ)` that are all Freiman isomorphic to `B` has at most
`(2 ^ n) ^ (4 * m * log₂ k / k)` members. -/
private lemma card_le_of_forall_freimanIsomorphic {k m : ℕ} (hk : 2 ≤ k)
    {s : Finset (Finset (Fin n → ZMod 2))} (hs : s ⊆ restrictedSumsetCardSets (Fin n → ZMod 2) k m)
    {B : Finset (Fin n → ZMod 2)} (hB : ∀ A ∈ s, FreimanIsomorphic 2 A B) :
    #s ≤ ((2 : ℝ) ^ n) ^ (4 * m * logb 2 k / k) := by
  obtain rfl | ⟨A₀, hA₀⟩ := s.eq_empty_or_nonempty
  · rw [card_empty, Nat.cast_zero]
    positivity
  obtain ⟨rfl, hA₀m⟩ := mem_restrictedSumsetCardSets.1 (hs hA₀)
  rw [← Set.ncard_coe_finset]
  refine (Nat.cast_le.2 (Set.ncard_le_ncard ?_ (Set.toFinite _))).trans
    (ncard_isAddFreimanIso_le_of_card_restrictedSumset_le hk hA₀m.le n)
  intro A hA
  exact (hB A₀ hA₀).trans (hB A hA).symm

/-- If every set of `k` elements of `𝔽₂ⁿ` with at most `m` elements in its restricted sumset is
Freiman isomorphic to a member of `representatives`, then
`|S_k^m(𝔽₂ⁿ)| ≤ |representatives| * (2 ^ n) ^ (4 * m * log₂ k / k)`. -/
private lemma card_restrictedSumsetCardSets_le_card_mul {k m : ℕ} (hk : 2 ≤ k)
    {representatives : Finset (Finset (Fin n → ZMod 2))}
    (hcover : CoversFreimanIsoClasses 2
      {A : Finset (Fin n → ZMod 2) | #A = k ∧ #(restrictedSumset A) ≤ m} representatives) :
    #(restrictedSumsetCardSets (Fin n → ZMod 2) k m) ≤
      #representatives * ((2 : ℝ) ^ n) ^ (4 * m * logb 2 k / k) := by
  choose! r hr hrA using fun A (hA : A ∈ restrictedSumsetCardSets (Fin n → ZMod 2) k m) ↦
    hcover A (by grind [mem_restrictedSumsetCardSets])
  rw [card_eq_sum_card_fiberwise hr, Nat.cast_sum, ← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ ?_
  intro B _
  refine card_le_of_forall_freimanIsomorphic (B := B) hk (filter_subset _ _) ?_
  intro A hA
  obtain ⟨hAS, rfl⟩ := mem_filter.1 hA
  exact hrA A hAS

variable (n) in
/-- **Proposition 26 (i)** of Green. If `k ≥ 2 ^ 9000` and `m ≤ k ^ (31 / 30)`, then
`|S_k^m(𝔽₂ⁿ)| ≤ N ^ (4 * m * log₂ k / k) * (e * m / k) ^ k * exp (k ^ (31 / 32))`, where
`N = 2 ^ n`. -/
lemma card_restrictedSumsetCardSets_pi_zmod_two_le_of_le_rpow {k m : ℕ} (hk : 2 ^ 9000 ≤ k)
    (hm : m ≤ (k : ℝ) ^ ((31 : ℝ) / 30)) :
    #(restrictedSumsetCardSets (Fin n → ZMod 2) k m) ≤
      (2 ^ n) ^ (4 * m * logb 2 k / k) * (exp 1 * m / k) ^ k * exp (k ^ ((31 : ℝ) / 32)) := by
  have ht : smallSumsetClassCountThreshold ≤ k := by rwa [smallSumsetClassCountThreshold_def]
  obtain ⟨representatives, hcover, hcard⟩ :=
    exists_coversFreimanIsoClasses_card_restrictedSumset_le (ZMod 2) (Fin n → ZMod 2) ht hm
  refine (card_restrictedSumsetCardSets_le_card_mul
    (one_lt_of_smallSumsetClassCountThreshold_le ht) hcover).trans ?_
  refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_
  ring

variable (n) in
/-- **Proposition 26 (ii)** of Green. If `k ≥ 2`, then
`|S_k^m(𝔽₂ⁿ)| ≤ N ^ (4 * m * log₂ k / k) * k ^ (4 * k)`, where `N = 2 ^ n`. -/
lemma card_restrictedSumsetCardSets_pi_zmod_two_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    #(restrictedSumsetCardSets (Fin n → ZMod 2) k m) ≤
      ((2 : ℝ) ^ n) ^ (4 * m * logb 2 k / k) * k ^ (4 * k) := by
  obtain ⟨representatives, hcover, hcard⟩ :=
    exists_coversFreimanIsoClasses_card_le_pow (ZMod 2) (Fin n → ZMod 2) 2 k
  refine (card_restrictedSumsetCardSets_le_card_mul hk (hcover.subset fun A ⟨hA, _⟩ ↦ hA)).trans ?_
  rw [mul_comm]
  gcongr
  exact_mod_cast (hcard : #representatives ≤ k ^ (4 * k))

end CountingSetsWithSmallSumset
