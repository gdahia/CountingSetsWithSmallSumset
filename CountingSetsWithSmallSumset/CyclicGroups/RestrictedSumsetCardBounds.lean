/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import CountingSetsWithSmallSumset.CyclicGroups.Unfolding
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.MembersInInterval
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationSpaces
import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ClassCountBounds

/-!
# The number of subsets of `ℤ_N` with a given size of restricted sumset

This file proves Proposition 23 of Green, *Counting sets with small sumset, and the clique number
of random Cayley graphs*: bounds for the size of `S_k^m(ℤ_N)`. The unfolding map is injective, so
it suffices to count the unfoldings `Ā ⊆ [N]` of the sets `A ∈ S_k^m(ℤ_N)`. Each `Ā` has `k`
elements, at most `2 * m` elements in its restricted sumset and, by Lemma 22, Freiman dimension at
most `4 * m / k`. A Freiman isomorphism class of dimension at most `r` has at most `N ^ (r + 1)`
members in `[N]`. The number of classes is at most `k ^ (4 * k)` in general, and at most
`(2 * e * m / k) ^ k * exp (k ^ (31 / 32))` by Proposition 18 when `m ≤ k ^ (31 / 30) / 2`.

## Main statements

* `card_restrictedSumsetCardSets_zmod_le_of_le_rpow`: Proposition 23 (i) of Green.
* `card_restrictedSumsetCardSets_zmod_le_of_freimanDim_le`: Proposition 23 (ii) of Green with a
  bound `r` for the Freiman dimension of the unfoldings in place of `4 * m / k`.
* `card_restrictedSumsetCardSets_zmod_le`: Proposition 23 (ii) of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real SumOfSetsInSeveralDimensions

variable {N : ℕ} [NeZero N]

private lemma natCast_pow_floor_add_one_le (k m : ℕ) :
    (N : ℝ) ^ (⌊4 * (m : ℝ) / k⌋₊ + 1) ≤ (N : ℝ) ^ (1 + 4 * (m : ℝ) / k) := by
  rw [← rpow_natCast]
  apply rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 NeZero.one_le)
  push_cast
  linarith [Nat.floor_le (by positivity : 0 ≤ 4 * (m : ℝ) / k)]

/-- If the unfoldings of the sets of `S_k^m(ℤ_N)` have Freiman dimension at most `r` and lie in
the Freiman isomorphism classes of the members of `representatives`, then
`|S_k^m(ℤ_N)| ≤ |representatives| * N ^ (r + 1)`. -/
private lemma card_restrictedSumsetCardSets_zmod_le_card_mul_pow {k m r : ℕ} (hk : 0 < k)
    {representatives : Finset (Finset ℕ)} (hrep : RepresentsFreimanIsoClasses 2
      (zmodLift '' (restrictedSumsetCardSets (ZMod N) k m : Set (Finset (ZMod N))))
      representatives)
    (hr : ∀ A ∈ restrictedSumsetCardSets (ZMod N) k m, freimanDim (zmodLift A) ≤ r) :
    #(restrictedSumsetCardSets (ZMod N) k m) ≤ #representatives * N ^ (r + 1) := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ zmodLift_injective]
  apply ncard_le_card_mul_pow_of_representsFreimanIsoClasses hrep
  rintro _ ⟨A, hA, rfl⟩
  exact ⟨card_pos.1 (by simp [(mem_restrictedSumsetCardSets.1 hA).1, hk]), zmodLift_subset_Icc A,
    hr A hA⟩

/-- By Lemma 22, if `k > 0`, then the unfoldings of the sets of `S_k^m(ℤ_N)` have Freiman
dimension at most `⌊4 * m / k⌋`. -/
private lemma freimanDim_zmodLift_le_floor {k m : ℕ} (hk : 0 < k) {A : Finset (ZMod N)}
    (hA : A ∈ restrictedSumsetCardSets (ZMod N) k m) :
    freimanDim (zmodLift A) ≤ ⌊4 * (m : ℝ) / k⌋₊ := by
  obtain ⟨hAk, hAm⟩ := mem_restrictedSumsetCardSets.1 hA
  apply Nat.le_floor
  have h := freimanDim_zmodLift_le (card_pos.1 (by grind : 0 < #A))
  rwa [hAk, hAm] at h

/-- If the unfoldings of the sets of `S_k^m(ℤ_N)` lie in the Freiman isomorphism classes of the
members of `representatives`, then `|S_k^m(ℤ_N)| ≤ |representatives| * N ^ (1 + 4 * m / k)`. -/
private lemma card_restrictedSumsetCardSets_zmod_le_card_mul {k m : ℕ} (hk : 0 < k)
    {representatives : Finset (Finset ℕ)} (hrep : RepresentsFreimanIsoClasses 2
      (zmodLift '' (restrictedSumsetCardSets (ZMod N) k m : Set (Finset (ZMod N))))
      representatives) :
    #(restrictedSumsetCardSets (ZMod N) k m) ≤
      #representatives * (N : ℝ) ^ (1 + 4 * (m : ℝ) / k) := by
  refine (Nat.cast_le.2 (card_restrictedSumsetCardSets_zmod_le_card_mul_pow hk hrep
    fun _ ↦ freimanDim_zmodLift_le_floor hk)).trans ?_
  push_cast
  exact mul_le_mul_of_nonneg_left (natCast_pow_floor_add_one_le k m) (by positivity)

variable (N) in
/-- **Proposition 23 (ii)** of Green with a bound for the Freiman dimension of the unfoldings. If
`k > 0` and the unfoldings of the sets of `S_k^m(ℤ_N)` have Freiman dimension at most `r`, then
`|S_k^m(ℤ_N)| ≤ N ^ (r + 1) * k ^ (4 * k)`. -/
lemma card_restrictedSumsetCardSets_zmod_le_of_freimanDim_le {k m r : ℕ} (hk : 0 < k)
    (hr : ∀ A ∈ restrictedSumsetCardSets (ZMod N) k m, freimanDim (zmodLift A) ≤ r) :
    #(restrictedSumsetCardSets (ZMod N) k m) ≤ N ^ (r + 1) * k ^ (4 * k) := by
  obtain ⟨representatives, hrep, hcard⟩ := exists_representsFreimanIsoClasses_card_le_pow ℚ ℚ 2 k
  have hsub : image (Nat.castAddMonoidHom ℚ) ''
      (zmodLift '' (restrictedSumsetCardSets (ZMod N) k m : Set (Finset (ZMod N)))) ⊆
      {A | #A = k} := by
    rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    simp [card_image_of_injective _ Nat.cast_injective, (mem_restrictedSumsetCardSets.1 hA).1]
  obtain ⟨representatives', -, hrep', hcard'⟩ := exists_representsFreimanIsoClasses_card_le_of_image
    (isAddFreimanIso_image_of_injective 2 (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective)
    (hrep.subset hsub)
  rw [mul_comm]
  apply (card_restrictedSumsetCardSets_zmod_le_card_mul_pow hk hrep' hr).trans
  gcongr
  exact hcard'.trans hcard

variable (N) in
/-- **Proposition 23 (ii)** of Green. If `k > 0`, then
`|S_k^m(ℤ_N)| ≤ N ^ (1 + 4 * m / k) * k ^ (4 * k)`. -/
lemma card_restrictedSumsetCardSets_zmod_le {k : ℕ} (hk : 0 < k) (m : ℕ) :
    #(restrictedSumsetCardSets (ZMod N) k m) ≤ (N : ℝ) ^ (1 + 4 * (m : ℝ) / k) * k ^ (4 * k) := by
  refine (Nat.cast_le.2 (card_restrictedSumsetCardSets_zmod_le_of_freimanDim_le N hk
    fun _ ↦ freimanDim_zmodLift_le_floor hk)).trans ?_
  push_cast
  exact mul_le_mul_of_nonneg_right (natCast_pow_floor_add_one_le k m) (by positivity)

variable (N) in
/-- **Proposition 23 (i)** of Green. If `k ≥ 2 ^ 9000` and `m ≤ k ^ (31 / 30) / 2`, then
`|S_k^m(ℤ_N)| ≤ N ^ (1 + 4 * m / k) * (2 * e * m / k) ^ k * exp (k ^ (31 / 32))`. -/
lemma card_restrictedSumsetCardSets_zmod_le_of_le_rpow {k m : ℕ} (hk : 2 ^ 9000 ≤ k)
    (hm : m ≤ (k : ℝ) ^ ((31 : ℝ) / 30) / 2) :
    #(restrictedSumsetCardSets (ZMod N) k m) ≤
      N ^ (1 + 4 * (m : ℝ) / k) * (2 * exp 1 * m / k) ^ k * exp (k ^ ((31 : ℝ) / 32)) := by
  have ht : smallSumsetClassCountThreshold ≤ k := by rwa [smallSumsetClassCountThreshold_def]
  obtain ⟨representatives, hrep, hcard⟩ :=
    exists_representsFreimanIsoClasses_card_restrictedSumset_le_of_injective ℚ
      (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective (m := 2 * m) ht (by push_cast; linarith)
  have hsub : zmodLift '' (restrictedSumsetCardSets (ZMod N) k m : Set (Finset (ZMod N))) ⊆
      {A : Finset ℕ | #A = k ∧ #(restrictedSumset A) ≤ 2 * m} := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨hAk, hAm⟩ := mem_restrictedSumsetCardSets.1 hA
    exact ⟨by simp [hAk], hAm ▸ card_restrictedSumset_zmodLift_le A⟩
  apply (card_restrictedSumsetCardSets_zmod_le_card_mul
    (pos_of_smallSumsetClassCountThreshold_le ht) (hrep.subset hsub)).trans
  apply (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq
  push_cast
  ring

end CountingSetsWithSmallSumset
