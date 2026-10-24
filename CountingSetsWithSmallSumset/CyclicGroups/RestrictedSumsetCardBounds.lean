/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CountingSetsWithSmallSumset.CyclicGroups.Unfolding
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
* `card_restrictedSumsetCardSets_zmod_le`: Proposition 23 (ii) of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real SumOfSetsInSeveralDimensions

variable {N : ℕ} [NeZero N]

/-- The unfolding of a set of `S_k^m(ℤ_N)` lies in `[N]`, has `k` elements and has Freiman
dimension at most `⌊4 * m / k⌋`. -/
private lemma zmodLift_mem_boundedFreimanDimSets {k m : ℕ} (hk : 0 < k) {A : Finset (ZMod N)}
    (hA : A ∈ restrictedSumsetCardSets (ZMod N) k m) :
    zmodLift A ∈ boundedFreimanDimSets N ⌊4 * (m : ℝ) / k⌋₊ k := by
  obtain ⟨hAk, hAm⟩ := mem_restrictedSumsetCardSets.1 hA
  refine ⟨zmodLift_subset_Icc A, by simp [hAk], Nat.le_floor ?_⟩
  have h := freimanDim_zmodLift_le (card_pos.1 (by grind : 0 < #A))
  rwa [hAk, hAm] at h

private lemma natCast_pow_floor_add_one_le (k m : ℕ) :
    (N : ℝ) ^ (⌊4 * (m : ℝ) / k⌋₊ + 1) ≤ (N : ℝ) ^ (1 + 4 * (m : ℝ) / k) := by
  rw [← rpow_natCast]
  refine rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 NeZero.one_le) ?_
  push_cast
  linarith [Nat.floor_le (by positivity : 0 ≤ 4 * (m : ℝ) / k)]

variable (N) in
/-- **Proposition 23 (ii)** of Green. If `k > 0`, then
`|S_k^m(ℤ_N)| ≤ N ^ (1 + 4 * m / k) * k ^ (4 * k)`. -/
theorem card_restrictedSumsetCardSets_zmod_le {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (#(restrictedSumsetCardSets (ZMod N) k m) : ℝ) ≤
      N ^ (1 + 4 * (m : ℝ) / k) * k ^ (4 * k) := by
  have h := Set.ncard_le_ncard_of_injOn zmodLift
    (fun A hA ↦ zmodLift_mem_boundedFreimanDimSets (m := m) hk hA) zmodLift_injective.injOn
    ((Icc 1 N).powerset.finite_toSet.subset fun _ ⟨hXN, _⟩ ↦ mem_powerset.2 hXN)
  rw [Set.ncard_coe_finset] at h
  exact (Nat.cast_le.2 h).trans ((card_boundedFreimanDimSets N _ hk).trans
    (mul_le_mul_of_nonneg_right (natCast_pow_floor_add_one_le k m) (by positivity)))

variable (N) in
/-- **Proposition 23 (i)** of Green. If `k ≥ 2 ^ 9000` and `m ≤ k ^ (31 / 30) / 2`, then
`|S_k^m(ℤ_N)| ≤ N ^ (1 + 4 * m / k) * (2 * e * m / k) ^ k * exp (k ^ (31 / 32))`. -/
theorem card_restrictedSumsetCardSets_zmod_le_of_le_rpow {k m : ℕ} (hk : 2 ^ 9000 ≤ k)
    (hm : (m : ℝ) ≤ k ^ ((31 : ℝ) / 30) / 2) :
    #(restrictedSumsetCardSets (ZMod N) k m) ≤
      N ^ (1 + 4 * (m : ℝ) / k) * (2 * exp 1 * m / k) ^ k * exp (k ^ ((31 : ℝ) / 32)) := by
  have ht : smallSumsetClassCountThreshold ≤ k := by rwa [smallSumsetClassCountThreshold_def]
  have hk₀ := pos_of_smallSumsetClassCountThreshold_le ht
  obtain ⟨representatives, hcover, hcard⟩ :=
    exists_coversFreimanIsoClasses_card_restrictedSumset_le_of_injective ℚ
      (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective (m := 2 * m) ht (by push_cast; linarith)
  have hsub : zmodLift '' (restrictedSumsetCardSets (ZMod N) k m : Set (Finset (ZMod N))) ⊆
      {A : Finset ℕ | #A = k ∧ #(restrictedSumset A) ≤ 2 * m} := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨hAk, hAm⟩ := mem_restrictedSumsetCardSets.1 hA
    exact ⟨by simp [hAk], hAm ▸ card_restrictedSumset_zmodLift_le A⟩
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ zmodLift_injective]
  refine (Nat.cast_le.2 (ncard_le_card_mul_pow_of_coversFreimanIsoClasses (hcover.subset hsub)
    (n := N) (r := ⌊4 * (m : ℝ) / k⌋₊) ?_)).trans ?_
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨hXn, hXk, hXr⟩ := zmodLift_mem_boundedFreimanDimSets hk₀ hA
    exact ⟨card_pos.1 (hXk ▸ hk₀), hXn, hXr⟩
  rw [Nat.cast_mul, Nat.cast_pow]
  refine (mul_le_mul hcard (natCast_pow_floor_add_one_le k m) (by positivity)
    (by positivity)).trans_eq ?_
  push_cast
  ring

end CountingSetsWithSmallSumset
