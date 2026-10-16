/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.CayleySumGraph
public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import Mathlib.Basic.Real.Basic
import CountingSetsWithSmallSumset.LargeRestrictedSumset.LargeSubset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith

/-!
# Cayley sum graphs with a large clique

Let `Γ` be a finite abelian group and `L ≥ 46656`. If the Cayley sum graph of `A ⊆ Γ` has a clique
`X` with more than `L` vertices, then Corollary 20 of Green, *Counting sets with small sumset, and
the clique number of random Cayley graphs*, gives `C ⊆ X` with `|X| ≤ 8 |C|` and
`|C ∔ C| ≥ 7 |C|`, and `C ∔ C ⊆ A` because `C` is a clique. A set `R ⊆ Γ` lies in
`2 ^ (|Γ| - |R|)` sets `A`. Hence at most `2 ^ |Γ|` times the sum of `|S_j^m(Γ)| / 2 ^ m` over
`L < 8 j ≤ 8 |Γ|` and `7 j ≤ m ≤ |Γ|` sets `A` have a Cayley sum graph with clique number greater
than `L`. This is the first step of the proofs of Theorems 7 and 9 in Section 7 of the paper.

## Main statements

* `card_lt_cliqueNum_cayleySumGraph_le`: the bound for the number of sets `A ⊆ Γ` whose Cayley sum
  graph has clique number greater than `L`.
-/

public section

namespace CountingSetsWithSmallSumset

open Finset SimpleGraph

variable {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] in
/-- A set `A` whose Cayley sum graph has clique number greater than `L ≥ 46656` contains the
restricted sumset of a set `C` with `8 |C| > L` and `|C ∔ C| ≥ 7 |C|`. -/
private lemma exists_restrictedSumset_subset_of_lt_cliqueNum {L : ℝ} (hL : 46656 ≤ L)
    {A : Finset Γ} (hA : L < (cayleySumGraph (A : Set Γ)).cliqueNum) :
    ∃ C : Finset Γ, (L < 8 * #C ∧ 7 * #C ≤ #(restrictedSumset C)) ∧ restrictedSumset C ⊆ A := by
  obtain ⟨X, hX, hXcard⟩ := (cayleySumGraph (A : Set Γ)).exists_isNClique_cliqueNum
  rw [← hXcard] at hA
  obtain ⟨C, hCX, hXC, hCm⟩ := exists_subset_seven_mul_card_le_card_restrictedSumset (A := X)
    (by exact_mod_cast hL.trans hA.le)
  exact ⟨C, ⟨hA.trans_le (by exact_mod_cast hXC), hCm⟩,
    isClique_cayleySumGraph_iff.1 (hX.subset (coe_subset.2 hCX))⟩

/-- A sum over sets `C` with `|C| ∈ J` and `|C ∔ C| ≥ 7 |C|` of `2 ^ (-|C ∔ C|)` is at most the
sum of `|S_j^m(Γ)| / 2 ^ m` over `j ∈ J` and `7 j ≤ m ≤ |Γ|`. -/
private lemma sum_one_div_two_pow_le_sum_sum {s : Finset (Finset Γ)} {J : Finset ℕ}
    (hs : ∀ C ∈ s, #C ∈ J ∧ 7 * #C ≤ #(restrictedSumset C)) :
    ∑ C ∈ s, (1 : ℝ) / 2 ^ #(restrictedSumset C) ≤ ∑ j ∈ J,
      ∑ m ∈ Icc (7 * j) (Fintype.card Γ), (#(restrictedSumsetCardSets Γ j m) : ℝ) / 2 ^ m := by
  choose hJ h7 using hs
  rw [← sum_fiberwise_of_maps_to hJ]
  gcongr with j
  rw [← sum_fiberwise_of_maps_to (g := fun C ↦ #(restrictedSumset C))
    (t := Icc (7 * j) (Fintype.card Γ))]
  · gcongr with m
    have hsub : {C ∈ {C ∈ s | #C = j} | #(restrictedSumset C) = m} ⊆
        restrictedSumsetCardSets Γ j m := by
      intro C hC
      rw [mem_filter, mem_filter] at hC
      obtain ⟨⟨-, hCj⟩, hCm⟩ := hC
      exact mem_restrictedSumsetCardSets.2 ⟨hCj, hCm⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans_eq ?_
    rw [sum_eq_card_nsmul (b := 1 / 2 ^ m), nsmul_eq_mul, mul_one_div]
    intro C hC
    obtain ⟨-, hCm⟩ := mem_restrictedSumsetCardSets.1 hC
    rw [hCm]
  · intro C hC
    obtain ⟨hCs, rfl⟩ := mem_filter.1 hC
    exact mem_Icc.2 ⟨h7 C hCs, card_le_univ _⟩

/-- Let `L ≥ 46656`. The number of sets `A ⊆ Γ` whose Cayley sum graph has clique number greater
than `L` is at most `2 ^ |Γ|` times the sum of `|S_j^m(Γ)| / 2 ^ m` over the `j ≤ |Γ|` with
`L < 8 j` and over `7 j ≤ m ≤ |Γ|`. -/
lemma card_lt_cliqueNum_cayleySumGraph_le {L : ℝ} (hL : 46656 ≤ L) :
    (#{A : Finset Γ | L < (cayleySumGraph (A : Set Γ)).cliqueNum} : ℝ) ≤
      2 ^ Fintype.card Γ * ∑ j ∈ Icc 1 (Fintype.card Γ) with L < 8 * (j : ℕ),
        ∑ m ∈ Icc (7 * j) (Fintype.card Γ), (#(restrictedSumsetCardSets Γ j m) : ℝ) / 2 ^ m := by
  set T : Finset (Finset Γ) := {C | L < 8 * #C ∧ 7 * #C ≤ #(restrictedSumset C)}
  have hcard : #{A : Finset Γ | L < (cayleySumGraph (A : Set Γ)).cliqueNum} ≤
      ∑ C ∈ T, 2 ^ (Fintype.card Γ - #(restrictedSumset C)) := by
    refine (card_le_card (t := T.biUnion fun C ↦ Icc (restrictedSumset C) univ) ?_).trans
      (card_biUnion_le.trans_eq ?_)
    · intro A hA
      obtain ⟨-, hA⟩ := mem_filter.1 hA
      obtain ⟨C, hCT, hCA⟩ := exists_restrictedSumset_subset_of_lt_cliqueNum hL hA
      exact mem_biUnion.2 ⟨C, mem_filter.2 ⟨mem_univ C, hCT⟩, mem_Icc.2 ⟨hCA, subset_univ A⟩⟩
    · congr with C
      rw [card_Icc_finset (subset_univ _), card_univ]
  have hT : ∀ C ∈ T, #C ∈ {j ∈ Icc 1 (Fintype.card Γ) | L < 8 * (j : ℕ)} ∧
      7 * #C ≤ #(restrictedSumset C) := by
    intro C hC
    obtain ⟨-, hCL, hCm⟩ := mem_filter.1 hC
    refine ⟨mem_filter.2 ⟨mem_Icc.2 ⟨?_, card_le_univ C⟩, hCL⟩, hCm⟩
    exact_mod_cast (by linarith : (0 : ℝ) < #C)
  calc _ ≤ ∑ C ∈ T, (2 : ℝ) ^ (Fintype.card Γ - #(restrictedSumset C)) := by exact_mod_cast hcard
    _ = 2 ^ Fintype.card Γ * ∑ C ∈ T, 1 / 2 ^ #(restrictedSumset C) := by
      rw [mul_sum]
      congr with C
      rw [pow_sub₀ 2 two_ne_zero (card_le_univ _), one_div]
    _ ≤ _ := by
      gcongr
      exact sum_one_div_two_pow_le_sum_sum hT

end CountingSetsWithSmallSumset
