/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import CountingSetsWithSmallSumset.CayleySumGraph
import CountingSetsWithSmallSumset.BinaryGroups.CliqueNumber
import CountingSetsWithSmallSumset.CyclicGroups.CliqueNumber
import CountingSetsWithSmallSumset.CyclicGroups.RamseyGraph

/-!
# Counting sets with small sumset

The statements of `Challenge.lean`, proved by the results of the library with the same names
without the prime.
-/

public section

open Finset Real SimpleGraph Filter Topology

namespace CountingSetsWithSmallSumset

/-- **Theorem 7** of Green. If `log₂ N ≥ 2 ^ 9000`, at most `2 ^ N / N` subsets `A ⊆ ℤ/Nℤ` have a
Cayley sum graph with clique number greater than `160 * log₂ N`. -/
theorem card_cliqueNum_cayleySumGraph_gt_le' {N : ℕ} [NeZero N] (hN : 2 ^ 9000 ≤ logb 2 N) :
    #{A : Finset (ZMod N) | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).cliqueNum} ≤
      (2 : ℝ) ^ N / N :=
  card_cliqueNum_cayleySumGraph_gt_le hN

/-- **Theorem 7** of Green. The proportion of the subsets `A ⊆ ℤ/Nℤ` whose Cayley sum graph has
clique number at most `160 * log₂ N` tends to `1`. -/
theorem tendsto_card_cliqueNum_cayleySumGraph_le' :
    Tendsto (fun N : ℕ+ ↦ (#{A : Finset (ZMod N) |
      (cayleySumGraph (A : Set (ZMod N))).cliqueNum ≤ 160 * logb 2 N} : ℝ) / 2 ^ (N : ℕ))
      atTop (𝓝 1) :=
  tendsto_card_cliqueNum_cayleySumGraph_le

/-- **Theorem 8** of Green. If `log₂ N ≥ 2 ^ 9000`, some subset `A ⊆ ℤ/Nℤ` has a Cayley sum graph
with clique number and independence number at most `160 * log₂ N`. -/
theorem exists_cliqueNum_le_and_indepNum_le' {N : ℕ} [NeZero N] (hN : 2 ^ 9000 ≤ logb 2 N) :
    ∃ A : Finset (ZMod N), (cayleySumGraph (A : Set (ZMod N))).cliqueNum ≤ 160 * logb 2 N ∧
      (cayleySumGraph (A : Set (ZMod N))).indepNum ≤ 160 * logb 2 N :=
  exists_cliqueNum_le_and_indepNum_le hN

/-- **Theorem 9** of Green, as a count. If `n ≥ 2 ^ 9000`, at most
`2 ^ 2 ^ n / n + 2 ^ 2 ^ n / 2 ^ n` subsets `A ⊆ 𝔽₂ⁿ` have a Cayley graph with clique number
outside `[n * log₂ n / 4, 308 * n * log₂ n]`. -/
theorem card_cliqueNum_addCayley_lt_or_gt_le' {n : ℕ} (hn : 2 ^ 9000 ≤ n) :
    #{A : Finset (Fin n → ZMod 2) |
      (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * logb 2 n / 4 ∨
        308 * n * logb 2 n < (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum} ≤
      (2 : ℝ) ^ 2 ^ n / n + 2 ^ 2 ^ n / 2 ^ n :=
  card_cliqueNum_addCayley_lt_or_gt_le hn

/-- **Theorem 9** of Green. The proportion of the subsets `A ⊆ 𝔽₂ⁿ` whose Cayley graph has clique
number in `[n * log₂ n / 4, 308 * n * log₂ n]` tends to `1`. -/
theorem tendsto_card_le_cliqueNum_addCayley_le' :
    Tendsto (fun n : ℕ ↦ (#{A : Finset (Fin n → ZMod 2) |
      n * logb 2 n / 4 ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum ∧
        (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum ≤ 308 * n * logb 2 n} : ℝ) / 2 ^ 2 ^ n)
      atTop (𝓝 1) :=
  tendsto_card_le_cliqueNum_addCayley_le

end CountingSetsWithSmallSumset
