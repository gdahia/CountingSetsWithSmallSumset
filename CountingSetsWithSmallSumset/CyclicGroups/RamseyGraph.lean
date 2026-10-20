/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.CayleySumGraph
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CountingSetsWithSmallSumset.CyclicGroups.CliqueNumber

/-!
# Cayley sum graphs on `ℤ_N` without large cliques or independent sets

Theorem 8 of Green, *Counting sets with small sumset, and the clique number of random Cayley
graphs*: if `log₂ N ≥ 2 ^ 9000`, some `A ⊆ ℤ_N` has a Cayley sum graph whose clique number and
independence number are at most `160 * log₂ N`. The independent sets of `G_A` are the cliques of
`G_{ℤ_N \ A}`, so by Theorem 7 at most `2 * 2 ^ N / N < 2 ^ N` sets `A` fail.

## Main statements

* `exists_cliqueNum_le_and_indepNum_le`: Theorem 8 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real SimpleGraph

variable {N : ℕ} [NeZero N]

private lemma card_indepNum_cayleySumGraph_gt_le (hN : 2 ^ 9000 ≤ logb 2 N) :
    (#{A : Finset (ZMod N) | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).indepNum} :
      ℝ) ≤ 2 ^ N / N := by
  refine le_of_eq_of_le ?_ (card_cliqueNum_cayleySumGraph_gt_le hN)
  congr 1
  refine card_nbij' compl compl ?_ ?_ (fun A _ ↦ compl_compl A) (fun A _ ↦ compl_compl A) <;>
    intro A hA <;> simpa [← cliqueNum_compl, compl_cayleySumGraph] using hA

/-- **Theorem 8** of Green. If `log₂ N ≥ 2 ^ 9000`, then some `A ⊆ ℤ_N` has a Cayley sum graph
with clique number and independence number at most `160 * log₂ N`. -/
theorem exists_cliqueNum_le_and_indepNum_le (hN : 2 ^ 9000 ≤ logb 2 N) :
    ∃ A : Finset (ZMod N), (cayleySumGraph (A : Set (ZMod N))).cliqueNum ≤ 160 * logb 2 N ∧
      (cayleySumGraph (A : Set (ZMod N))).indepNum ≤ 160 * logb 2 N := by
  have h3 : (3 : ℝ) ≤ N := by
    rcases N with _ | _ | _ | N <;> norm_num at hN ⊢ <;> grind
  by_contra! h
  have hcover : univ ⊆
      ({A | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).cliqueNum} :
        Finset (Finset (ZMod N))) ∪
      ({A | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).indepNum} :
        Finset (Finset (ZMod N))) := by
    intro A _
    simp only [mem_union, mem_filter, mem_univ, true_and]
    grind
  have hcard := (Nat.cast_le (α := ℝ)).2 ((card_le_card hcover).trans (card_union_le _ _))
  rw [card_univ, Fintype.card_finset, ZMod.card] at hcard
  push_cast at hcard
  linarith [card_cliqueNum_cayleySumGraph_gt_le hN, card_indepNum_cayleySumGraph_gt_le hN,
    div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 ^ N) (by norm_num : (0 : ℝ) < 3) h3,
    (by positivity : (0 : ℝ) < 2 ^ N)]

end CountingSetsWithSmallSumset
