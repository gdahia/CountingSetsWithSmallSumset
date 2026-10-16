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
  have h3 : (3 : ℝ) ≤ N := (by norm_num : (3 : ℝ) ≤ 2 ^ (2 : ℝ)).trans
    ((le_logb_iff_rpow_le one_lt_two (Nat.cast_pos.2 (NeZero.pos N))).1
      ((by norm_num : (2 : ℝ) ≤ 2 ^ 9).trans ((pow_le_pow_right₀ (by norm_num) (by norm_num) :
        (2 : ℝ) ^ 9 ≤ 2 ^ 9000).trans hN)))
  by_contra! h
  set P : Finset (Finset (ZMod N)) :=
    {A | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).cliqueNum}
  set Q : Finset (Finset (ZMod N)) :=
    {A | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).indepNum}
  have hcover : (univ : Finset (Finset (ZMod N))) ⊆ P ∪ Q := by
    intro A _
    rw [mem_union, mem_filter, mem_filter]
    by_cases hA : ((cayleySumGraph (A : Set (ZMod N))).cliqueNum : ℝ) ≤ 160 * logb 2 N
    · exact Or.inr ⟨mem_univ A, h A hA⟩
    · exact Or.inl ⟨mem_univ A, not_le.1 hA⟩
  have hcard := (Nat.cast_le (α := ℝ)).2 ((card_le_card hcover).trans (card_union_le P Q))
  rw [card_univ, Fintype.card_finset, ZMod.card] at hcard
  push_cast at hcard
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  linarith [card_cliqueNum_cayleySumGraph_gt_le hN, card_indepNum_cayleySumGraph_gt_le hN,
    div_le_div_of_nonneg_left h2N.le (by norm_num : (0 : ℝ) < 3) h3]

end CountingSetsWithSmallSumset
