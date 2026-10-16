/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.LinearAlgebra.Dimension.Finrank
import CountingSetsWithSmallSumset.BinaryLowerBound.Covariance
import CountingSetsWithSmallSumset.BinaryLowerBound.SecondMoment
import CountingSetsWithSmallSumset.BinaryLowerBound.SubspaceCount
import CountingSetsWithSmallSumset.BinaryLowerBound.SubspaceDimension
import Mathlib.Algebra.Field.ZMod

/-!
# A lower bound for the clique number of random Cayley graphs on `𝔽₂ⁿ`

This file proves Proposition 27 of Green, the lower bound of Theorem 9: the Cayley graph of a
uniformly random `A ⊆ 𝔽₂ⁿ` has clique number at least `n * log₂ n / 4` with probability tending
to `1`. In `𝔽₂ⁿ` the Cayley sum graph of `A` is the Cayley graph `SimpleGraph.addCayley A`.

Let `k` be as in `exists_dim_of_two_pow_sixteen_le`, so that `2 ^ k ≥ n * log₂ n / 4`. If `A`
contains `H \ {0}` for a `k`-dimensional subspace `H`, then `H` is a clique with `2 ^ k` vertices.
The second moment method (`card_filter_forall_not_subset_mul_sq_le`) bounds the number of `A`
containing no such `H \ {0}` in terms of the number of `k`-dimensional subspaces
(`two_pow_le_two_pow_mul_card_finrank_eq`) and the covariance terms
(`mul_sum_sum_two_pow_sub_one_le`, which rests on Lemma 28 of Green).

## Main statements

* `two_pow_finrank_le_cliqueNum_addCayley`: if `H \ {0} ⊆ A`, then the clique number of the Cayley
  graph of `A` is at least `2 ^ dim H`.
* `card_cliqueNum_addCayley_lt_le`: Proposition 27 of Green, explicit form. For `n ≥ 2 ^ 16`, at
  most `2 ^ 2 ^ n / n` sets `A ⊆ 𝔽₂ⁿ` have clique number less than `n * log₂ n / 4`.
* `tendsto_card_le_cliqueNum_addCayley`: Proposition 27 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Module SimpleGraph Filter Topology

/-- If `A` contains `H \ {0}` for a subspace `H` of `𝔽₂ⁿ`, then `H` is a clique of the Cayley
graph of `A`, so its clique number is at least `2 ^ dim H`. In the terms of Green, `H \ {0}` is the
restricted sumset of `H`. -/
lemma two_pow_finrank_le_cliqueNum_addCayley {n : ℕ} {H : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {A : Finset (Fin n → ZMod 2)} (hA : ∀ x ∈ H, x ≠ 0 → x ∈ A) :
    2 ^ finrank (ZMod 2) H ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum := by
  classical
  rw [← card_filter_mem_submodule H]
  refine IsClique.card_le_cliqueNum ?_
  intro x hx y hy hxy
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
  rw [addCayley_adj]
  exact ⟨hxy, Or.inl (hA _ (H.add_mem (H.neg_mem hx) hy) (by grind [neg_add_eq_zero]))⟩

/-- The nonzero elements of a subspace `H` of `𝔽₂ⁿ`. In the terms of Green, this is the
restricted sumset of `H`. -/
private noncomputable def nonzeroElements {n : ℕ} (H : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Finset (Fin n → ZMod 2) := by
  classical
  exact ({x | x ∈ H} : Finset _).erase 0

private lemma card_nonzeroElements_inter {n : ℕ} (H H' : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    #(nonzeroElements H ∩ nonzeroElements H') = 2 ^ finrank (ZMod 2) ↥(H ⊓ H') - 1 := by
  classical
  rw [← card_filter_mem_submodule,
    ← card_erase_of_mem (s := {x | x ∈ H ⊓ H'}) (a := 0) (by simp)]
  congr 1
  ext x
  simp only [nonzeroElements, mem_inter, mem_erase, mem_filter, mem_univ, true_and,
    Submodule.mem_inf]
  tauto

/-- A set `A ⊆ 𝔽₂ⁿ` whose Cayley graph has clique number less than `n * log₂ n / 4 ≤ 2 ^ k` contains
the nonzero elements of no `k`-dimensional subspace. -/
private lemma card_cliqueNum_lt_le_card_forall_not_subset {n k : ℕ}
    (hlog : n * Real.logb 2 n / 4 ≤ 2 ^ k) :
    #{A : Finset (Fin n → ZMod 2) |
      (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * Real.logb 2 n / 4} ≤
      #{A : Finset (Fin n → ZMod 2) | ∀ H ∈ ({H | finrank (ZMod 2) H = k} :
        Finset (Submodule (ZMod 2) (Fin n → ZMod 2))), ¬nonzeroElements H ⊆ A} := by
  classical
  apply card_le_card
  intro A hA
  obtain ⟨-, hA⟩ := mem_filter.mp hA
  rw [mem_filter]
  refine ⟨mem_univ A, ?_⟩
  intro H hH hHA
  have h := two_pow_finrank_le_cliqueNum_addCayley (A := A) (H := H)
    fun x hx hx₀ ↦ hHA (by simp [nonzeroElements, hx, hx₀])
  simp only [mem_filter, mem_univ, true_and] at hH
  rw [hH] at h
  have h' : (2 : ℝ) ^ k ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum := by exact_mod_cast h
  linarith

/-- **Proposition 27** of Green, explicit form. For `n ≥ 2 ^ 16`, at most `2 ^ 2 ^ n / n` of the
`2 ^ 2 ^ n` sets `A ⊆ 𝔽₂ⁿ` have a Cayley graph with clique number less than `n * log₂ n / 4`. -/
theorem card_cliqueNum_addCayley_lt_le {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    #{A : Finset (Fin n → ZMod 2) |
      (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * Real.logb 2 n / 4} ≤
      (2 ^ 2 ^ n / n : ℝ) := by
  classical
  obtain ⟨k, hkn, hlog, hk, hkn'⟩ := exists_dim_of_two_pow_sixteen_le hn
  set ℋ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2)) := {H | finrank (ZMod 2) H = k}
  set Z : ℕ := #{A : Finset (Fin n → ZMod 2) | ∀ H ∈ ℋ, ¬nonzeroElements H ⊆ A}
  set S : ℝ := ∑ i ∈ ℋ, ∑ j ∈ ℋ, ((2 : ℝ) ^ (2 ^ finrank (ZMod 2) ↥(i ⊓ j) - 1) - 1)
  have h2 : (Z : ℝ) * #ℋ ^ 2 ≤ 2 ^ 2 ^ n * S := by
    convert card_filter_forall_not_subset_mul_sq_le ℋ nonzeroElements using 2
    · simp only [Z]
      congr
    · simp
    · simp only [S, card_nonzeroElements_inter]
  have hM : (2 : ℝ) ^ (n * k) ≤ 2 ^ (k ^ 2 + k) * #ℋ := by
    exact_mod_cast two_pow_le_two_pow_mul_card_finrank_eq hkn
  have hS : (n : ℝ) * 2 ^ (2 * (k ^ 2 + k)) * S ≤ 2 ^ (2 * (n * k)) :=
    mul_sum_sum_two_pow_sub_one_le hk hkn'
  have hZ' : (Z : ℝ) * n ≤ 2 ^ 2 ^ n := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 ^ (2 * (n * k)))
    calc (Z : ℝ) * n * 2 ^ (2 * (n * k))
        ≤ Z * n * (2 ^ (k ^ 2 + k) * #ℋ) ^ 2 := by
          rw [mul_comm 2, pow_mul]
          gcongr
      _ = n * 2 ^ (2 * (k ^ 2 + k)) * (Z * (#ℋ : ℝ) ^ 2) := by ring
      _ ≤ n * 2 ^ (2 * (k ^ 2 + k)) * (2 ^ 2 ^ n * S) := by gcongr
      _ = 2 ^ 2 ^ n * (n * 2 ^ (2 * (k ^ 2 + k)) * S) := by ring
      _ ≤ 2 ^ 2 ^ n * 2 ^ (2 * (n * k)) := by gcongr
  rw [le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_cliqueNum_lt_le_card_forall_not_subset hlog) (Nat.cast_nonneg n)).trans
      hZ'

/-- **Proposition 27** of Green. The proportion of the sets `A ⊆ 𝔽₂ⁿ` whose Cayley graph has
clique number at least `n * log₂ n / 4` tends to `1`. -/
theorem tendsto_card_le_cliqueNum_addCayley :
    Tendsto (fun n : ℕ ↦ (#{A : Finset (Fin n → ZMod 2) |
      n * Real.logb 2 n / 4 ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum} : ℝ) / 2 ^ 2 ^ n)
      atTop (𝓝 1) := by
  have hcompl (n : ℕ) : (#{A : Finset (Fin n → ZMod 2) |
      n * Real.logb 2 n / 4 ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum} : ℝ) =
      2 ^ 2 ^ n - #{A : Finset (Fin n → ZMod 2) |
        (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * Real.logb 2 n / 4} := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Finset (Fin n → ZMod 2))))
      fun A ↦ n * Real.logb 2 n / 4 ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum
    simp only [not_le, card_univ, Fintype.card_finset, Fintype.card_fun, Fintype.card_fin,
      ZMod.card] at this
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n : ℕ ↦ 1 - 1 / (n : ℝ))
    (h := fun _ ↦ 1) ?_ tendsto_const_nhds ?_ ?_
  · simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
  · filter_upwards [eventually_ge_atTop (2 ^ 16)] with n hn
    rw [hcompl, sub_div, div_self (by positivity), one_div]
    gcongr
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div]
    exact card_cliqueNum_addCayley_lt_le hn
  · filter_upwards with n
    rw [hcompl, div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) #{A : Finset (Fin n → ZMod 2) |
      (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * Real.logb 2 n / 4}]

end CountingSetsWithSmallSumset
