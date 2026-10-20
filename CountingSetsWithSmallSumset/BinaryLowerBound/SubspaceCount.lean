/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The number of subspaces of `𝔽₂ⁿ` of a given dimension

A subspace `H` of `𝔽₂ⁿ` has `2 ^ dim H` elements. For `k ≤ n`, the number `M` of `k`-dimensional
subspaces of `𝔽₂ⁿ` satisfies `2 ^ (n * k) ≤ 2 ^ (k ^ 2 + k) * M`. Indeed, there are
`(2 ^ n - 1) (2 ^ n - 2) ⋯ (2 ^ n - 2 ^ (k - 1)) ≥ 2 ^ ((n - 1) * k)` linearly independent
`k`-tuples, and at most `2 ^ (k ^ 2)` of them span a given subspace.

## Main statements

* `card_filter_mem_submodule`: a subspace `H` of `𝔽₂ⁿ` has `2 ^ dim H` elements.
* `two_pow_le_two_pow_mul_card_linearIndependent`: the lower bound for the number of linearly
  independent `k`-tuples.
* `two_pow_le_two_pow_mul_card_finrank_eq`: the lower bound for the number of `k`-dimensional
  subspaces.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Module Submodule

/-- A subspace `H` of `𝔽₂ⁿ` has `2 ^ dim H` elements. -/
lemma card_filter_mem_submodule {n : ℕ} (H : Submodule (ZMod 2) (Fin n → ZMod 2))
    [DecidablePred (· ∈ H)] : #{x | x ∈ H} = 2 ^ finrank (ZMod 2) H := by
  rw [← Fintype.card_subtype, card_eq_pow_finrank (K := ZMod 2) (V := H), ZMod.card]

/-- For `k ≤ n`, the number `L` of linearly independent `k`-tuples of vectors of `𝔽₂ⁿ` satisfies
`2 ^ (n * k) ≤ 2 ^ k * L`. -/
lemma two_pow_le_two_pow_mul_card_linearIndependent {n k : ℕ} (hk : k ≤ n)
    [DecidablePred fun v : Fin k → Fin n → ZMod 2 ↦ LinearIndependent (ZMod 2) v] :
    2 ^ (n * k) ≤ 2 ^ k * #{v : Fin k → Fin n → ZMod 2 | LinearIndependent (ZMod 2) v} := by
  have hLI : #{v : Fin k → Fin n → ZMod 2 | LinearIndependent (ZMod 2) v} =
      ∏ i : Fin k, (2 ^ n - 2 ^ (i : ℕ)) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using
      card_linearIndependent (K := ZMod 2) (V := Fin n → ZMod 2) (k := k) (by simpa)
  rw [hLI, (by simp [pow_mul] : 2 ^ (n * k) = ∏ _ : Fin k, 2 ^ n),
    (by simp : 2 ^ k = ∏ _ : Fin k, 2), ← prod_mul_distrib]
  apply prod_le_prod
  intro i _
  grind [pow_succ, Nat.pow_le_pow_right two_pos (i.isLt.trans_le hk : (i : ℕ) + 1 ≤ n)]

/-- For `k ≤ n`, the number `M` of `k`-dimensional subspaces of `𝔽₂ⁿ` satisfies
`2 ^ (n * k) ≤ 2 ^ (k ^ 2 + k) * M`. -/
lemma two_pow_le_two_pow_mul_card_finrank_eq {n k : ℕ} (hk : k ≤ n) :
    2 ^ (n * k) ≤
      2 ^ (k ^ 2 + k) * #{H : Submodule (ZMod 2) (Fin n → ZMod 2) | finrank (ZMod 2) H = k} := by
  classical
  refine (two_pow_le_two_pow_mul_card_linearIndependent hk).trans ?_
  set LI : Finset (Fin k → Fin n → ZMod 2) := {v | LinearIndependent (ZMod 2) v}
  rw [pow_add, mul_comm (2 ^ (k ^ 2)), mul_assoc]
  refine Nat.mul_le_mul_left _ ((card_le_mul_card_image
    (f := fun v ↦ span (ZMod 2) (Set.range v)) LI (2 ^ (k ^ 2)) ?_).trans ?_)
  · intro H hH
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hH
    obtain ⟨-, hv⟩ := mem_filter.mp hv
    trans #(Fintype.piFinset fun _ : Fin k ↦ ({x | x ∈ span (ZMod 2) (Set.range v)} : Finset _))
    · apply card_le_card
      intro w hw
      obtain ⟨-, hw⟩ := mem_filter.mp hw
      rw [Fintype.mem_piFinset]
      intro i
      simpa [← hw] using subset_span (Set.mem_range_self i)
    simp [card_filter_mem_submodule, finrank_span_eq_card hv, ← pow_mul, sq]
  · refine Nat.mul_le_mul_left _ (card_le_card ?_)
    intro H hH
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hH
    obtain ⟨-, hv⟩ := mem_filter.mp hv
    simp [finrank_span_eq_card hv]

end CountingSetsWithSmallSumset
