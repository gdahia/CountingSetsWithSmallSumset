/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Data.Fintype.Powerset

/-!
# Sets with a given size and a given size of restricted sumset

For a finite group `Γ`, `S_k^m(Γ)` is the family of the sets `X ⊆ Γ` with `|X| = k` and
`|X ∔ X| = m`. This is Definition 3 of Green, *Counting sets with small sumset, and the clique
number of random Cayley graphs*. The family is empty when `m` exceeds the size of `Γ`.

## Main definitions

* `restrictedSumsetCardSets Γ k m`: the family `S_k^m(Γ)`.

## Main statements

* `restrictedSumsetCardSets_eq_empty`: `S_k^m(Γ)` is empty if `m > |Γ|`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable (Γ : Type*) [Fintype Γ] [DecidableEq Γ] [Add Γ]

/-- **Definition 3** of Green. `S_k^m(Γ)` is the family of the sets `X ⊆ Γ` with `|X| = k` and
`|X ∔ X| = m`. -/
def restrictedSumsetCardSets (k m : ℕ) : Finset (Finset Γ) :=
  {X | #X = k ∧ #(restrictedSumset X) = m}

variable {Γ}

lemma mem_restrictedSumsetCardSets {k m : ℕ} {X : Finset Γ} :
    X ∈ restrictedSumsetCardSets Γ k m ↔ #X = k ∧ #(restrictedSumset X) = m := by
  simp [restrictedSumsetCardSets]

lemma restrictedSumsetCardSets_eq_empty (k : ℕ) {m : ℕ} (hm : Fintype.card Γ < m) :
    restrictedSumsetCardSets Γ k m = ∅ := by
  ext X
  simp only [mem_restrictedSumsetCardSets, notMem_empty, iff_false, not_and]
  intro _ hX
  grind [card_le_univ (restrictedSumset X)]

end CountingSetsWithSmallSumset
