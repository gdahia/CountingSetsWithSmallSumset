/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Cayley sum graphs

The Cayley sum graph `G_A` of a subset `A` of an abelian group has an edge between distinct `x`
and `y` when `x + y ∈ A`. A finite set `X` spans a clique of `G_A` exactly when the restricted
sumset of `X` lies in `A`. In a group of exponent `2`, `x + y = y - x`, so `G_A` is the Cayley
graph `SimpleGraph.addCayley A`.

## Main definitions

* `cayleySumGraph A`: the Cayley sum graph of `A`.

## Main statements

* `isClique_cayleySumGraph_iff`: `X` is a clique of `G_A` if and only if `X ∔ X ⊆ A`.
* `compl_cayleySumGraph`: the complement of `G_A` is the Cayley sum graph of the complement of
  `A`.
* `cayleySumGraph_eq_addCayley`: in a group of exponent `2`, `G_A` is the Cayley graph of `A`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset SimpleGraph

variable {G : Type*}

/-- The Cayley sum graph of `A`: distinct `x` and `y` are adjacent when `x + y ∈ A`. -/
def cayleySumGraph [Add G] (A : Set G) : SimpleGraph G :=
  fromRel fun x y ↦ x + y ∈ A

lemma cayleySumGraph_adj [AddCommMagma G] {A : Set G} {x y : G} :
    (cayleySumGraph A).Adj x y ↔ x ≠ y ∧ x + y ∈ A := by
  simp [cayleySumGraph, add_comm y x]

lemma isClique_cayleySumGraph_iff [DecidableEq G] [AddCommMagma G] {A X : Finset G} :
    (cayleySumGraph (A : Set G)).IsClique (X : Set G) ↔ restrictedSumset X ⊆ A := by
  simp only [IsClique, Set.Pairwise, mem_coe, cayleySumGraph_adj, subset_iff,
    mem_restrictedSumset]
  grind

lemma compl_cayleySumGraph [AddCommMagma G] (A : Set G) :
    (cayleySumGraph A)ᶜ = cayleySumGraph Aᶜ := by
  ext x y
  simp only [compl_adj, cayleySumGraph_adj, Set.mem_compl_iff]
  tauto

lemma cayleySumGraph_eq_addCayley [AddCommGroup G] (hG : ∀ x : G, x + x = 0) (A : Set G) :
    cayleySumGraph A = addCayley A := by
  ext x y
  simp [cayleySumGraph_adj, addCayley_adj, neg_eq_of_add_eq_zero_left (hG _), add_comm y x]

end CountingSetsWithSmallSumset
