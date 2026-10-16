/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Covers
import Mathlib.Algebra.BigOperators.Fin

/-!
# Additive relations of tuples

A relation of order `s` between the coordinates of a tuple `a : Fin t → G` is an equation
`a i₁ + ⋯ + a iₛ = a j₁ + ⋯ + a jₛ`. Following Section 3 of Green, *Counting sets with small
sumset, and the clique number of random Cayley graphs*, Freiman isomorphisms are described by
relations: two injective tuples that satisfy the same relations of order `s` have Freiman
isomorphic ranges, and a Freiman isomorphism of order `s` preserves the relations of order `s` of
a tuple in its domain.

## Main definitions

* `FreimanRelationIndex s t`: a pair of `s`-tuples of indices in `Fin t`, which stands for a
  relation of order `s`.
* `freimanRelationHolds a p`: the tuple `a` satisfies the relation `p`.

## Main statements

* `exists_isAddFreimanIso_range`, `freimanIsomorphic_of_freimanRelationHolds_iff`: injective
  tuples with the same relations of order `s` have Freiman isomorphic ranges.
* `freimanRelationHolds_comp_iff`: a Freiman isomorphism preserves relations.
* `freimanRelationHolds_pairSum_iff`: a Freiman isomorphism of order `2 * s` preserves the
  relations of order `s` of sums of pairs.
* `injective_of_freimanRelationHolds_iff`: a tuple with the same relations of positive order as an
  injective tuple is injective.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable {G H : Type*}

/-- A pair of `s`-tuples of indices in `Fin t`. The pair `(i, j)` stands for the relation
`a (i 1) + ⋯ + a (i s) = a (j 1) + ⋯ + a (j s)` between the coordinates of a tuple `a`. -/
abbrev FreimanRelationIndex (s t : ℕ) :=
  (Fin s → Fin t) × (Fin s → Fin t)

/-- The tuple `a` satisfies the relation `(i, j)`: the sum of the coordinates of `a` indexed by `i`
equals the sum of those indexed by `j`. -/
def freimanRelationHolds [AddCommMonoid G] {s t : ℕ} (a : Fin t → G) :
    FreimanRelationIndex s t → Prop :=
  fun (i, j) ↦ ∑ k, a (i k) = ∑ k, a (j k)

/-- A finite set of `t` elements is the range of an injective tuple of length `t`. -/
lemma exists_injective_range_eq {X : Finset G} {t : ℕ} (hX : #X = t) :
    ∃ a : Fin t → G, Function.Injective a ∧ Set.range a = X := by
  refine ⟨Subtype.val ∘ (X.equivFinOfCardEq hX).symm,
    Subtype.val_injective.comp (Equiv.injective _), ?_⟩
  rw [(X.equivFinOfCardEq hX).symm.surjective.range_comp, Subtype.range_coe]

/-- A multiset of `s` elements of the range of `a` lists the coordinates of `a` at `s` indices. -/
private lemma exists_eq_map_univ {s t : ℕ} {a : Fin t → G} {u : Multiset G}
    (hu : ∀ x ∈ u, x ∈ Set.range a) (hcard : u.card = s) :
    ∃ p : Fin s → Fin t, u = univ.val.map fun i ↦ a (p i) := by
  obtain rfl : u.toList.length = s := (Multiset.length_toList u).trans hcard
  choose p hp using fun i : Fin u.toList.length ↦
    hu u.toList[i.1] (Multiset.mem_toList.mp (List.getElem_mem i.2))
  refine ⟨p, ?_⟩
  rw [Fin.univ_val_map]
  simp only [hp, List.ofFn_getElem, Multiset.coe_toList]

variable [AddCommMonoid G] [AddCommMonoid H]

/-- Two injective tuples that satisfy the same relations of order `s` have ranges that are Freiman
isomorphic of order `s`. -/
lemma exists_isAddFreimanIso_range {s t : ℕ} {a : Fin t → G} {b : Fin t → H}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (h : ∀ p : FreimanRelationIndex s t, freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    ∃ f : G → H, IsAddFreimanIso s (Set.range a) (Set.range b) f := by
  obtain ⟨f, rfl⟩ : ∃ f : G → H, f ∘ a = b :=
    ⟨Function.extend a b 0, funext (ha.extend_apply b 0)⟩
  refine ⟨f, ?_, ?_⟩
  · rw [Set.range_comp]
    exact hb.injOn_range.bijOn_image
  · intro u v hu hv hucard hvcard
    obtain ⟨p, rfl⟩ := exists_eq_map_univ hu hucard
    obtain ⟨q, rfl⟩ := exists_eq_map_univ hv hvcard
    simpa only [Multiset.map_map, Function.comp_def, ← sum_eq_multiset_sum,
      freimanRelationHolds] using (h (p, q)).symm

/-- Two finite sets enumerated by injective tuples with the same relations of order `s` are
Freiman isomorphic of order `s`. -/
lemma freimanIsomorphic_of_freimanRelationHolds_iff {s t : ℕ} {A B : Finset G}
    {a b : Fin t → G} (ha : Function.Injective a) (hA : Set.range a = A)
    (hb : Function.Injective b) (hB : Set.range b = B)
    (h : ∀ p : FreimanRelationIndex s t, freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    FreimanIsomorphic s A B := by
  rw [FreimanIsomorphic, ← hA, ← hB]
  exact exists_isAddFreimanIso_range ha hb h

/-- A Freiman isomorphism of order `s` preserves the relations of order `s` of a tuple in its
domain. -/
lemma freimanRelationHolds_comp_iff {s t : ℕ} {A : Set G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso s A B f) {a : Fin t → G} (ha : ∀ i, a i ∈ A)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds (f ∘ a) p ↔ freimanRelationHolds a p := by
  obtain ⟨i, j⟩ := p
  simpa only [Multiset.map_map, Function.comp_def, ← sum_eq_multiset_sum,
    freimanRelationHolds] using hf.map_sum_eq_map_sum (s := univ.val.map fun k ↦ a (i k))
      (t := univ.val.map fun k ↦ a (j k)) (by simp [ha]) (by simp [ha]) (by simp) (by simp)

/-- A Freiman isomorphism `f` of order `2 * s` on a set containing the coordinates of `c₁` and
`c₂` preserves the relations of order `s` of the sums `c₁ i + c₂ i`. -/
lemma freimanRelationHolds_pairSum_iff {s t : ℕ} {A : Set G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso (2 * s) A B f) {c₁ c₂ : Fin t → G} (h₁ : ∀ i, c₁ i ∈ A)
    (h₂ : ∀ i, c₂ i ∈ A) (p : FreimanRelationIndex s t) :
    freimanRelationHolds (fun i ↦ f (c₁ i) + f (c₂ i)) p ↔ freimanRelationHolds (c₁ + c₂) p := by
  obtain ⟨i, j⟩ := p
  have hmem (k : Fin s → Fin t) :
      ∀ x ∈ (univ.val.map fun l ↦ c₁ (k l)) + univ.val.map fun l ↦ c₂ (k l), x ∈ A := by
    simp only [Multiset.mem_add, Multiset.mem_map, mem_val, mem_univ, true_and]
    grind
  simpa only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
    ← sum_eq_multiset_sum, freimanRelationHolds, Pi.add_apply, sum_add_distrib] using
    hf.map_sum_eq_map_sum (hmem i) (hmem j) (by simp [two_mul]) (by simp [two_mul])

/-- A tuple that satisfies the same relations of order `n + 1` as an injective tuple is
injective. -/
lemma injective_of_freimanRelationHolds_iff {G : Type*} [AddCancelCommMonoid G] {n t : ℕ}
    {a : Fin t → G} {b : Fin t → H} (ha : Function.Injective a)
    (h : ∀ p : FreimanRelationIndex (n + 1) t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    Function.Injective b := by
  intro i j hij
  have hp := (h (Fin.cons i fun _ ↦ j, fun _ ↦ j)).mpr
    (by simp [freimanRelationHolds, Fin.sum_univ_succ, hij, succ_nsmul'])
  simp only [freimanRelationHolds, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hp
  exact ha (add_right_cancel hp)

end CountingSetsWithSmallSumset
