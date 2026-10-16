/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
import Mathlib.Algebra.Order.Chebyshev

/-!
# Summing quadruples

A summing quadruple of a finite set `B` is a pair `((a, b), (c, d))` of ordered pairs of distinct
elements of `B` with `a + b = c + d`. It is degenerate when `(c, d) = (a, b)` or
`(c, d) = (b, a)`, so there are `2 * #B.offDiag` degenerate summing quadruples. Write `M` for the
number of all summing quadruples. The Cauchy–Schwarz inequality gives
`#B.offDiag ^ 2 ≤ #(restrictedSumset B) * M`. In an additive commutative group a summing quadruple
is determined by its first three entries, so a set `A` has at most `#A ^ 3` non-degenerate summing
quadruples. These counts are used in the proof of Proposition 19 of Green, *Counting sets with
small sumset, and the clique number of random Cayley graphs*.

## Main definitions

* `summingQuadruples B`: the summing quadruples of `B`.
* `nondegenerateSummingQuadruples B`: the non-degenerate summing quadruples of `B`.

## Main statements

* `sq_card_offDiag_le_card_restrictedSumset_mul`: the bound
  `#B.offDiag ^ 2 ≤ #(restrictedSumset B) * (2 * #B.offDiag + #(nondegenerateSummingQuadruples B))`.
* `card_nondegenerateSummingQuadruples_le`: there are at most `#A ^ 3` non-degenerate summing
  quadruples.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable {G : Type*} [DecidableEq G]

/-- The summing quadruples of `B`: the pairs `((a, b), (c, d))` of ordered pairs of distinct
elements of `B` with `a + b = c + d`. -/
def summingQuadruples [Add G] (B : Finset G) : Finset ((G × G) × (G × G)) :=
  (B.offDiag ×ˢ B.offDiag).filter fun ((a, b), (c, d)) ↦ a + b = c + d

/-- The non-degenerate summing quadruples of `B`: the pairs `((a, b), (c, d))` of ordered pairs of
distinct elements of `B` with `a + b = c + d`, `(c, d) ≠ (a, b)` and `(c, d) ≠ (b, a)`. -/
def nondegenerateSummingQuadruples [Add G] (B : Finset G) : Finset ((G × G) × (G × G)) :=
  (B.offDiag ×ˢ B.offDiag).filter fun ((a, b), (c, d)) ↦
    a + b = c + d ∧ (c, d) ≠ (a, b) ∧ (c, d) ≠ (b, a)

private lemma sum_card_fiber_eq_card_offDiag [Add G] (B : Finset G) :
    ∑ x ∈ restrictedSumset B, #(B.offDiag.filter fun (a, b) ↦ a + b = x) = #B.offDiag := by
  rw [restrictedSumset_eq_image_offDiag, card_eq_sum_card_image fun ((a, b) : G × G) ↦ a + b]

private lemma sum_sq_card_fiber_eq_card_filter [Add G] (B : Finset G) :
    ∑ x ∈ restrictedSumset B, #(B.offDiag.filter fun (a, b) ↦ a + b = x) ^ 2 =
      #(summingQuadruples B) := by
  rw [summingQuadruples, card_eq_sum_card_fiberwise (f := fun ((a, b), _) ↦ a + b)
    (t := restrictedSumset B)]
  · congr with x
    rw [sq, ← card_product]
    congr 1
    ext ⟨⟨a, b⟩, c, d⟩
    simp only [mem_filter, mem_product]
    grind
  · rintro ⟨⟨a, b⟩, c, d⟩ h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_offDiag] at h
    exact mem_coe.mpr (mem_restrictedSumset.mpr ⟨a, by grind, b, by grind⟩)

private lemma card_filter_sum_eq_le [Add G] (B : Finset G) :
    #(summingQuadruples B) ≤
      2 * #B.offDiag + #(nondegenerateSummingQuadruples B) := by
  have hsub : summingQuadruples B ⊆
      (B.offDiag.image fun p ↦ (p, p)) ∪ (B.offDiag.image fun p ↦ (p, p.swap)) ∪
        nondegenerateSummingQuadruples B := by
    rintro ⟨⟨a, b⟩, c, d⟩ h
    simp only [summingQuadruples, mem_filter, mem_product, mem_offDiag] at h
    simp only [nondegenerateSummingQuadruples, mem_union, mem_image, mem_filter, mem_product,
      mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    grind
  grw [card_le_card hsub, card_union_le, card_union_le, card_image_le, card_image_le]
  grind

/-- The Cauchy–Schwarz bound for the restricted sumset in terms of summing quadruples. -/
lemma sq_card_offDiag_le_card_restrictedSumset_mul [Add G] (B : Finset G) :
    #B.offDiag ^ 2 ≤
      #(restrictedSumset B) * (2 * #B.offDiag + #(nondegenerateSummingQuadruples B)) := by
  have h := sq_sum_le_card_mul_sum_sq (s := restrictedSumset B)
    (f := fun x ↦ #(B.offDiag.filter fun (a, b) ↦ a + b = x))
  rw [sum_card_fiber_eq_card_offDiag, sum_sq_card_fiber_eq_card_filter, Nat.cast_id] at h
  grw [h, card_filter_sum_eq_le]

/-- A non-degenerate summing quadruple has four distinct entries. -/
lemma card_entries_eq_four_of_mem_nondegenerateSummingQuadruples [AddCommGroup G]
    {A : Finset G} {a b c d : G} (h : ((a, b), (c, d)) ∈ nondegenerateSummingQuadruples A) :
    #{a, b, c, d} = 4 := by
  simp only [nondegenerateSummingQuadruples, mem_filter, mem_product, mem_offDiag, ne_eq,
    Prod.mk.injEq] at h
  grind [card_insert_of_notMem, card_singleton]

/-- A set `A` has at most `#A ^ 3` non-degenerate summing quadruples. -/
lemma card_nondegenerateSummingQuadruples_le [AddCommGroup G] (A : Finset G) :
    #(nondegenerateSummingQuadruples A) ≤ #A ^ 3 := by
  rw [pow_succ, pow_two, ← card_product, ← card_product]
  refine card_le_card_of_injOn (fun ((a, b), (c, _)) ↦ ((a, b), c)) ?_ ?_
  · rintro ⟨⟨a, b⟩, c, d⟩ h
    simp only [nondegenerateSummingQuadruples, coe_filter, Set.mem_ofPred_eq, mem_product,
      mem_offDiag] at h
    simp only [coe_product, Set.mem_prod, mem_coe]
    grind
  · rintro ⟨⟨a, b⟩, c, d⟩ h ⟨⟨a', b'⟩, c', d'⟩ h' heq
    simp only [nondegenerateSummingQuadruples, coe_filter, Set.mem_ofPred_eq] at h h'
    simp only [Prod.mk.injEq] at heq ⊢
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    refine ⟨⟨rfl, rfl⟩, rfl, ?_⟩
    grind

end CountingSetsWithSmallSumset
