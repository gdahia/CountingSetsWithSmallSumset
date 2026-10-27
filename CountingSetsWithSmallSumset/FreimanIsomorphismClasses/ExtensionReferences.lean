/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Relations
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring.RingNF

/-!
# Extension references

This file contains the coding argument of Lemma 16 of Green, *Counting sets with small sumset,
and the clique number of random Cayley graphs*. Let `a` be a tuple of length `l + d` in a
cancellative commutative monoid. The shape of a relation `a i₁ + a i₂ = a j₁ + a j₂` records which
of its four indices are among the first `l` indices, and which of the last `d` indices the others
are. If two relations of the same shape hold, the difference of their parts on the first `l`
coordinates is a relation with four terms on each side between the first `l` coordinates. So the
relations with two terms on each side of `a` are determined by the relations with four terms on
each side of its first `l` coordinates and by one relation of each shape, if there is one. This
choice of one relation of each shape, the reference relation of that shape, is the extension
reference of `a`.

## Main definitions

* `ExtensionShape d`: the shape of a relation with two terms on each side.
* `extensionBaseTuple a`: the first `l` coordinates of a tuple of length `l + d`.
* `extensionReference a`: for each shape, a reference relation of that shape satisfied by `a`, if
  there is one.

## Main statements

* `freimanRelationHolds_iff_of_extensionReference_eq`: two tuples of length `l + d` with the same
  extension reference, whose first `l` coordinates satisfy the same relations with four terms on
  each side, satisfy the same relations with two terms on each side.
* `card_extensionReferenceType`: there are `(1 + l ^ 4) ^ ((d + 1) ^ 4)` extension references.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

noncomputable section

variable {G : Type*} [AddCancelCommMonoid G] {l d : ℕ}

/-- The position of an index of `Fin (l + d)` relative to the first `l` indices: `Sum.inl ()`
for one of the first `l` indices and `Sum.inr j` for the `j`-th of the last `d` indices. -/
abbrev ExtensionSlot (d : ℕ) := Unit ⊕ Fin d

/-- The positions of the four indices of a relation with two summands on each side. -/
abbrev ExtensionShape (d : ℕ) :=
  (Fin 2 → ExtensionSlot d) × (Fin 2 → ExtensionSlot d)

private def extensionSlot (i : Fin (l + d)) : ExtensionSlot d :=
  (finSumFinEquiv.symm i).map (fun _ ↦ ()) id

/-- The index itself if it is one of the first `l` indices, and `i₀` otherwise. -/
private def extensionBaseIndex (i₀ : Fin l) (i : Fin (l + d)) : Fin l :=
  (finSumFinEquiv.symm i).elim id fun _ ↦ i₀

/-- The index in the position `slot`, taken to be `b` if the position is among the first `l`. -/
private def extensionIndex (slot : ExtensionSlot d) (b : Fin l) : Fin (l + d) :=
  finSumFinEquiv (slot.elim (fun _ ↦ Sum.inl b) Sum.inr)

private lemma extensionIndex_extensionSlot (i₀ : Fin l) (i : Fin (l + d)) :
    extensionIndex (extensionSlot i) (extensionBaseIndex i₀ i) = i := by
  obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective i
  cases z <;> simp [extensionIndex, extensionSlot, extensionBaseIndex]

private lemma extensionSlot_extensionIndex (slot : ExtensionSlot d) (b : Fin l) :
    extensionSlot (extensionIndex slot b) = slot := by
  cases slot <;> simp [extensionIndex, extensionSlot]

private def extensionShape : FreimanRelationIndex 2 (l + d) → ExtensionShape d :=
  fun (i, j) ↦ (extensionSlot ∘ i, extensionSlot ∘ j)

private def extensionBasePart (i₀ : Fin l) :
    FreimanRelationIndex 2 (l + d) → FreimanRelationIndex 2 l :=
  fun (i, j) ↦ (extensionBaseIndex i₀ ∘ i, extensionBaseIndex i₀ ∘ j)

private def extensionRelation :
    ExtensionShape d → FreimanRelationIndex 2 l → FreimanRelationIndex 2 (l + d) :=
  fun (u, v) (w₁, w₂) ↦ (fun k ↦ extensionIndex (u k) (w₁ k), fun k ↦ extensionIndex (v k) (w₂ k))

private lemma extensionRelation_shape_basePart (i₀ : Fin l) (p : FreimanRelationIndex 2 (l + d)) :
    extensionRelation (extensionShape p) (extensionBasePart i₀ p) = p := by
  obtain ⟨i, j⟩ := p
  simp [extensionRelation, extensionShape, extensionBasePart, extensionIndex_extensionSlot]

private lemma extensionShape_extensionRelation (shape : ExtensionShape d)
    (part : FreimanRelationIndex 2 l) :
    extensionShape (extensionRelation shape part) = shape := by
  obtain ⟨u, v⟩ := shape
  obtain ⟨w₁, w₂⟩ := part
  simp [extensionShape, extensionRelation, Function.comp_def, extensionSlot_extensionIndex]

private noncomputable instance extensionReferenceLinearOrder (l : ℕ) :
    LinearOrder (FreimanRelationIndex 2 l) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

private noncomputable def extensionReferenceCandidates (a : Fin (l + d) → G)
    (shape : ExtensionShape d) :
    Finset (FreimanRelationIndex 2 l) := by
  classical
  exact univ.filter fun part ↦ freimanRelationHolds a (extensionRelation shape part)

/-- For each shape, the least relation on the first `l` indices whose extension by the shape is
a relation satisfied by `a`, if there is one. -/
@[no_expose] noncomputable def extensionReference (a : Fin (l + d) → G) :
    ExtensionShape d → Option (FreimanRelationIndex 2 l) :=
  fun shape ↦ if h : (extensionReferenceCandidates a shape).Nonempty then
    some ((extensionReferenceCandidates a shape).min' h) else none

private lemma mem_extensionReferenceCandidates {a : Fin (l + d) → G} {shape : ExtensionShape d}
    {part : FreimanRelationIndex 2 l} :
    part ∈ extensionReferenceCandidates a shape ↔
      freimanRelationHolds a (extensionRelation shape part) := by
  simp [extensionReferenceCandidates]

private lemma freimanRelationHolds_of_extensionReference_eq_some {a : Fin (l + d) → G}
    {shape : ExtensionShape d} {ref : FreimanRelationIndex 2 l}
    (href : extensionReference a shape = some ref) :
    freimanRelationHolds a (extensionRelation shape ref) := by
  unfold extensionReference at href
  split at href <;> cases href
  exact mem_extensionReferenceCandidates.mp (min'_mem _ _)

private lemma exists_extensionReference_eq_some (i₀ : Fin l) {a : Fin (l + d) → G}
    {p : FreimanRelationIndex 2 (l + d)} (hp : freimanRelationHolds a p) :
    ∃ ref, extensionReference a (extensionShape p) = some ref := by
  rw [← extensionRelation_shape_basePart i₀ p, ← mem_extensionReferenceCandidates] at hp
  exact ⟨_, dite_eq_left ⟨_, hp⟩⟩

/-- There are `(1 + l ^ 4) ^ ((d + 1) ^ 4)` extension references. -/
lemma card_extensionReferenceType (l d : ℕ) :
    Fintype.card (ExtensionShape d → Option (FreimanRelationIndex 2 l)) =
      (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_option, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_fin]
  ring

/-- The first `l` coordinates of a tuple of length `l + d`. -/
def extensionBaseTuple (a : Fin (l + d) → G) : Fin l → G :=
  fun i ↦ a (finSumFinEquiv (Sum.inl i))

private lemma add_extensionBaseTuple_eq_of_extensionSlot_eq (i₀ : Fin l) (a : Fin (l + d) → G)
    {i j : Fin (l + d)}
    (hslot : extensionSlot i = extensionSlot j) :
    a i + extensionBaseTuple a (extensionBaseIndex i₀ j) =
      a j + extensionBaseTuple a (extensionBaseIndex i₀ i) := by
  obtain ⟨si, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨sj, rfl⟩ := finSumFinEquiv.surjective j
  obtain i | i := si <;> obtain j | j := sj <;>
    simp_all [extensionSlot, extensionBaseIndex, extensionBaseTuple, add_comm]

/-- The relation on the first `l` coordinates that compares two relations of the same shape. -/
private def extensionComparison (i₀ : Fin l) :
    FreimanRelationIndex 2 (l + d) → FreimanRelationIndex 2 (l + d) → FreimanRelationIndex 4 l :=
  fun (p₁, p₂) (q₁, q₂) ↦ (Fin.append (extensionBaseIndex i₀ ∘ p₁) (extensionBaseIndex i₀ ∘ q₂),
    Fin.append (extensionBaseIndex i₀ ∘ p₂) (extensionBaseIndex i₀ ∘ q₁))

/-- For two relations of the same shape, the comparison relation on the first `l` coordinates
holds exactly when the sum of one relation and the reverse of the other holds. -/
private lemma freimanRelationHolds_extensionComparison_iff (i₀ : Fin l) (a : Fin (l + d) → G)
    {p₁ p₂ q₁ q₂ : Fin 2 → Fin (l + d)}
    (hshape : extensionShape (p₁, p₂) = extensionShape (q₁, q₂)) :
    freimanRelationHolds (extensionBaseTuple a) (extensionComparison i₀ (p₁, p₂) (q₁, q₂)) ↔
      a (p₁ 0) + a (p₁ 1) + (a (q₂ 0) + a (q₂ 1)) =
        a (p₂ 0) + a (p₂ 1) + (a (q₁ 0) + a (q₁ 1)) := by
  simp only [extensionShape, Prod.mk.injEq, funext_iff, Function.comp_apply] at hshape
  obtain ⟨h₁, h₂⟩ := hshape
  have hl (k : Fin 2) := add_extensionBaseTuple_eq_of_extensionSlot_eq i₀ a (h₁ k)
  have hr (k : Fin 2) := add_extensionBaseTuple_eq_of_extensionSlot_eq i₀ a (h₂ k)
  rw [freimanRelationHolds, ← (finSumFinEquiv (m := 2) (n := 2)).sum_comp,
    ← (finSumFinEquiv (m := 2) (n := 2)).sum_comp]
  simp only [extensionComparison, Fintype.sum_sum_type, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right, Fin.append_left, Fin.append_right, Function.comp_apply,
    Fin.sum_univ_two]
  grind

private lemma freimanRelationHolds_of_extensionReference_eq (i₀ : Fin l) {a b : Fin (l + d) → G}
    (hrefs : extensionReference a = extensionReference b)
    (hbase : ∀ r : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) r →
        freimanRelationHolds (extensionBaseTuple b) r)
    {p : FreimanRelationIndex 2 (l + d)} (hp : freimanRelationHolds a p) :
    freimanRelationHolds b p := by
  obtain ⟨ref, href⟩ := exists_extensionReference_eq_some i₀ hp
  have hqa := freimanRelationHolds_of_extensionReference_eq_some href
  have hqb := freimanRelationHolds_of_extensionReference_eq_some (hrefs ▸ href)
  have hshape := extensionShape_extensionRelation (extensionShape p) ref
  generalize extensionRelation (extensionShape p) ref = q at hqa hqb hshape
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  have hcomparison := hbase (extensionComparison i₀ (p₁, p₂) (q₁, q₂))
  rw [freimanRelationHolds_extensionComparison_iff i₀ a hshape.symm,
    freimanRelationHolds_extensionComparison_iff i₀ b hshape.symm] at hcomparison
  simp only [freimanRelationHolds, Fin.sum_univ_two] at hp hqa hqb ⊢
  grind

/-- Two tuples of length `l + d` with the same extension reference, whose first `l` coordinates
satisfy the same relations with four summands, satisfy the same relations with two summands. -/
lemma freimanRelationHolds_iff_of_extensionReference_eq (i₀ : Fin l) {a b : Fin (l + d) → G}
    (hrefs : extensionReference a = extensionReference b)
    (hbase : ∀ p : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) p ↔
        freimanRelationHolds (extensionBaseTuple b) p)
    (p : FreimanRelationIndex 2 (l + d)) :
    freimanRelationHolds a p ↔ freimanRelationHolds b p :=
  ⟨freimanRelationHolds_of_extensionReference_eq i₀ hrefs fun r ↦ (hbase r).mp,
    freimanRelationHolds_of_extensionReference_eq i₀ hrefs.symm fun r ↦ (hbase r).mpr⟩

end

end CountingSetsWithSmallSumset
