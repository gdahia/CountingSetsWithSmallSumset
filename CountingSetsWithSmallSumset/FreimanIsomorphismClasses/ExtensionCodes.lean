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
import Mathlib.Tactic.Ring

/-!
# Extension codes

This file contains the coding argument of Lemma 16 of Green, *Counting sets with small sumset,
and the clique number of random Cayley graphs*. Let `a` be a tuple of length `l + d` in a
commutative monoid with cancellation. The shape of a relation `a i + a j = a k + a l` records
which of its four indices are among the first `l` and which of the last `d` indices the others
are. If two relations of the same shape hold, the difference of their parts on the first `l`
coordinates is a relation with four terms on each side between the first `l` coordinates. So the
relations with two terms on each side of `a` are determined by the relations with four terms on
each side of its first `l` coordinates and by one relation of each shape, if there is one. This is
the extension code of `a`.

## Main definitions

* `ExtensionShape d`: the shape of a relation with two terms on each side.
* `extensionBaseTuple a`: the first `l` coordinates of a tuple of length `l + d`.
* `extensionCode a`: for each shape, a relation of that shape satisfied by `a`, if there is one.

## Main statements

* `freimanRelationHolds_iff_of_extensionCode_eq`: two tuples of length `l + d` with the same
  extension code, whose first `l` coordinates satisfy the same relations with four terms on each
  side, satisfy the same relations with two terms on each side.
* `card_extensionCodeType`: there are `(1 + l ^ 4) ^ ((d + 1) ^ 4)` extension codes.
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

private def extensionBaseWitness (i₀ : Fin l) :
    FreimanRelationIndex 2 (l + d) → FreimanRelationIndex 2 l :=
  fun (i, j) ↦ (extensionBaseIndex i₀ ∘ i, extensionBaseIndex i₀ ∘ j)

private def extensionRelation :
    ExtensionShape d → FreimanRelationIndex 2 l → FreimanRelationIndex 2 (l + d) :=
  fun (u, v) (w₁, w₂) ↦ (fun k ↦ extensionIndex (u k) (w₁ k), fun k ↦ extensionIndex (v k) (w₂ k))

private lemma extensionRelation_shape_witness (i₀ : Fin l) (p : FreimanRelationIndex 2 (l + d)) :
    extensionRelation (extensionShape p) (extensionBaseWitness i₀ p) = p := by
  obtain ⟨i, j⟩ := p
  simp [extensionRelation, extensionShape, extensionBaseWitness, extensionIndex_extensionSlot]

private lemma extensionShape_extensionRelation (shape : ExtensionShape d)
    (witness : FreimanRelationIndex 2 l) :
    extensionShape (extensionRelation shape witness) = shape := by
  obtain ⟨u, v⟩ := shape
  obtain ⟨w₁, w₂⟩ := witness
  simp [extensionShape, extensionRelation, Function.comp_def, extensionSlot_extensionIndex]

private noncomputable instance extensionWitnessLinearOrder (l : ℕ) :
    LinearOrder (FreimanRelationIndex 2 l) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

private noncomputable def extensionWitnesses (a : Fin (l + d) → G) (shape : ExtensionShape d) :
    Finset (FreimanRelationIndex 2 l) := by
  classical
  exact univ.filter fun witness ↦ freimanRelationHolds a (extensionRelation shape witness)

/-- For each shape, the least relation on the first `l` indices whose extension by the shape is
a relation satisfied by `a`, if there is one. -/
@[no_expose] noncomputable def extensionCode (a : Fin (l + d) → G) :
    ExtensionShape d → Option (FreimanRelationIndex 2 l) :=
  fun shape ↦ if h : (extensionWitnesses a shape).Nonempty then
    some ((extensionWitnesses a shape).min' h) else none

private lemma mem_extensionWitnesses {a : Fin (l + d) → G} {shape : ExtensionShape d}
    {witness : FreimanRelationIndex 2 l} :
    witness ∈ extensionWitnesses a shape ↔
      freimanRelationHolds a (extensionRelation shape witness) := by
  simp [extensionWitnesses]

private lemma freimanRelationHolds_of_extensionCode_eq_some {a : Fin (l + d) → G}
    {shape : ExtensionShape d} {witness : FreimanRelationIndex 2 l}
    (hcode : extensionCode a shape = some witness) :
    freimanRelationHolds a (extensionRelation shape witness) := by
  unfold extensionCode at hcode
  split at hcode <;> cases hcode
  exact mem_extensionWitnesses.mp (min'_mem _ _)

private lemma exists_extensionCode_eq_some (i₀ : Fin l) {a : Fin (l + d) → G}
    {p : FreimanRelationIndex 2 (l + d)} (hp : freimanRelationHolds a p) :
    ∃ witness, extensionCode a (extensionShape p) = some witness := by
  rw [← extensionRelation_shape_witness i₀ p, ← mem_extensionWitnesses] at hp
  exact ⟨_, dite_eq_left ⟨_, hp⟩⟩

/-- There are `(1 + l ^ 4) ^ ((d + 1) ^ 4)` extension codes. -/
lemma card_extensionCodeType (l d : ℕ) :
    Fintype.card (ExtensionShape d → Option (FreimanRelationIndex 2 l)) =
      (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
  simp [FreimanRelationIndex]
  ring

/-- The first `l` coordinates of a tuple of length `l + d`. -/
def extensionBaseTuple (a : Fin (l + d) → G) : Fin l → G :=
  fun i ↦ a (finSumFinEquiv (Sum.inl i))

private lemma extensionSlot_add_base_eq (i₀ : Fin l) (a : Fin (l + d) → G) {i j : Fin (l + d)}
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
  have hl (k : Fin 2) := extensionSlot_add_base_eq i₀ a (h₁ k)
  have hr (k : Fin 2) := extensionSlot_add_base_eq i₀ a (h₂ k)
  rw [freimanRelationHolds, ← (finSumFinEquiv (m := 2) (n := 2)).sum_comp,
    ← (finSumFinEquiv (m := 2) (n := 2)).sum_comp]
  simp only [extensionComparison, Fintype.sum_sum_type, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right, Fin.append_left, Fin.append_right, Function.comp_apply,
    Fin.sum_univ_two]
  grind

private lemma freimanRelationHolds_of_extensionCode_eq (i₀ : Fin l) {a b : Fin (l + d) → G}
    (hcode : extensionCode a = extensionCode b)
    (hbase : ∀ r : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) r →
        freimanRelationHolds (extensionBaseTuple b) r)
    {p : FreimanRelationIndex 2 (l + d)} (hp : freimanRelationHolds a p) :
    freimanRelationHolds b p := by
  obtain ⟨witness, hwitness⟩ := exists_extensionCode_eq_some i₀ hp
  have hqa := freimanRelationHolds_of_extensionCode_eq_some hwitness
  have hqb := freimanRelationHolds_of_extensionCode_eq_some (hcode ▸ hwitness)
  have hshape := extensionShape_extensionRelation (extensionShape p) witness
  generalize extensionRelation (extensionShape p) witness = q at hqa hqb hshape
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  have hcomparison := hbase (extensionComparison i₀ (p₁, p₂) (q₁, q₂))
  rw [freimanRelationHolds_extensionComparison_iff i₀ a hshape.symm,
    freimanRelationHolds_extensionComparison_iff i₀ b hshape.symm] at hcomparison
  simp only [freimanRelationHolds, Fin.sum_univ_two] at hp hqa hqb ⊢
  grind

/-- Two tuples of length `l + d` with the same extension code, whose first `l` coordinates
satisfy the same relations with four summands, satisfy the same relations with two summands. -/
lemma freimanRelationHolds_iff_of_extensionCode_eq (i₀ : Fin l) {a b : Fin (l + d) → G}
    (hcode : extensionCode a = extensionCode b)
    (hbase : ∀ p : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) p ↔
        freimanRelationHolds (extensionBaseTuple b) p)
    (p : FreimanRelationIndex 2 (l + d)) :
    freimanRelationHolds a p ↔ freimanRelationHolds b p :=
  ⟨freimanRelationHolds_of_extensionCode_eq i₀ hcode fun r ↦ (hbase r).mp,
    freimanRelationHolds_of_extensionCode_eq i₀ hcode.symm fun r ↦ (hbase r).mpr⟩

end

end CountingSetsWithSmallSumset
