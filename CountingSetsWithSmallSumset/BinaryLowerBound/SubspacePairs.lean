/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pairs of subspaces of `𝔽₂ⁿ` with an intersection of given dimension

This file proves Lemma 28 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*: for `l ≤ k`, there are at most `2 ^ (n * (2 * k - l))` ordered pairs
`(H, H')` of `k`-dimensional subspaces of `𝔽₂ⁿ` with `dim (H ∩ H') = l`. Such a pair is
determined by `2 * k - l` vectors: `l` vectors spanning `H ∩ H'`, and `k - l` further vectors for
each of `H` and `H'`.

## Main statements

* `exists_sup_span_range_eq`: if `L ≤ H` and `dim H = dim L + d`, then `H` is spanned by `L` and
  `d` vectors.
* `card_finrank_inf_eq_le`: Lemma 28 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Module Submodule

/-- If `L ≤ H` and `dim H = dim L + d`, then `H` is spanned by `L` and `d` vectors. -/
lemma exists_sup_span_range_eq {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {L H : Submodule K V} (hLH : L ≤ H) {d : ℕ}
    (hd : finrank K L + d = finrank K H) : ∃ u : Fin d → V, L ⊔ span K (Set.range u) = H := by
  induction d generalizing L with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simp [eq_of_le_of_finrank_eq hLH hd]
  | succ d ih =>
    obtain ⟨x, hxH, hxL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hLH (by rintro rfl; grind))
    obtain ⟨u, hu⟩ := ih (L := L ⊔ span K {x}) (sup_le hLH (by simpa using hxH))
      (by rw [finrank_sup_span_singleton hxL]; grind)
    refine ⟨Fin.cons x u, ?_⟩
    rw [Fin.range_cons, span_insert, ← sup_assoc, hu]

/-- **Lemma 28** of Green. For `l ≤ k`, there are at most `2 ^ (n * (2 * k - l))` ordered pairs
of `k`-dimensional subspaces of `𝔽₂ⁿ` whose intersection has dimension `l`. -/
lemma card_finrank_inf_eq_le (n : ℕ) {k l : ℕ} (hl : l ≤ k) :
    #{(H, H') : Submodule (ZMod 2) (Fin n → ZMod 2) × Submodule (ZMod 2) (Fin n → ZMod 2) |
      finrank (ZMod 2) H = k ∧ finrank (ZMod 2) H' = k ∧ finrank (ZMod 2) ↥(H ⊓ H') = l} ≤
      2 ^ (n * (2 * k - l)) := by
  classical
  let f : (Fin l → Fin n → ZMod 2) × (Fin (k - l) → Fin n → ZMod 2) ×
      (Fin (k - l) → Fin n → ZMod 2) →
      Submodule (ZMod 2) (Fin n → ZMod 2) × Submodule (ZMod 2) (Fin n → ZMod 2) :=
    fun (w, u, v) ↦ (span (ZMod 2) (Set.range w) ⊔ span (ZMod 2) (Set.range u),
      span (ZMod 2) (Set.range w) ⊔ span (ZMod 2) (Set.range v))
  trans #(univ.image f)
  · apply card_le_card
    rintro ⟨H, H'⟩ hH
    obtain ⟨-, hH, hH', hHH'⟩ := mem_filter.1 hH
    obtain ⟨w, hw⟩ := exists_sup_span_range_eq (K := ZMod 2) (L := ⊥) (H := H ⊓ H') bot_le
      (d := l) (by simp [hHH'])
    obtain ⟨u, hu⟩ := exists_sup_span_range_eq (K := ZMod 2) (L := H ⊓ H') (H := H) inf_le_left
      (d := k - l) (by grind)
    obtain ⟨v, hv⟩ := exists_sup_span_range_eq (K := ZMod 2) (L := H ⊓ H') (H := H')
      inf_le_right (d := k - l) (by grind)
    rw [bot_sup_eq] at hw
    exact mem_image.mpr ⟨(w, u, v), mem_univ _, by simp [f, hw, hu, hv]⟩
  refine card_image_le.trans ?_
  simp only [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    ← pow_mul, ← pow_add]
  rw [(by grind : 2 * k - l = l + 2 * (k - l))]
  exact Nat.pow_le_pow_right (by grind) (by grind)

end CountingSetsWithSmallSumset
