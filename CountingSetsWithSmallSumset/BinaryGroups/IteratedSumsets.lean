/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Sums of distinct elements of an affinely independent set

Let `X` be an affinely independent subset of a finite set `A` in a vector space. Two sets of `h`
elements of `X` with the same sum have the same indicator function, so the `C(|X|, h)` sums of `h`
distinct elements of `X` are distinct elements of the `h`-fold sumset `hA`. Together with
`(|X|/h)^h ≤ C(|X|, h)` and the Plünnecke–Ruzsa inequality `|hA| ≤ (|A + A|/|A|)^h |A|` this
bounds `|X|`. This is the counting step in the proof of Lemma 25 of Green, *Counting sets with
small sumset, and the clique number of random Cayley graphs*.

## Main statements

* `sum_mem_nsmul`: the sum of the elements of an `h`-element subset of `A` lies in `hA`.
* `choose_card_le_card_nsmul`: `C(|X|, h) ≤ |hA|` for an affinely independent `X ⊆ A`.
* `pow_le_pow_mul_choose`: `x ^ h ≤ h ^ h C(x, h)` for `h ≤ x`.
* `card_pow_le_of_affineIndependent`: `|X| ^ h ≤ h ^ h (|A + A|/|A|)^h |A|` for an affinely
  independent `X ⊆ A` with `h ≤ |X|`.
-/

public section

namespace CountingSetsWithSmallSumset

open Finset
open scoped Pointwise

/-- The sum of the elements of a subset `s` of `A` lies in the `|s|`-fold sumset of `A`. -/
lemma sum_mem_nsmul {G : Type*} [AddCommMonoid G] [DecidableEq G] {A s : Finset G}
    (hs : s ⊆ A) : ∑ x ∈ s, x ∈ #s • A := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, succ_nsmul']
    exact add_mem_add (hs (mem_insert_self a s)) (ih ((subset_insert a s).trans hs))

/-- `x ^ h ≤ h ^ h C(x, h)` when `h ≤ x`, that is, `(x/h)^h ≤ C(x, h)`. -/
lemma pow_le_pow_mul_choose {x h : ℕ} (hhx : h ≤ x) : x ^ h ≤ h ^ h * x.choose h := by
  refine Nat.le_of_mul_le_mul_right ?_ h.factorial_pos
  have hprod (y : ℕ) (f : ℕ → ℕ) : y ^ h * ∏ i ∈ range h, f i = ∏ i ∈ range h, y * f i := by
    rw [prod_mul_distrib, prod_const, card_range]
  rw [mul_assoc, mul_comm (x.choose h), ← Nat.descFactorial_eq_factorial_mul_choose,
    ← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
    hprod, hprod]
  refine prod_le_prod ?_
  intro i hi
  have hih : i < h := mem_range.1 hi
  zify [hih.le, (hih.trans_le hhx).le]
  nlinarith

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The sums of the `h`-element subsets of an affinely independent set are distinct. -/
lemma injOn_sum_powersetCard {X : Finset V} (hX : AffineIndependent F ((↑) : X → V)) (h : ℕ) :
    Set.InjOn (fun s ↦ ∑ x ∈ s, x) (X.powersetCard h : Set (Finset V)) := by
  classical
  intro s hs t ht hst
  obtain ⟨hsX, rfl⟩ := mem_powersetCard.1 hs
  obtain ⟨htX, hts⟩ := mem_powersetCard.1 ht
  have hw := hX.eq_of_sum_eq_sum_subtype (w₁ := fun x ↦ if x ∈ s then (1 : F) else 0)
    (w₂ := fun x ↦ if x ∈ t then (1 : F) else 0)
    (by simp [inter_eq_right.2 hsX, inter_eq_right.2 htX, hts])
    (by simpa [ite_smul, sum_ite_mem, inter_eq_right.2 hsX, inter_eq_right.2 htX] using hst)
  ext x
  grind [hw x]

variable [DecidableEq V]

/-- If `X ⊆ A` is affinely independent, then `C(|X|, h) ≤ |hA|`. -/
lemma choose_card_le_card_nsmul {A X : Finset V} (hXA : X ⊆ A)
    (hX : AffineIndependent F ((↑) : X → V)) (h : ℕ) : (#X).choose h ≤ #(h • A) := by
  rw [← card_powersetCard]
  refine card_le_card_of_injOn _ ?_ (injOn_sum_powersetCard hX h)
  intro s hs
  obtain ⟨hsX, rfl⟩ := mem_powersetCard.1 hs
  exact sum_mem_nsmul (hsX.trans hXA)

/-- If `X ⊆ A` is affinely independent and `h ≤ |X|`, then
`|X| ^ h ≤ h ^ h (|A + A|/|A|)^h |A|`. -/
lemma card_pow_le_of_affineIndependent {A X : Finset V} (hA : A.Nonempty) (hXA : X ⊆ A)
    (hX : AffineIndependent F ((↑) : X → V)) {h : ℕ} (hh : h ≤ #X) :
    (#X : ℝ) ^ h ≤ h ^ h * ((#(A + A) / #A) ^ h * #A) := by
  refine le_trans (b := (h : ℝ) ^ h * #(h • A)) ?_ ?_
  · exact_mod_cast (pow_le_pow_mul_choose hh).trans
      (Nat.mul_le_mul_left _ (choose_card_le_card_nsmul hXA hX h))
  · gcongr
    simpa using (NNRat.cast_le (K := ℝ)).2 (pluennecke_ruzsa_inequality_nsmul_add hA A h)

end CountingSetsWithSmallSumset
