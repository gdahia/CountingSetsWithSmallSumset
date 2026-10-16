/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanDimension.HomSpace
public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import CountingSetsWithSmallSumset.BinaryGroups.IteratedSumsets
import CountingSetsWithSmallSumset.BinaryGroups.Sumsets
import CountingSetsWithSmallSumset.FreimanDimension.AffineModel
import CountingSetsWithSmallSumset.FreimanDimension.IsomorphicCopies
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The Freiman dimension of a subset of `𝔽₂^n` with small restricted sumset

Let `A` be a set of `k ≥ 2` elements of a vector space over `𝔽₂` with `|A ∔ A| ≤ m`. Then
`|A + A| ≤ m + 1`. Let `h = ⌊log₂ k⌋` and let `X ⊆ A` be an affinely independent set with the same
affine span as `A`, so that `|X|` is the affine dimension of `A` plus one. If `h ≤ |X|`, then the
sums of `h` distinct elements of `X` and the Plünnecke–Ruzsa inequality give
`(|X|/h)^h ≤ ((m + 1)/k)^h k`, and since `k ≤ (2 log₂ k / h)^h` this yields
`|X| ≤ 4 m log₂ k / k`. If `|X| < h`, the same bound holds because `k ≤ 4m`. By Corollary 14 of
Green, `A` is Freiman isomorphic to a set of affine dimension `r_{𝔽₂}(A)` with the same restricted
sumset size, so `r_{𝔽₂}(A) + 1 ≤ 4 m log₂ k / k`. This is Lemma 25 of Green, *Counting sets with
small sumset, and the clique number of random Cayley graphs*.

Together with the count of Freiman isomorphic copies, at most `(2 ^ n) ^ (4 m log₂ k / k)` subsets
of `𝔽₂^n` are Freiman isomorphic to `A`.

## Main statements

* `finrank_vectorSpan_add_one_le_of_card_restrictedSumset_le`: the affine dimension `d` of a set
  `A` of `k ≥ 2` elements of an `𝔽₂`-vector space with `|A ∔ A| ≤ m` satisfies
  `d + 1 ≤ 4 m log₂ k / k`.
* `freimanDimOver_add_one_le_of_card_restrictedSumset_le`: Lemma 25 of Green,
  `r_{𝔽₂}(A) + 1 ≤ 4 m log₂ k / k`.
* `ncard_isAddFreimanIso_le_of_card_restrictedSumset_le`: at most `(2 ^ n) ^ (4 m log₂ k / k)`
  subsets of `𝔽₂^n` are Freiman isomorphic of order `2` to such a set `A`.
-/

public section

namespace CountingSetsWithSmallSumset

open Finset Module Real

/-- `2 ^ t ≤ 2 t` for `1 ≤ t ≤ 2`. -/
private lemma two_rpow_le_two_mul {t : ℝ} (ht₁ : 1 ≤ t) (ht₂ : t ≤ 2) : (2 : ℝ) ^ t ≤ 2 * t := by
  have h := rpow_one_add_le_one_add_mul_self (s := 1) (p := t - 1) (by norm_num) (by linarith)
    (by linarith)
  rw [← sub_add_cancel t 1, rpow_add_one two_ne_zero]
  norm_num at h
  linarith

/-- `k ≤ (2 log₂ k / h) ^ h` for `h = ⌊log₂ k⌋ ≥ 1`. -/
private lemma le_two_mul_logb_div_log_pow {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ≤ (2 * logb 2 k / Nat.log 2 k) ^ Nat.log 2 k := by
  have hh : (1 : ℝ) ≤ Nat.log 2 k := by exact_mod_cast Nat.log_pos one_lt_two hk
  calc (k : ℝ) = ((2 : ℝ) ^ (logb 2 k / Nat.log 2 k)) ^ Nat.log 2 k := by
        rw [← rpow_mul_natCast zero_le_two, div_mul_cancel₀ _ (by linarith),
          rpow_logb two_pos (by norm_num) (by positivity)]
    _ ≤ (2 * logb 2 k / Nat.log 2 k) ^ Nat.log 2 k := by
        rw [mul_div_assoc]
        gcongr
        refine two_rpow_le_two_mul ?_ ?_
        · rw [le_div_iff₀ (by linarith), one_mul]
          exact_mod_cast natLog_le_logb k 2
        · rw [div_le_iff₀ (by linarith)]
          have hLh : logb 2 (k : ℝ) < Nat.log 2 k + 1 := by
            exact_mod_cast Nat.lt_floor_add_one (logb 2 (k : ℝ))
          linarith

/-- If `2 ≤ k ≤ m + 1`, `h = ⌊log₂ k⌋` and `x ^ h ≤ h ^ h ((m + 1)/k)^h k` whenever `h ≤ x`, then
`x ≤ 4 m log₂ k / k`. -/
private lemma le_four_mul_logb_div {x k m : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m + 1)
    (hx : Nat.log 2 k ≤ x →
      (x : ℝ) ^ Nat.log 2 k ≤ Nat.log 2 k ^ Nat.log 2 k * (((m + 1) / k) ^ Nat.log 2 k * k)) :
    (x : ℝ) ≤ 4 * m * logb 2 k / k := by
  have hL : 1 ≤ logb 2 (k : ℝ) := by
    rw [le_logb_iff_rpow_le one_lt_two (by positivity), rpow_one]
    exact_mod_cast hk
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by grind : 1 ≤ m)
  rcases lt_or_ge x (Nat.log 2 k) with hxh | hxh
  · have hxL : (x : ℝ) ≤ logb 2 k :=
      (Nat.cast_le.2 hxh.le).trans (by exact_mod_cast natLog_le_logb k 2)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hxL (by exact_mod_cast (by grind : k ≤ 4 * m) : (k : ℝ) ≤ 4 * m)
      (Nat.cast_nonneg k) (by linarith)]
  · have hh : 0 < Nat.log 2 k := Nat.log_pos one_lt_two hk
    refine le_of_pow_le_pow_left₀ hh.ne' (div_nonneg (by nlinarith) (by positivity)) ?_
    calc (x : ℝ) ^ Nat.log 2 k
        ≤ Nat.log 2 k ^ Nat.log 2 k * (((m + 1) / k) ^ Nat.log 2 k * k) := hx hxh
      _ ≤ Nat.log 2 k ^ Nat.log 2 k *
          ((2 * m / k) ^ Nat.log 2 k * (2 * logb 2 k / Nat.log 2 k) ^ Nat.log 2 k) := by
          gcongr
          · linarith
          · exact le_two_mul_logb_div_log_pow hk
      _ = (4 * m * logb 2 k / k) ^ Nat.log 2 k := by
          rw [← mul_pow, ← mul_pow]
          congr 1
          field_simp [(by exact_mod_cast hh.ne' : (Nat.log 2 k : ℝ) ≠ 0)]
          ring

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

/-- A set `A` of `k ≥ 2` elements of an `𝔽₂`-vector space with `|A ∔ A| ≤ m` has affine dimension
`d` with `d + 1 ≤ 4 m log₂ k / k`. -/
lemma finrank_vectorSpan_add_one_le_of_card_restrictedSumset_le {A : Finset V} (hA : 2 ≤ #A)
    {m : ℕ} (hm : #(restrictedSumset A) ≤ m) :
    (finrank (ZMod 2) (vectorSpan (ZMod 2) (A : Set V)) + 1 : ℝ) ≤ 4 * m * logb 2 #A / #A := by
  have hne : A.Nonempty := card_pos.1 (by grind)
  obtain ⟨t, htA, hspan, hind⟩ := exists_affineIndependent (ZMod 2) V (A : Set V)
  obtain ⟨X, rfl⟩ := (A.finite_toSet.subset htA).exists_finset_coe
  have hXne : X.Nonempty := by
    rw [← coe_nonempty, ← affineSpan_nonempty (k := ZMod 2), hspan, affineSpan_nonempty,
      coe_nonempty]
    exact hne
  have : Nonempty X := hXne.to_subtype
  have hX : finrank (ZMod 2) (vectorSpan (ZMod 2) (A : Set V)) + 1 = #X := by
    rw [← direction_affineSpan, ← hspan, direction_affineSpan,
      ← Subtype.range_coe (s := (X : Set V)), hind.finrank_vectorSpan_add_one]
    simp
  rw [← Nat.cast_add_one, hX]
  refine le_four_mul_logb_div hA (by grind [card_sub_one_le_card_restrictedSumset hne]) ?_
  intro hh
  refine (card_pow_le_of_affineIndependent hne (coe_subset.1 htA) hind hh).trans ?_
  gcongr
  exact_mod_cast (card_add_le_card_restrictedSumset_add_one A).trans (by grind)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [DecidableEq W]

/-- **Lemma 25** of Green. If `A` is a set of `k ≥ 2` elements of an `𝔽₂`-vector space with
`|A ∔ A| ≤ m`, then `r_{𝔽₂}(A) + 1 ≤ 4 m log₂ k / k`. -/
theorem freimanDimOver_add_one_le_of_card_restrictedSumset_le {A : Finset W} (hA : 2 ≤ #A)
    {m : ℕ} (hm : #(restrictedSumset A) ≤ m) :
    (freimanDimOver (ZMod 2) A + 1 : ℝ) ≤ 4 * m * logb 2 #A / #A := by
  obtain ⟨⟨f, hf, hdim⟩, -⟩ := isGreatest_freimanDimOver (ZMod 2) (card_pos.1 (by grind : 0 < #A))
  rw [← coe_image] at hf hdim
  have hcard : #(A.image f) = #A := card_image_of_injOn hf.bijOn.injOn
  rw [← hdim, ← hcard]
  exact finrank_vectorSpan_add_one_le_of_card_restrictedSumset_le (hcard ▸ hA)
    ((card_restrictedSumset_image_le hf.isAddFreimanHom).trans hm)

/-- If `A` is a set of `k ≥ 2` elements of an `𝔽₂`-vector space with `|A ∔ A| ≤ m`, then at most
`(2 ^ n) ^ (4 m log₂ k / k)` subsets of `𝔽₂^n` are Freiman isomorphic of order `2` to `A`. -/
lemma ncard_isAddFreimanIso_le_of_card_restrictedSumset_le {A : Finset W} (hA : 2 ≤ #A) {m : ℕ}
    (hm : #(restrictedSumset A) ≤ m) (n : ℕ) :
    ({B : Finset (Fin n → ZMod 2) | ∃ f : W → (Fin n → ZMod 2),
      IsAddFreimanIso 2 (A : Set W) (B : Set (Fin n → ZMod 2)) f}.ncard : ℝ) ≤
      ((2 : ℝ) ^ n) ^ (4 * m * logb 2 #A / #A) := by
  have hle := ncard_isAddFreimanIso_le (ZMod 2) n (card_pos.1 (by grind) : A.Nonempty)
  rw [Nat.card_zmod] at hle
  refine (Nat.cast_le.2 hle).trans ?_
  push_cast
  rw [← rpow_natCast ((2 : ℝ) ^ n)]
  push_cast
  exact rpow_le_rpow_of_exponent_le (one_le_pow₀ one_le_two)
    (freimanDimOver_add_one_le_of_card_restrictedSumset_le hA hm)

end CountingSetsWithSmallSumset
