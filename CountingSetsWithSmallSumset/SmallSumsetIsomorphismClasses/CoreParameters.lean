/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.RestrictedSumset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreDecomposition

/-!
# Proposition 15 with explicit parameters

This file fixes the parameters of the core decomposition of Proposition 15 of Green, *Counting
sets with small sumset, and the clique number of random Cayley graphs*. Let `A` be a set of
`t ≥ 2 ^ 9000` elements of a commutative monoid with cancellation whose restricted sumset has at
most `m ≥ t` elements. A sum is popular if it has at least `⌊t ^ (1 / 5)⌋` representations, and
the core is sampled with probability `t ^ (-1 / 15)`. Then `A` has a core `A₀` with at most
`4 t ^ (-1 / 15) m` elements and a subset `A₁` missing at most `4 t ^ (-4 / 5) m` elements such that
a translate of `A₁` lies in the restricted sumset of `A₀`. The paper takes `m = |A ∔ A|`; here `m`
is any upper bound with `t ≤ m`.

## Main definitions

* `smallSumsetClassCountThreshold`: the threshold `2 ^ 9000` for `t`.

## Main statements

* `exists_image_add_subset_restrictedSumset`: Proposition 15 of Green.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

noncomputable section

/-- An explicit threshold above which the small-sumset class estimates apply. -/
irreducible_def smallSumsetClassCountThreshold : ℕ :=
  2 ^ (9000 : ℕ)

lemma two_pow_200_le_smallSumsetClassCountThreshold :
    2 ^ (200 : ℕ) ≤ smallSumsetClassCountThreshold := by
  rw [smallSumsetClassCountThreshold_def]
  exact pow_le_pow_right' (by norm_num) (by norm_num)

lemma smallSumsetClassCountThreshold_pos :
    0 < smallSumsetClassCountThreshold := by
  rw [smallSumsetClassCountThreshold_def]
  positivity

lemma one_lt_of_smallSumsetClassCountThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : 1 < t := by
  rw [smallSumsetClassCountThreshold_def] at ht
  exact (Nat.one_lt_two_pow (by norm_num)).trans_le ht

lemma pos_of_smallSumsetClassCountThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : 0 < t :=
  Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)

lemma one_lt_cast_of_smallSumsetClassCountThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : (1 : ℝ) < t :=
  mod_cast one_lt_of_smallSumsetClassCountThreshold_le ht

/-- The rate `t ^ (-1 / 15)` at which the elements of a `t`-set are sampled to form its core. -/
private def coreSamplingRate (t : ℕ) : ℝ :=
  (t : ℝ) ^ (-(1 : ℝ) / 15)

/-- The number `⌊t ^ (1 / 5)⌋` of representations above which a sum is popular. -/
private def popularSumThreshold (t : ℕ) : ℕ :=
  ⌊(t : ℝ) ^ ((1 : ℝ) / 5)⌋₊

/-- The weight `t ^ (11 / 15)` of an exceptional element in the core decomposition. -/
private def exceptionPenalty (t : ℕ) : ℝ :=
  (t : ℝ) ^ ((11 : ℝ) / 15)

/-- The bound for the size of the core plus `exceptionPenalty t` times the number of exceptional
elements, for a `t`-set whose restricted sumset has at most `m` elements. -/
private def coreDecompositionBudget (t m : ℕ) : ℝ :=
  coreSamplingRate t * t + exceptionPenalty t *
    (1 + popularSumThreshold t * m / t +
      t * (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2))

private lemma exceptionPenalty_mul_rpow_one_fifth {t : ℕ} (ht : 0 < t) :
    exceptionPenalty t * (t : ℝ) ^ ((1 : ℝ) / 5) = coreSamplingRate t * t := by
  have htReal : (0 : ℝ) < t := mod_cast ht
  unfold coreSamplingRate exceptionPenalty
  rw [← Real.rpow_add htReal, ← Real.rpow_add_one htReal.ne']
  norm_num

private lemma exceptionPenalty_mul_rpow_neg_four_fifths {t : ℕ} (ht : 0 < t) :
    exceptionPenalty t * (t : ℝ) ^ (-(4 : ℝ) / 5) = coreSamplingRate t := by
  unfold coreSamplingRate exceptionPenalty
  rw [← Real.rpow_add (mod_cast ht)]
  norm_num

private lemma coreSamplingRate_pos {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) :
    0 < coreSamplingRate t := by
  unfold coreSamplingRate
  exact Real.rpow_pos_of_pos (by linarith [one_lt_cast_of_smallSumsetClassCountThreshold_le ht]) _

private lemma coreSamplingRate_lt_one {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) :
    coreSamplingRate t < 1 := by
  unfold coreSamplingRate
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_cast_of_smallSumsetClassCountThreshold_le ht)
    (by norm_num)

private lemma exceptionPenalty_nonneg (t : ℕ) : 0 ≤ exceptionPenalty t := by
  unfold exceptionPenalty
  positivity

private lemma exceptionPenalty_pos {t : ℕ} (ht : 0 < t) : 0 < exceptionPenalty t := by
  unfold exceptionPenalty
  positivity

private lemma one_hundred_eighty_le_rpow_one_thirtieth {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : (180 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 30) := by
  rw [smallSumsetClassCountThreshold_def] at ht
  have htReal : (2 : ℝ) ^ (9000 : ℕ) ≤ t := mod_cast ht
  refine ((by norm_num : (180 : ℝ) ≤ 2 ^ (8 : ℕ)).trans ?_).trans
    (Real.rpow_le_rpow (by positivity) htReal (by norm_num))
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)

private lemma rpow_one_fifth_eq_pow (t : ℕ) :
    (t : ℝ) ^ ((1 : ℝ) / 5) = ((t : ℝ) ^ ((1 : ℝ) / 30)) ^ (6 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private lemma one_hundred_eighty_le_rpow_one_fifth {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : (180 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 5) := by
  rw [rpow_one_fifth_eq_pow]
  exact (one_hundred_eighty_le_rpow_one_thirtieth ht).trans
    (le_self_pow₀ (by linarith [one_hundred_eighty_le_rpow_one_thirtieth ht]) (by norm_num))

private lemma rpow_one_fifth_div_two_le_popularSumThreshold {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (t : ℝ) ^ ((1 : ℝ) / 5) / 2 ≤ popularSumThreshold t := by
  unfold popularSumThreshold
  linarith [Nat.lt_floor_add_one ((t : ℝ) ^ ((1 : ℝ) / 5)),
    one_hundred_eighty_le_rpow_one_fifth ht]

private lemma rpow_one_fifth_div_six_le_popularSumThreshold_div_two {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (t : ℝ) ^ ((1 : ℝ) / 5) / 6 ≤ (popularSumThreshold t / 2 : ℕ) := by
  have hdiv : (popularSumThreshold t : ℝ) ≤ 2 * (popularSumThreshold t / 2 : ℕ) + 1 := by
    norm_cast
    grind
  linarith [rpow_one_fifth_div_two_le_popularSumThreshold ht,
    one_hundred_eighty_le_rpow_one_fifth ht]

private lemma rpow_one_fifteenth_eq_sq (t : ℕ) :
    (t : ℝ) ^ ((1 : ℝ) / 15) = ((t : ℝ) ^ ((1 : ℝ) / 30)) ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private lemma four_fifths_mul_log_le_rpow_one_fifteenth_div_six {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (4 : ℝ) / 5 * Real.log t ≤ (t : ℝ) ^ ((1 : ℝ) / 15) / 6 := by
  have htPos : (0 : ℝ) < t := by linarith [one_lt_cast_of_smallSumsetClassCountThreshold_le ht]
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htPos ((1 : ℝ) / 30))
  rw [Real.log_rpow htPos] at hlog
  rw [rpow_one_fifteenth_eq_sq]
  nlinarith [one_hundred_eighty_le_rpow_one_thirtieth ht]

private lemma coreSamplingRate_sq_mul_rpow_one_fifth {t : ℕ} (ht : 0 < t) :
    coreSamplingRate t ^ (2 : ℕ) * (t : ℝ) ^ ((1 : ℝ) / 5) = (t : ℝ) ^ ((1 : ℝ) / 15) := by
  unfold coreSamplingRate
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_add (mod_cast ht)]
  norm_num

private lemma one_sub_coreSamplingRate_sq_pow_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2) ≤ (t : ℝ) ^ (-(4 : ℝ) / 5) := by
  have ht_pos := pos_of_smallSumsetClassCountThreshold_le ht
  rw [Real.rpow_def_of_pos (mod_cast ht_pos)]
  refine (pow_le_pow_left₀ (by nlinarith [coreSamplingRate_pos ht, coreSamplingRate_lt_one ht])
    (Real.one_sub_le_exp_neg _) _).trans ?_
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  linarith [mul_le_mul_of_nonneg_left (rpow_one_fifth_div_six_le_popularSumThreshold_div_two ht)
      (sq_nonneg (coreSamplingRate t)),
    four_fifths_mul_log_le_rpow_one_fifteenth_div_six ht,
    coreSamplingRate_sq_mul_rpow_one_fifth ht_pos]

private lemma exceptionPenalty_le_coreSamplingRate_mul {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    exceptionPenalty t ≤ coreSamplingRate t * t := by
  rw [← exceptionPenalty_mul_rpow_one_fifth (pos_of_smallSumsetClassCountThreshold_le ht)]
  exact le_mul_of_one_le_right (exceptionPenalty_nonneg t)
    (Real.one_le_rpow (one_lt_cast_of_smallSumsetClassCountThreshold_le ht).le (by norm_num))

private lemma exceptionPenalty_mul_popularSumThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (m : ℕ) :
    exceptionPenalty t * (popularSumThreshold t * m / t) ≤ coreSamplingRate t * m := by
  rw [← mul_div_assoc,
    div_le_iff₀ (by linarith [one_lt_cast_of_smallSumsetClassCountThreshold_le ht]),
    mul_right_comm,
    ← exceptionPenalty_mul_rpow_one_fifth (pos_of_smallSumsetClassCountThreshold_le ht),
    ← mul_assoc]
  gcongr
  · exact exceptionPenalty_nonneg t
  · exact Nat.floor_le (by positivity)

private lemma exceptionPenalty_mul_one_sub_coreSamplingRate_sq_pow_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    exceptionPenalty t * (t * (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2)) ≤
      coreSamplingRate t * t := by
  conv_rhs =>
    rw [← exceptionPenalty_mul_rpow_neg_four_fifths (pos_of_smallSumsetClassCountThreshold_le ht)]
  rw [mul_assoc, mul_comm (t : ℝ)]
  gcongr
  · exact exceptionPenalty_nonneg t
  · exact one_sub_coreSamplingRate_sq_pow_le ht

/-- The numerical specialization of Green's alteration budget. -/
private lemma coreDecompositionBudget_le_four_mul_coreSamplingRate_mul {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m) :
    coreDecompositionBudget t m ≤ 4 * coreSamplingRate t * m := by
  unfold coreDecompositionBudget
  rw [mul_add, mul_add, mul_one]
  linarith [exceptionPenalty_le_coreSamplingRate_mul ht,
    exceptionPenalty_mul_popularSumThreshold_le ht m,
    exceptionPenalty_mul_one_sub_coreSamplingRate_sq_pow_le ht,
    mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr htm) (coreSamplingRate_pos ht).le]

variable {G : Type*} [AddCancelCommMonoid G] [DecidableEq G]

private lemma exists_image_add_subset_restrictedSumset_card_add_mul_le_budget {A : Finset G}
    {t m : ℕ} (hA : #A = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : #(restrictedSumset A) ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ Z ⊆ A, (A \ Z).image (a + ·) ⊆ restrictedSumset A₀ ∧
      #A₀ + exceptionPenalty t * #Z ≤ coreDecompositionBudget t m :=
  exists_image_add_subset_restrictedSumset_card_add_mul_le hA
    (card_pos.mp (hA ▸ pos_of_smallSumsetClassCountThreshold_le ht)) hm (popularSumThreshold t)
    (coreSamplingRate_pos ht) (coreSamplingRate_lt_one ht) (exceptionPenalty_nonneg t)

/-- **Proposition 15** of Green, with `t ≥ 2 ^ 9000` in place of `t` sufficiently large. Let
`t ≤ m`. A `t`-set `A` whose restricted sumset has at most `m` elements has a core `A₀` with at
most `4 * t ^ (-1 / 15) * m` elements and a subset `A₁` missing at most `4 * t ^ (-4 / 5) * m`
elements such that a translate of `A₁` lies in the restricted sumset of `A₀`. -/
theorem exists_image_add_subset_restrictedSumset {A : Finset G} {t m : ℕ} (hA : #A = t)
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m) (hm : #(restrictedSumset A) ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ A₁ ⊆ A, A₁.image (a + ·) ⊆ restrictedSumset A₀ ∧
      #A₀ ≤ 4 * (t : ℝ) ^ (-(1 : ℝ) / 15) * m ∧ #(A \ A₁) ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m := by
  have hle := coreDecompositionBudget_le_four_mul_coreSamplingRate_mul ht htm
  have hR := exceptionPenalty_pos (pos_of_smallSumsetClassCountThreshold_le ht)
  obtain ⟨a, ha, A₀, hA₀, Z, hZ, htranslate, hbudget⟩ :=
    exists_image_add_subset_restrictedSumset_card_add_mul_le_budget hA ht hm
  refine ⟨a, ha, A₀, hA₀, A \ Z, sdiff_subset, htranslate, ?_, ?_⟩
  · unfold coreSamplingRate at hle
    linarith [mul_nonneg hR.le (Nat.cast_nonneg (α := ℝ) #Z)]
  · rw [sdiff_sdiff_self_left, inter_eq_right.mpr hZ]
    rw [← exceptionPenalty_mul_rpow_neg_four_fifths
      (pos_of_smallSumsetClassCountThreshold_le ht)] at hle
    refine le_of_mul_le_mul_left ?_ hR
    linarith [Nat.cast_nonneg (α := ℝ) #A₀]

end

end CountingSetsWithSmallSumset
