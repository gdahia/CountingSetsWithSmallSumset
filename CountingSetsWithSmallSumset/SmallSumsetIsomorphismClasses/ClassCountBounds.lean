/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreAndCovers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# The number of Freiman isomorphism classes of sets with small sumset

Let `t ≥ 2 ^ 9000` and `m ≤ t ^ (31 / 30)`. Following Section 4 of Green, *Counting sets with
small sumset, and the clique number of random Cayley graphs*, the sets `A ⊆ ℕ` with `|A| = t`
whose restricted sumset has at most `m` elements lie in at most
`(e * m / t) ^ t * exp (t ^ (31 / 32))` Freiman isomorphism classes of order `2`. A class of
Freiman dimension at most `r` has at most `n ^ (r + 1)` members in `[n]`. So, for
`s ≤ t ^ (31 / 30) / 2`, there are at most `n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))`
sets `X ⊆ [n]` with `|X| = t`, `freimanDim X ≤ r` and `|X + X| ≤ s`.

## Main definitions

* `freimanClassRealizations n r t B`: the sets `X ⊆ [n]` with `|X| = t` and `freimanDim X ≤ r`
  that are Freiman isomorphic of order `2` to `B`.

## Main statements

* `freimanClassCountBound_le`: the bound
  `freimanClassCountBound t m ≤ (e * m / t) ^ t * exp (t ^ (31 / 32))`.
* `exists_smallRestrictedSumsetFreimanClassCover`: Proposition 18 of Green, the bound for the
  number of classes.
* `ncard_freimanClassRealizations_le`: Lemma 13 (i) of Green, the bound `n ^ (r + 1)` for the
  number of members of a class in `[n]`.
* `smallSumsetFreimanDimSets_ncard_le_of_class_cover`: the bound for the number of sets.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Real SumOfSetsInSeveralDimensions
open scoped Pointwise

noncomputable section

private lemma two_pow_le_natCast {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) :
    (2 : ℝ) ^ (9000 : ℕ) ≤ t := by
  rw [smallSumsetClassCountThreshold_def] at ht
  exact_mod_cast ht

private lemma one_le_natCast {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) : (1 : ℝ) ≤ t :=
  mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le

private lemma natCast_pos {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) : (0 : ℝ) < t :=
  zero_lt_one.trans_le (one_le_natCast ht)

private lemma natCast_rpow_mul_rpow {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) {a b c : ℝ}
    (h : a + b = c) : (t : ℝ) ^ a * (t : ℝ) ^ b = (t : ℝ) ^ c := by
  rw [← rpow_add (natCast_pos ht), h]

private lemma natCast_pow_eq_exp {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) (N : ℕ) :
    (t : ℝ) ^ N = exp (N * log t) := by
  rw [exp_nat_mul, exp_log (natCast_pos ht)]

private lemma le_two_pow_rpow : (420000 : ℝ) ≤ ((2 : ℝ) ^ (9000 : ℕ)) ^ ((1 : ℝ) / 480) := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
  conv_rhs =>
    rw [← rpow_natCast, ← rpow_mul (by positivity), ← rpow_natCast (2 : ℝ) 9000,
      ← rpow_mul (by positivity)]
    norm_num
  norm_num

private lemma le_natCast_rpow {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) {a : ℝ}
    (ha : 1 / 480 ≤ a) : 420000 ≤ (t : ℝ) ^ a :=
  (le_two_pow_rpow.trans (rpow_le_rpow (by positivity) (two_pow_le_natCast ht) (by norm_num))).trans
    (rpow_le_rpow_of_exponent_le (one_le_natCast ht) ha)

private lemma log_natCast_le {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) :
    log t ≤ 3 / 200 * (t : ℝ) ^ ((1 : ℝ) / 480) := by
  have h₂ := two_pow_le_natCast ht
  have hexp : exp ((1 / 480 : ℝ)⁻¹) ≤ 2 ^ (9000 : ℕ) := by
    rw [← exp_log (by positivity : (0 : ℝ) < 2 ^ (9000 : ℕ)), exp_le_exp, log_pow,
      Nat.cast_ofNat, one_div, inv_inv]
    linarith [log_two_gt_d9]
  rw [← div_le_iff₀ (rpow_pos_of_pos (natCast_pos ht) _)]
  refine (log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 480) hexp (hexp.trans h₂)
    h₂).trans ((div_le_iff₀ (by positivity)).2 ?_)
  rw [log_pow, Nat.cast_ofNat]
  linarith [log_two_lt_d9, le_two_pow_rpow]

private lemma cast_choose_le_pow {t m k : ℕ} (ht : 0 < t) (htm : t ≤ m) (hk : k ≤ t) :
    (m.choose k : ℝ) ≤ (exp 1 * m / t) ^ t := by
  have ht₀ : (0 : ℝ) < t := mod_cast ht
  have hmt : 1 ≤ (m : ℝ) / t := (one_le_div₀ ht₀).2 (mod_cast htm)
  have h : (m : ℝ) ^ k / k.factorial = (m / t) ^ k * (t ^ k / k.factorial) := by
    rw [← mul_div_assoc, ← mul_pow, div_mul_cancel₀ _ ht₀.ne']
  rw [mul_div_assoc, mul_pow, ← exp_nat_mul, mul_one, mul_comm]
  refine (Nat.choose_le_pow_div k m).trans (h.trans_le ?_)
  exact mul_le_mul (pow_le_pow_right₀ hmt hk) (pow_div_factorial_le_exp _ ht₀.le k) (by positivity)
    (by positivity)

private lemma natCeil_four_mul_rpow_mul_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) {a b : ℝ} (hab : a + 31 / 30 = b) :
    (⌈4 * (t : ℝ) ^ a * m⌉₊ : ℝ) ≤ 4 * (t : ℝ) ^ b + 1 := by
  rw [← natCast_rpow_mul_rpow ht hab]
  refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
  linarith [mul_le_mul_of_nonneg_left hm (rpow_nonneg (Nat.cast_nonneg t) a)]

private lemma coreCardBound_cast_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (coreCardBound t m : ℝ) ≤ 4 * (t : ℝ) ^ ((29 : ℝ) / 30) + 1 :=
  natCeil_four_mul_rpow_mul_le ht hm (by norm_num)

private lemma exceptionCardBound_cast_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (exceptionCardBound t m : ℝ) ≤ 4 * (t : ℝ) ^ ((7 : ℝ) / 30) + 1 :=
  natCeil_four_mul_rpow_mul_le ht hm (by norm_num)

private lemma four_mul_rpow_add_two_le {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) {a : ℝ}
    (ha₀ : 0 ≤ a) (ha : a ≤ 479 / 480) : 4 * (t : ℝ) ^ a + 2 ≤ t := by
  have h := natCast_rpow_mul_rpow ht (add_sub_cancel a 1)
  rw [rpow_one] at h
  nlinarith [one_le_rpow (one_le_natCast ht) ha₀,
    le_natCast_rpow ht (a := 1 - a) (by linarith)]

private lemma coreCardBound_le_self {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) : coreCardBound t m ≤ t := by
  rw [← Nat.cast_le (α := ℝ)]
  linarith [coreCardBound_cast_le ht hm,
    four_mul_rpow_add_two_le ht (a := 29 / 30) (by norm_num) (by norm_num)]

private lemma exceptionCardBound_add_one_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) : exceptionCardBound t m + 1 ≤ t := by
  rw [← Nat.cast_le (α := ℝ), Nat.cast_add_one]
  linarith [exceptionCardBound_cast_le ht hm,
    four_mul_rpow_add_two_le ht (a := 7 / 30) (by norm_num) (by norm_num)]

/-- The inequality behind `coreClassCost_le`, for real numbers. -/
private lemma sixteen_mul_mul_le {c L A q : ℝ} (hc : c ≤ 4 * A + 1) (hL₀ : 0 ≤ L)
    (hL : L ≤ 3 / 200 * q) (hA : 420000 ≤ A) (hq : 420000 ≤ q) :
    16 * c * L ≤ 97 / 100 * (A * q) := by
  nlinarith [mul_le_mul_of_nonneg_right hc hL₀,
    mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ 16 * (4 * A + 1)),
    mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 hq)]

private lemma coreClassCost_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    16 * (coreCardBound t m : ℝ) * log t ≤ 97 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32) := by
  rw [← natCast_rpow_mul_rpow ht (a := 29 / 30) (b := 1 / 480) (c := 31 / 32) (by norm_num)]
  exact sixteen_mul_mul_le (coreCardBound_cast_le ht hm) (log_nonneg (one_le_natCast ht))
    (log_natCast_le ht) (le_natCast_rpow ht (by norm_num)) (le_natCast_rpow ht le_rfl)

/-- The inequality behind `extensionClassCost_le`, for real numbers. -/
private lemma five_mul_pow_mul_le {x L B q R : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 4 * B + 1) (hB : 1 ≤ B)
    (hL₀ : 0 ≤ L) (hL : L ≤ 3 / 200 * q) (hq : 0 ≤ q) (hR : 420000 ≤ R) :
    5 * (x + 1) ^ 4 * L ≤ 1 / 100 * (B ^ 4 * q * R) := by
  have hpow : (x + 1) ^ 4 ≤ (6 * B) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hBq : 0 ≤ B ^ 4 * q := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hpow hL₀,
    mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (6 * B) ^ 4),
    mul_nonneg hBq (sub_nonneg.2 hR)]

private lemma extensionClassCost_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    5 * ((exceptionCardBound t m : ℝ) + 1) ^ 4 * log t ≤
      1 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32) := by
  have hE : ((t : ℝ) ^ ((7 : ℝ) / 30)) ^ 4 * (t : ℝ) ^ ((1 : ℝ) / 480) * (t : ℝ) ^ ((1 : ℝ) / 30) =
      (t : ℝ) ^ ((31 : ℝ) / 32) := by
    rw [← rpow_natCast, ← rpow_mul (Nat.cast_nonneg t), natCast_rpow_mul_rpow ht rfl,
      natCast_rpow_mul_rpow ht]
    norm_num
  rw [← hE]
  exact five_mul_pow_mul_le (Nat.cast_nonneg _) (exceptionCardBound_cast_le ht hm)
    (one_le_rpow (one_le_natCast ht) (by norm_num)) (log_nonneg (one_le_natCast ht))
    (log_natCast_le ht) (by positivity) (le_natCast_rpow ht (by norm_num))

private lemma classCountSummationRange_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (((exceptionCardBound t m + 1) * coreCardBound t m : ℕ) : ℝ) ≤
      exp (1 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
  have ht₀ := natCast_pos ht
  refine (Nat.cast_le.2 (Nat.mul_le_mul (exceptionCardBound_add_one_le ht hm)
    (coreCardBound_le_self ht hm))).trans ?_
  rw [Nat.cast_mul, ← log_le_iff_le_exp (by positivity), log_mul ht₀.ne' ht₀.ne',
    ← natCast_rpow_mul_rpow ht (a := 29 / 30) (b := 1 / 480) (c := 31 / 32) (by norm_num)]
  nlinarith [log_natCast_le ht, le_natCast_rpow ht (a := 29 / 30) (by norm_num),
    le_natCast_rpow ht (a := 1 / 480) le_rfl]

private lemma classCountTerm_le_pow {t m d l D L : ℕ} (ht : 2 ≤ t) (hd : d ≤ D) (hl : l ≤ L)
    (hL : L ≤ t) :
    l ^ (16 * l) * m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) ≤
      t ^ (16 * L + 5 * (D + 1) ^ 4) * m.choose (t - d) := by
  have hbase : 1 + (t - d) ^ 4 ≤ t ^ 5 := by
    linarith [Nat.pow_le_pow_left (Nat.sub_le t d) 4, Nat.one_le_pow 4 t (by grind),
      Nat.mul_le_mul_left (t ^ 4) ht, pow_succ t 4]
  rw [pow_add, pow_mul t 5, mul_right_comm]
  gcongr ?_ * ?_ * _
  · exact pow_le_pow (hl.trans hL) (by grind) (by gcongr)
  · exact pow_le_pow hbase (Nat.one_le_pow _ _ (by grind)) (by gcongr)

private lemma freimanClassCountTerm_le {t m d l : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (htm : t ≤ m) (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) (hd : d ≤ exceptionCardBound t m)
    (hl : l ≤ coreCardBound t m) :
    ((l ^ (16 * l) * m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) : ℕ) : ℝ) ≤
      (exp 1 * m / t) ^ t * exp (99 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
  have ht₁ := one_lt_of_smallSumsetClassCountThreshold_le ht
  refine (Nat.cast_le.2 (classCountTerm_le_pow (m := m) ht₁ hd hl
    (coreCardBound_le_self ht hm))).trans ?_
  rw [Nat.cast_mul, Nat.cast_pow, natCast_pow_eq_exp ht, mul_comm]
  refine mul_le_mul (cast_choose_le_pow (by grind) htm (Nat.sub_le t d)) (exp_le_exp.2 ?_)
    (exp_pos _).le (by positivity)
  push_cast
  linarith [coreClassCost_le ht hm, extensionClassCost_le ht hm,
    rpow_nonneg (Nat.cast_nonneg t) ((31 : ℝ) / 32)]

/-- If `2 ^ 9000 ≤ t ≤ m ≤ t ^ (31 / 30)`, then
`freimanClassCountBound t m ≤ (e * m / t) ^ t * exp (t ^ (31 / 32))`. -/
lemma freimanClassCountBound_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (freimanClassCountBound t m : ℝ) ≤
      (exp 1 * m / t) ^ t * exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  rw [freimanClassCountBound, ← sum_product', Nat.cast_sum]
  refine (sum_le_sum fun p hp ↦ freimanClassCountTerm_le ht htm hm
    (Nat.lt_succ_iff.1 (mem_range.1 (mem_product.1 hp).1))
    (mem_Icc.1 (mem_product.1 hp).2).2).trans ?_
  rw [sum_const, card_product, card_range, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (classCountSummationRange_le ht hm)
    (by positivity)).trans_eq ?_
  rw [mul_left_comm, ← exp_add]
  congr 2
  ring

/-- Proposition 18 of Green. If `t ≥ 2 ^ 9000` and `m ≤ t ^ (31 / 30)`, then there are at most
`(e * m / t) ^ t * exp (t ^ (31 / 32))` sets such that every `A ⊆ ℕ` with `|A| = t` whose restricted
sumset has at most `m` elements is Freiman isomorphic of order `2` to one of them. -/
theorem exists_smallRestrictedSumsetFreimanClassCover {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 2 (smallRestrictedSumsetSets t m) representatives ∧
      (#representatives : ℝ) ≤ (exp 1 * m / t) ^ t * exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  by_cases htm : t ≤ m
  · obtain ⟨representatives, hcover, hcard⟩ :=
      exists_smallRestrictedSumsetFreimanClassCover_raw t m ht
    exact ⟨representatives, hcover,
      (Nat.cast_le.2 hcard).trans (freimanClassCountBound_le ht htm hm)⟩
  · refine ⟨∅, ?_, ?_⟩
    · rintro A ⟨rfl, hsum⟩
      exact (htm ((card_le_card_restrictedSumset_of_three_le A (le_trans (by norm_num)
        (two_pow_200_le_smallSumsetClassCountThreshold.trans ht))).trans hsum)).elim
    · rw [card_empty, Nat.cast_zero]
      positivity

/-- The sets `X ⊆ [n]` with `|X| = t` and `freimanDim X ≤ r` that are Freiman isomorphic of order
`2` to `representative`. -/
def freimanClassRealizations (n r t : ℕ) (representative : Finset ℕ) :
    Set (Finset ℕ) :=
  {X | X ⊆ Icc 1 n ∧ X.card = t ∧ freimanDim X ≤ r ∧
    FreimanEquivalent 2 X representative}

private lemma freimanClassRealizations_finite (n r t : ℕ) (B : Finset ℕ) :
    (freimanClassRealizations n r t B).Finite :=
  (Icc 1 n).powerset.finite_toSet.subset fun _ hX ↦ mem_powerset.2 hX.1

private lemma freimanEquivalent_of_freimanEquivalent_right {X Y B : Finset ℕ}
    (hX : FreimanEquivalent 2 X B) (hY : FreimanEquivalent 2 Y B) : FreimanEquivalent 2 X Y := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  exact ⟨Function.invFunOn g Y ∘ f, hg.invFunOn.comp hf⟩

private lemma relationHolds_comp_iff {t : ℕ} {X Y : Finset ℕ} {f : ℕ → ℕ}
    (hf : IsAddFreimanIso 2 (X : Set ℕ) (Y : Set ℕ) f) {a : Fin t → ℕ} (ha : ∀ i, a i ∈ X)
    (p : RelationIndex t) : relationHolds a p ↔ relationHolds (f ∘ a) p :=
  (hf.add_eq_add (ha _) (ha _) (ha _) (ha _)).symm

/-- Lemma 13 (i) of Green. A Freiman isomorphism class of order `2` has at most `n ^ (r + 1)`
members `X ⊆ [n]` with `|X| = t` and `freimanDim X ≤ r`. -/
lemma ncard_freimanClassRealizations_le (n r t : ℕ) (representative : Finset ℕ)
    (ht : 0 < t) :
    ((freimanClassRealizations n r t representative).ncard : ℝ) ≤
      (n : ℝ) ^ (r + 1) := by
  obtain hempty | ⟨X₀, hX₀⟩ := (freimanClassRealizations n r t representative).eq_empty_or_nonempty
  · rw [hempty, Set.ncard_empty, Nat.cast_zero]
    positivity
  have := (freimanClassRealizations_finite n r t representative).fintype
  choose f hf using fun X : freimanClassRealizations n r t representative ↦
    freimanEquivalent_of_freimanEquivalent_right hX₀.2.2.2 X.2.2.2.2
  let a := finsetTuple X₀ hX₀.2.1
  have ha (i : Fin t) : a i ∈ X₀ := (X₀.orderIsoOfFin hX₀.2.1 i).2
  have hrange (X : freimanClassRealizations n r t representative) :
      Set.range (f X ∘ a) = X.1 := by
    rw [Set.range_comp, range_finsetTuple]
    exact (hf X).bijOn.image_eq
  obtain ⟨anchor, hanchor⟩ := exists_determiningCoordinates ht a
    ((relationModelDim_le_freimanDim ht ⟨X₀, hX₀.2.1⟩).trans hX₀.2.2.1)
  have hmem (X : freimanClassRealizations n r t representative) (i : Fin (r + 1)) :
      f X (a (anchor i)) ∈ Icc 1 n := by
    apply X.2.1
    rw [← mem_coe, ← hrange X]
    exact Set.mem_range_self _
  have hinj : Function.Injective fun X (i : Fin (r + 1)) ↦
      (⟨f X (a (anchor i)), hmem X i⟩ : Icc 1 n) := by
    intro X Y hXY
    have h := tuple_eq_of_relations_of_determiningCoordinates a (f X ∘ a) (f Y ∘ a) anchor hanchor
      (relationHolds_comp_iff (hf X) ha) (relationHolds_comp_iff (hf Y) ha)
      fun i ↦ congrArg Subtype.val (congrFun hXY i)
    apply Subtype.ext
    apply coe_injective
    rw [← hrange X, ← hrange Y, h]
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Set.fintypeCard_eq_ncard, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
    Nat.card_Icc, Nat.add_sub_cancel] at hcard
  exact_mod_cast hcard

/-- Let `t ≥ 2 ^ 9000` and `s ≤ t ^ (31 / 30) / 2`. There are at most
`n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ [n]` with `|X| = t`,
`freimanDim X ≤ r` and `|X + X| ≤ s`. -/
theorem smallSumsetFreimanDimSets_ncard_le_of_class_cover (n r s t : ℕ)
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hs : (s : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2) :
    ((smallSumsetFreimanDimSets n r s t).ncard : ℝ) ≤
      (n : ℝ) ^ (r + 1) * (2 * exp 1 * s / t) ^ t * exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  have hm : ((2 * s : ℕ) : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) := by
    push_cast
    linarith
  obtain ⟨representatives, hcover, hcard⟩ := exists_smallRestrictedSumsetFreimanClassCover ht hm
  have hfin := freimanClassRealizations_finite n r t
  have hsubset : smallSumsetFreimanDimSets n r s t ⊆
      ↑(representatives.biUnion fun B ↦ (hfin B).toFinset) := by
    intro X hX
    obtain ⟨B, hB, hXB⟩ := hcover X
      ⟨hX.2.1, (card_restrictedSumset_le_card_add X).trans (hX.2.2.2.trans (by grind))⟩
    exact mem_coe.2 (mem_biUnion.2 ⟨B, hB, (hfin B).mem_toFinset.2 ⟨hX.1, hX.2.1, hX.2.2.1, hXB⟩⟩)
  have hncard : (smallSumsetFreimanDimSets n r s t).ncard ≤ #representatives * n ^ (r + 1) := by
    refine (Set.ncard_le_ncard hsubset).trans ?_
    rw [Set.ncard_coe_finset]
    refine card_biUnion_le_card_mul _ _ _ fun B _ ↦ ?_
    rw [← Set.ncard_eq_toFinset_card _ (hfin B)]
    exact_mod_cast ncard_freimanClassRealizations_le n r t B
      (Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht))
  refine (Nat.cast_le.2 hncard).trans ?_
  rw [Nat.cast_mul, Nat.cast_pow, mul_comm, mul_assoc]
  refine (mul_le_mul_of_nonneg_left hcard (by positivity)).trans_eq ?_
  push_cast
  ring

end

end CountingSetsWithSmallSumset
