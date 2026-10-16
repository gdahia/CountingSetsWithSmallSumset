/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.BoundedFreimanDimSets
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreAndCovers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# The number of Freiman isomorphism classes of sets with small sumset

Let `t ≥ 2 ^ 9000` and `m ≤ t ^ (31 / 30)`. Following Section 4 of Green, *Counting sets with
small sumset, and the clique number of random Cayley graphs*, the sets of `t` elements of a vector
space whose restricted sumset has at most `m` elements lie in at most
`(e * m / t) ^ t * exp (t ^ (31 / 32))` Freiman isomorphism classes of order `2`. The same holds
for a set with an injective additive map into a vector space, such as `ℕ` or `ℤ` in `ℚ`. A class
of Freiman dimension at most `r` has at most `n ^ (r + 1)` members in `[n]`. So, for
`s ≤ t ^ (31 / 30) / 2`, there are at most `n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))`
sets `X ⊆ [n]` with `|X| = t`, `freimanDim X ≤ r` and `|X + X| ≤ s`. The paper states
Proposition 18 for `t` sufficiently large; here `t ≥ 2 ^ 9000`.

## Main statements

* `freimanClassCountBound_le`: the bound
  `freimanClassCountBound t m ≤ (e * m / t) ^ t * exp (99 / 100 * t ^ (31 / 32))`.
* `exists_coversFreimanIsoClasses_card_restrictedSumset_le`: Proposition 18 of Green for subsets
  of a vector space.
* `exists_coversFreimanIsoClasses_card_restrictedSumset_le_of_injective`: Proposition 18 of Green
  for a set with an injective additive map into a vector space.
* `smallSumsetFreimanDimSets_ncard_le_of_class_cover`: the bound for the number of sets of natural
  numbers.
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
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) {a b : ℝ} (hab : a + 31 / 30 = b) :
    (⌈4 * (t : ℝ) ^ a * m⌉₊ : ℝ) ≤ 4 * (t : ℝ) ^ b + 1 := by
  rw [← natCast_rpow_mul_rpow ht hab]
  refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
  linarith [mul_le_mul_of_nonneg_left hm (rpow_nonneg (Nat.cast_nonneg t) a)]

private lemma coreCardBound_cast_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (coreCardBound t m : ℝ) ≤ 4 * (t : ℝ) ^ ((29 : ℝ) / 30) + 1 :=
  natCeil_four_mul_rpow_mul_le ht hm (by norm_num)

private lemma exceptionCardBound_cast_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (exceptionCardBound t m : ℝ) ≤ 4 * (t : ℝ) ^ ((7 : ℝ) / 30) + 1 :=
  natCeil_four_mul_rpow_mul_le ht hm (by norm_num)

private lemma four_mul_rpow_add_two_le {t : ℕ} (ht : smallSumsetClassCountThreshold ≤ t) {a : ℝ}
    (ha₀ : 0 ≤ a) (ha : a ≤ 479 / 480) : 4 * (t : ℝ) ^ a + 2 ≤ t := by
  have h := natCast_rpow_mul_rpow ht (add_sub_cancel a 1)
  rw [rpow_one] at h
  nlinarith [one_le_rpow (one_le_natCast ht) ha₀,
    le_natCast_rpow ht (a := 1 - a) (by linarith)]

private lemma coreCardBound_le_self {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) : coreCardBound t m ≤ t := by
  rw [← Nat.cast_le (α := ℝ)]
  linarith [coreCardBound_cast_le ht hm,
    four_mul_rpow_add_two_le ht (a := 29 / 30) (by norm_num) (by norm_num)]

private lemma exceptionCardBound_add_one_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) : exceptionCardBound t m + 1 ≤ t := by
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
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
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
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
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
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
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
    (htm : t ≤ m) (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) (hd : d ≤ exceptionCardBound t m)
    (hl : l ≤ coreCardBound t m) :
    ((l ^ (16 * l) * m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) : ℕ) : ℝ) ≤
      (exp 1 * m / t) ^ t * exp (98 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
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
`freimanClassCountBound t m ≤ (e * m / t) ^ t * exp (99 / 100 * t ^ (31 / 32))`. -/
lemma freimanClassCountBound_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (freimanClassCountBound t m : ℝ) ≤
      (exp 1 * m / t) ^ t * exp (99 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
  rw [freimanClassCountBound, ← sum_product', Nat.cast_sum]
  refine (sum_le_sum (g := fun _ ↦ (exp 1 * m / t) ^ t *
    exp (98 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32))) ?_).trans ?_
  · rintro ⟨d, l⟩ hp
    obtain ⟨hd, hl⟩ := mem_product.1 hp
    obtain ⟨-, hl⟩ := mem_Icc.1 hl
    exact freimanClassCountTerm_le ht htm hm (Nat.lt_succ_iff.1 (mem_range.1 hd)) hl
  rw [sum_const, card_product, card_range, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (classCountSummationRange_le ht hm)
    (by positivity)).trans_eq ?_
  rw [mul_left_comm, ← exp_add]
  congr 2
  ring

/-- The bound for `m = t` with the factor `exp (99 / 100 * t ^ (31 / 32))` is at most the bound for
`m = t - 1` with the factor `exp (t ^ (31 / 32))`, since `(t / (t - 1)) ^ t ≤ e ^ 2`. -/
private lemma exp_one_pow_mul_exp_le {t m : ℕ} (ht : smallSumsetClassCountThreshold ≤ t)
    (hmt : m + 1 = t) :
    (exp 1 * t / t) ^ t * exp (99 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) ≤
      (exp 1 * m / t) ^ t * exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  have ht' : (t : ℝ) = m + 1 := by rw [← hmt]; push_cast; ring
  have hm : (1 : ℝ) ≤ m := by
    have := one_lt_of_smallSumsetClassCountThreshold_le ht
    exact_mod_cast (by grind : 1 ≤ m)
  have hratio : ((t : ℝ) / m) ^ t ≤ exp (1 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
    calc ((t : ℝ) / m) ^ t ≤ exp (1 / m) ^ t := by
          gcongr
          rw [ht', add_div, div_self (by positivity), add_comm]
          exact add_one_le_exp _
      _ = exp (t / m) := by rw [← exp_nat_mul]; ring_nf
      _ ≤ exp (1 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith [le_natCast_rpow ht (a := 31 / 32) (by norm_num)]
  calc (exp 1 * t / t) ^ t * exp (99 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32))
      = (exp 1 * m / t) ^ t * (((t : ℝ) / m) ^ t *
          exp (99 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32))) := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ (exp 1 * m / t) ^ t * (exp (1 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32)) *
          exp (99 / 100 * (t : ℝ) ^ ((31 : ℝ) / 32))) := by gcongr
    _ = (exp 1 * m / t) ^ t * exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by rw [← exp_add]; ring_nf

/-- **Proposition 18** of Green. Let `W` be a vector space over a field `F`, let `t ≥ 2 ^ 9000`
and `m ≤ t ^ (31 / 30)`. There is a family of at most `(e * m / t) ^ t * exp (t ^ (31 / 32))` finite
subsets of `W` such that every set of `t` elements of `W` whose restricted sumset has at most `m`
elements is Freiman isomorphic of order `2` to a member of the family. -/
theorem exists_coversFreimanIsoClasses_card_restrictedSumset_le (F W : Type*) [Field F]
    [AddCommGroup W] [Module F W] [DecidableEq W] {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ∃ representatives : Finset (Finset W),
      CoversFreimanIsoClasses 2 {A : Finset W | #A = t ∧ #(restrictedSumset A) ≤ m}
        representatives ∧
      #representatives ≤ (exp 1 * m / t) ^ t * exp (t ^ ((31 : ℝ) / 32)) := by
  obtain htm | hmt | hmt : t ≤ m ∨ m + 1 = t ∨ m + 1 < t := by grind
  · obtain ⟨representatives, hcover, hcard⟩ :=
      exists_coversFreimanIsoClasses_card_le_freimanClassCountBound F W ht htm
    refine ⟨representatives, hcover,
      (Nat.cast_le.2 hcard).trans ((freimanClassCountBound_le ht htm hm).trans ?_)⟩
    gcongr
    linarith [rpow_nonneg (Nat.cast_nonneg t) ((31 : ℝ) / 32)]
  · obtain ⟨representatives, hcover, hcard⟩ :=
      exists_coversFreimanIsoClasses_card_le_freimanClassCountBound F W ht le_rfl
    refine ⟨representatives, hcover.subset fun A ⟨hA, hAm⟩ ↦ ⟨hA, by grind⟩,
      (Nat.cast_le.2 hcard).trans
        ((freimanClassCountBound_le ht le_rfl ?_).trans (exp_one_pow_mul_exp_le ht hmt))⟩
    simpa using rpow_le_rpow_of_exponent_le (one_le_natCast ht) (by norm_num : (1 : ℝ) ≤ 31 / 30)
  · refine ⟨∅, ?_, by simpa using by positivity⟩
    rintro A ⟨hA, hAm⟩
    grind [card_sub_one_le_card_restrictedSumset (card_pos.mp (by grind : 0 < #A))]

private lemma restrictedSumset_image_subset {G H : Type*} [Add G] [Add H] [DecidableEq G]
    [DecidableEq H] (φ : G →ₙ+ H) (A : Finset G) :
    restrictedSumset (A.image φ) ⊆ (restrictedSumset A).image φ := by
  intro x hx
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab, rfl⟩ := by
    simpa only [mem_restrictedSumset, mem_image] using hx
  exact mem_image.mpr ⟨a + b, mem_restrictedSumset.mpr ⟨a, ha, b, hb, by grind, rfl⟩, by simp⟩

/-- **Proposition 18** of Green, for a set `G` with an injective additive map `φ` into a vector
space `W` over a field `F`, such as `ℕ` or `ℤ` with the inclusion into `ℚ`. Let `t ≥ 2 ^ 9000` and
`m ≤ t ^ (31 / 30)`. There is a family of at most `(e * m / t) ^ t * exp (t ^ (31 / 32))` finite
subsets of `G` such that every set of `t` elements of `G` whose restricted sumset has at most `m`
elements is Freiman isomorphic of order `2` to a member of the family. -/
theorem exists_coversFreimanIsoClasses_card_restrictedSumset_le_of_injective {G : Type*}
    [AddCommMonoid G] [DecidableEq G] (F : Type*) {W : Type*} [Field F] [AddCommGroup W]
    [Module F W] {φ : G →+ W} (hφ : Function.Injective φ) {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ∃ representatives : Finset (Finset G),
      CoversFreimanIsoClasses 2 {A : Finset G | #A = t ∧ #(restrictedSumset A) ≤ m}
        representatives ∧
      #representatives ≤ (exp 1 * m / t) ^ t * exp (t ^ ((31 : ℝ) / 32)) := by
  classical
  obtain ⟨representatives, hcover, hcard⟩ :=
    exists_coversFreimanIsoClasses_card_restrictedSumset_le F W ht hm
  have hsub : image φ '' {A : Finset G | #A = t ∧ #(restrictedSumset A) ≤ m} ⊆
      {A : Finset W | #A = t ∧ #(restrictedSumset A) ≤ m} := by
    rintro _ ⟨A, ⟨hA, hAm⟩, rfl⟩
    exact ⟨(card_image_of_injective _ hφ).trans hA, (card_le_card
      (restrictedSumset_image_subset φ.toAddHom A)).trans (card_image_le.trans hAm)⟩
  obtain ⟨representatives', -, hcover', hcard'⟩ := exists_coversFreimanIsoClasses_card_le_of_image
    (isAddFreimanIso_image_of_injective 2 hφ) (hcover.subset hsub)
  exact ⟨representatives', hcover', (Nat.cast_le.2 hcard').trans hcard⟩

/-- Let `t ≥ 2 ^ 9000` and `s ≤ t ^ (31 / 30) / 2`. There are at most
`n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ [n]` with `|X| = t`,
`freimanDim X ≤ r` and `|X + X| ≤ s`. The paper does not state this bound. It follows from
Proposition 18 and the bound `n ^ (r + 1)` for the number of members of a class in `[n]`. -/
lemma smallSumsetFreimanDimSets_ncard_le_of_class_cover (n r s t : ℕ)
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hs : s ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2) :
    (smallSumsetFreimanDimSets n r s t).ncard ≤
      n ^ (r + 1) * (2 * exp 1 * s / t) ^ t * exp (t ^ ((31 : ℝ) / 32)) := by
  have hm : ((2 * s : ℕ) : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) := by
    push_cast
    linarith
  obtain ⟨representatives, hcover, hcard⟩ :=
    exists_coversFreimanIsoClasses_card_restrictedSumset_le_of_injective ℚ
      (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective ht hm
  have hsub : smallSumsetFreimanDimSets n r s t ⊆
      {A : Finset ℕ | #A = t ∧ #(restrictedSumset A) ≤ 2 * s} := by
    rintro X ⟨-, hX, -, hXs⟩
    exact ⟨hX, (card_restrictedSumset_le_card_add X).trans (by grind)⟩
  have h := ncard_le_card_mul_pow_of_coversFreimanIsoClasses (hcover.subset hsub)
    fun X ⟨hXn, hX, hXr, _⟩ ↦ ⟨card_pos.1 (hX ▸ pos_of_smallSumsetClassCountThreshold_le ht),
      hXn, hXr⟩
  refine (Nat.cast_le.2 h).trans ?_
  rw [Nat.cast_mul, Nat.cast_pow, mul_comm, mul_assoc]
  refine (mul_le_mul_of_nonneg_left hcard (by positivity)).trans_eq ?_
  push_cast
  ring

end

end CountingSetsWithSmallSumset
