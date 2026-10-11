/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.DimensionAndCounting

/-!
# Cores of sets with small sumset and covers by Freiman isomorphism classes

This file follows Section 4 of Green's paper *Counting sets with small sumset, and the clique
number of random Cayley graphs*. Let `A` be a set of `t` natural numbers whose restricted sumset
has at most `m` elements. Green's Proposition 15 gives a small core `A₀ ⊆ A` and a set `A₁ ⊆ A`
with few elements missing such that a translate of `A₁` lies in the restricted sumset of `A₀`.
The Freiman isomorphism class of order `8` of `A₀` restricts the class of order `4` of `A₁`, which
restricts the class of order `2` of `A`. Counting the possibilities at each step covers the family
of all such `A` by few Freiman isomorphism classes of order `2`.

## Main definitions

* `FreimanEquivalent`: two finite sets of natural numbers are Freiman isomorphic of a given order.
* `CoversFreimanClasses`: a finite family meets every Freiman isomorphism class of a family.
* `smallRestrictedSumsetSets`: the `t`-sets whose restricted sumset has at most `m` elements.
* `freimanClassCountBound`: the sum that bounds the number of classes.

## Main statements

* `exists_core_decomposition_with_card_bounds`: Green's Proposition 15 with explicit parameters.
* `exists_remainderFreimanClassCover`: Green's Lemma 17, the subsets of size `u` of the restricted
  sumsets of the sets in one class of order `8` lie in few classes of order `4`.
* `exists_extensionFreimanClassCover`: the sets obtained by adding `d` elements to the sets of one
  class of order `4` lie in few classes of order `2`.
* `exists_smallRestrictedSumsetFreimanClassCover_raw`: the family `smallRestrictedSumsetSets t m`
  is covered by at most `freimanClassCountBound t m` classes of order `2`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

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

/-- The rate `t ^ (-1 / 15)` at which the elements of a `t`-set are sampled to form its core. -/
def coreSamplingRate (t : ℕ) : ℝ :=
  (t : ℝ) ^ (-(1 : ℝ) / 15)

/-- The number `⌊t ^ (1 / 5)⌋` of representations above which a sum is popular. -/
def popularSumThreshold (t : ℕ) : ℕ :=
  ⌊(t : ℝ) ^ ((1 : ℝ) / 5)⌋₊

/-- The weight `t ^ (11 / 15)` of an exceptional element in the core decomposition. -/
def exceptionPenalty (t : ℕ) : ℝ :=
  (t : ℝ) ^ ((11 : ℝ) / 15)

/-- The bound for the size of the core plus `exceptionPenalty t` times the number of exceptional
elements, for a `t`-set whose restricted sumset has at most `m` elements. -/
def coreDecompositionBudget (t m : ℕ) : ℝ :=
  coreSamplingRate t * t + exceptionPenalty t *
    (1 + (popularSumThreshold t : ℝ) * m / t +
      t * (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2))

lemma exceptionPenalty_mul_rpow_one_fifth {t : ℕ} (ht : 0 < t) :
    exceptionPenalty t * (t : ℝ) ^ ((1 : ℝ) / 5) =
      coreSamplingRate t * t := by
  have htReal : (0 : ℝ) < t := mod_cast ht
  unfold coreSamplingRate exceptionPenalty
  rw [← Real.rpow_add htReal, ← Real.rpow_add_one htReal.ne']
  norm_num

lemma exceptionPenalty_mul_rpow_neg_four_fifths {t : ℕ} (ht : 0 < t) :
    exceptionPenalty t * (t : ℝ) ^ (-(4 : ℝ) / 5) =
      coreSamplingRate t := by
  unfold coreSamplingRate exceptionPenalty
  rw [← Real.rpow_add (mod_cast ht)]
  norm_num

lemma one_lt_of_smallSumsetClassCountThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : 1 < t := by
  rw [smallSumsetClassCountThreshold_def] at ht
  exact (Nat.one_lt_two_pow (by norm_num)).trans_le ht

private lemma one_lt_cast_of_smallSumsetClassCountThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : (1 : ℝ) < t :=
  mod_cast one_lt_of_smallSumsetClassCountThreshold_le ht

lemma coreSamplingRate_pos {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : 0 < coreSamplingRate t := by
  unfold coreSamplingRate
  exact Real.rpow_pos_of_pos (by linarith [one_lt_cast_of_smallSumsetClassCountThreshold_le ht]) _

lemma coreSamplingRate_lt_one {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : coreSamplingRate t < 1 := by
  unfold coreSamplingRate
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_cast_of_smallSumsetClassCountThreshold_le ht)
    (by norm_num)

lemma exceptionPenalty_nonneg (t : ℕ) :
    0 ≤ exceptionPenalty t := by
  unfold exceptionPenalty
  positivity

lemma one_hundred_eighty_le_rpow_one_thirtieth {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (180 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 30) := by
  rw [smallSumsetClassCountThreshold_def] at ht
  have htReal : (2 : ℝ) ^ (9000 : ℕ) ≤ t := mod_cast ht
  have h₈ : (180 : ℝ) ≤ 2 ^ (8 : ℕ) := by norm_num
  refine le_trans (h₈.trans ?_) (Real.rpow_le_rpow (by positivity) htReal (by norm_num))
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)

private lemma one_hundred_eighty_le_rpow_one_fifth {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (180 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 5) := by
  have hz := one_hundred_eighty_le_rpow_one_thirtieth ht
  have hpow : (t : ℝ) ^ ((1 : ℝ) / 5) = ((t : ℝ) ^ ((1 : ℝ) / 30)) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hpow]
  exact hz.trans (le_self_pow₀ (by linarith) (by norm_num))

lemma popularSumThreshold_lower {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (t : ℝ) ^ ((1 : ℝ) / 5) / 2 ≤ popularSumThreshold t := by
  unfold popularSumThreshold
  linarith [Nat.lt_floor_add_one ((t : ℝ) ^ ((1 : ℝ) / 5)),
    one_hundred_eighty_le_rpow_one_fifth ht]

lemma popularSumThreshold_half_lower {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (t : ℝ) ^ ((1 : ℝ) / 5) / 6 ≤
      (popularSumThreshold t / 2 : ℕ) := by
  have hdiv : (popularSumThreshold t : ℝ) ≤ 2 * (popularSumThreshold t / 2 : ℕ) + 1 := by
    norm_cast
    grind
  linarith [popularSumThreshold_lower ht, one_hundred_eighty_le_rpow_one_fifth ht]

lemma rpow_one_fifteenth_le_six_mul_log_bound {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (4 : ℝ) / 5 * Real.log t ≤ (t : ℝ) ^ ((1 : ℝ) / 15) / 6 := by
  have htPos : (0 : ℝ) < t := by linarith [one_lt_cast_of_smallSumsetClassCountThreshold_le ht]
  have hz := one_hundred_eighty_le_rpow_one_thirtieth ht
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htPos ((1 : ℝ) / 30))
  have hpow : (t : ℝ) ^ ((1 : ℝ) / 15) = ((t : ℝ) ^ ((1 : ℝ) / 30)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  rw [Real.log_rpow htPos] at hlog
  rw [hpow]
  nlinarith

lemma coreSamplingRate_sq_mul_rpow_one_fifth {t : ℕ} (ht : 0 < t) :
    coreSamplingRate t ^ (2 : ℕ) * (t : ℝ) ^ ((1 : ℝ) / 5) =
      (t : ℝ) ^ ((1 : ℝ) / 15) := by
  unfold coreSamplingRate
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_add (mod_cast ht)]
  norm_num

lemma samplingFailureProbability_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2) ≤
      (t : ℝ) ^ (-(4 : ℝ) / 5) := by
  have ht_pos : 0 < t := Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  rw [Real.rpow_def_of_pos (mod_cast ht_pos)]
  refine (pow_le_pow_left₀ (by nlinarith [coreSamplingRate_pos ht, coreSamplingRate_lt_one ht])
    (Real.one_sub_le_exp_neg _) _).trans ?_
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  linarith [mul_le_mul_of_nonneg_left (popularSumThreshold_half_lower ht)
      (sq_nonneg (coreSamplingRate t)),
    rpow_one_fifteenth_le_six_mul_log_bound ht, coreSamplingRate_sq_mul_rpow_one_fifth ht_pos]

lemma exists_core_decomposition_with_budget (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a A₀ Z, a ∈ A ∧ A₀ ⊆ A ∧ Z ⊆ A ∧
      (A \ Z).image (a + ·) ⊆ restrictedSumset A₀ ∧
      (A₀.card : ℝ) + exceptionPenalty t * Z.card ≤
        coreDecompositionBudget t m := by
  have hA0 : A.Nonempty := Finset.card_pos.mp (hA.trans_gt
    (one_lt_of_smallSumsetClassCountThreshold_le ht).le)
  simpa only [coreDecompositionBudget] using exists_core_decomposition A hA hA0 hm
    (popularSumThreshold t) (coreSamplingRate_pos ht)
    (coreSamplingRate_lt_one ht) (exceptionPenalty_nonneg t)

/-- Two finite sets of natural numbers are Freiman equivalent of order `order` if there is a
Freiman isomorphism of that order from one onto the other. -/
def FreimanEquivalent (order : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ f : ℕ → ℕ, IsAddFreimanIso order (A : Set ℕ) (B : Set ℕ) f

/-- `representatives` contains a representative of every Freiman class meeting `family`. -/
def CoversFreimanClasses (order : ℕ) (family : Set (Finset ℕ))
    (representatives : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ family, ∃ B ∈ representatives, FreimanEquivalent order A B

/-- Integer `t`-sets whose restricted sumset has size at most `m`. -/
def smallRestrictedSumsetSets (t m : ℕ) : Set (Finset ℕ) :=
  {A | A.card = t ∧ (restrictedSumset A).card ≤ m}

/-- The integral upper bound for the size of Green's sampled core. -/
def coreCardBound (t m : ℕ) : ℕ :=
  ⌈4 * coreSamplingRate t * m⌉₊

/-- The integral upper bound for the number of exceptional elements. -/
def exceptionCardBound (t m : ℕ) : ℕ :=
  ⌈4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m⌉₊

private lemma add_mem_restrictedSumset {A : Finset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) : a + b ∈ restrictedSumset A :=
  Finset.mem_image.mpr ⟨(a, b), by simp [ha, hb, hab], rfl⟩

private lemma restrictedSumset_mono {A B : Finset ℕ} (h : A ⊆ B) :
    restrictedSumset A ⊆ restrictedSumset B :=
  Finset.image_subset_image (Finset.filter_subset_filter _ (Finset.product_subset_product h h))

private lemma image_add_erase_subset_restrictedSumset {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    (A.erase a).image (a + ·) ⊆ restrictedSumset A := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact add_mem_restrictedSumset ha (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm

/-- The restricted sumset of a set `A` of at least three natural numbers has at least `|A|`
elements. With `a` the least and `M` the greatest element of `A`, it contains the sums `a + x`
for `x ≠ a` and a sum `b + M` greater than all of them. -/
lemma card_le_card_restrictedSumset_of_three_le (A : Finset ℕ) (hA : 3 ≤ A.card) :
    A.card ≤ (restrictedSumset A).card := by
  have hne : A.Nonempty := Finset.card_pos.mp (by grind)
  set a := A.min' hne
  set M := A.max' hne
  have ha : a ∈ A := A.min'_mem hne
  obtain ⟨b, hb⟩ : ((A.erase a).erase M).Nonempty := by
    rw [← Finset.card_pos]
    grind [Finset.pred_card_le_card_erase]
  simp only [Finset.mem_erase] at hb
  have hab : a < b := (A.min'_le b hb.2.2).lt_of_ne' hb.2.1
  have hsub : insert (b + M) ((A.erase a).image (a + ·)) ⊆ restrictedSumset A :=
    Finset.insert_subset (add_mem_restrictedSumset hb.2.2 (A.max'_mem hne) hb.1)
      (image_add_erase_subset_restrictedSumset ha)
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (add_right_injective a),
    Finset.card_erase_of_mem ha]
  · grind
  · intro h
    obtain ⟨x, hx, hxb⟩ := Finset.mem_image.mp h
    have hxM : x ≤ M := A.le_max' x (Finset.mem_of_mem_erase hx)
    grind

private lemma card_le_of_card_restrictedSumset_le {A : Finset ℕ} {t m : ℕ} (hA : A.card = t)
    (ht : smallSumsetClassCountThreshold ≤ t) (hm : (restrictedSumset A).card ≤ m) : t ≤ m := by
  subst hA
  have h₃ : 3 ≤ A.card :=
    le_trans (by norm_num) (two_pow_200_le_smallSumsetClassCountThreshold.trans ht)
  exact (card_le_card_restrictedSumset_of_three_le A h₃).trans hm

/-- The numerical specialization of Green's alteration budget. -/
lemma coreDecompositionBudget_le_four_mul_samplingRate {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m) :
    coreDecompositionBudget t m ≤ 4 * coreSamplingRate t * m := by
  have ht_pos : 0 < t := Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real := one_lt_cast_of_smallSumsetClassCountThreshold_le ht
  have hR := exceptionPenalty_nonneg t
  have h₁ : exceptionPenalty t ≤ coreSamplingRate t * t := by
    rw [← exceptionPenalty_mul_rpow_one_fifth ht_pos]
    exact le_mul_of_one_le_right hR (Real.one_le_rpow ht_real.le (by norm_num))
  have h₂ : exceptionPenalty t * (popularSumThreshold t * m / t) ≤ coreSamplingRate t * m := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith), mul_right_comm,
      ← exceptionPenalty_mul_rpow_one_fifth ht_pos, ← mul_assoc]
    gcongr
    exact Nat.floor_le (by positivity)
  have h₃ : exceptionPenalty t *
      (t * (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2)) ≤
        coreSamplingRate t * t := by
    conv_rhs => rw [← exceptionPenalty_mul_rpow_neg_four_fifths ht_pos]
    rw [mul_assoc, mul_comm (t : ℝ)]
    gcongr
    exact samplingFailureProbability_le ht
  unfold coreDecompositionBudget
  rw [mul_add, mul_add, mul_one]
  linarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr htm) (coreSamplingRate_pos ht).le]

/-- Green's Proposition 15 with all asymptotic notation replaced by the explicit parameters used
in the class count. A `t`-set `A` whose restricted sumset has at most `m` elements has a core
`A₀` with at most `4 * t ^ (-1 / 15) * m` elements and a subset `A₁` missing at most
`4 * t ^ (-4 / 5) * m` elements such that a translate of `A₁` lies in the restricted sumset of
`A₀`. -/
theorem exists_core_decomposition_with_card_bounds (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ A₁ ⊆ A,
      A₁.image (a + ·) ⊆ restrictedSumset A₀ ∧
      (A₀.card : ℝ) ≤ 4 * coreSamplingRate t * m ∧
      ((A \ A₁).card : ℝ) ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m := by
  have ht_pos : 0 < t := Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have hle := coreDecompositionBudget_le_four_mul_samplingRate ht
    (card_le_of_card_restrictedSumset_le hA ht hm)
  have hR : 0 < exceptionPenalty t := by
    unfold exceptionPenalty
    positivity
  obtain ⟨a, A₀, Z, ha, hA₀, hZ, htranslate, hbudget⟩ :=
    exists_core_decomposition_with_budget A hA ht hm
  refine ⟨a, ha, A₀, hA₀, A \ Z, Finset.sdiff_subset, htranslate, ?_, ?_⟩
  · linarith [mul_nonneg hR.le (Nat.cast_nonneg (α := ℝ) Z.card)]
  · rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hZ]
    rw [← exceptionPenalty_mul_rpow_neg_four_fifths ht_pos] at hle
    refine le_of_mul_le_mul_left ?_ hR
    linarith [Nat.cast_nonneg (α := ℝ) A₀.card]

private lemma exists_sum_map_eq_sum_fin {s t : ℕ} {a : Fin t → ℕ} {u : Multiset ℕ}
    (hu : ∀ x ∈ u, x ∈ Set.range a) (hcard : u.card = s) :
    ∃ p : Fin s → Fin t, ∀ f : ℕ → ℕ, (u.map f).sum = ∑ i, f (a (p i)) := by
  obtain rfl : u.toList.length = s := (Multiset.length_toList u).trans hcard
  choose p hp using fun i : Fin u.toList.length ↦
    hu u.toList[i.1] (Multiset.mem_toList.mp (List.getElem_mem i.2))
  refine ⟨p, fun f ↦ ?_⟩
  simp only [hp]
  rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem]

private lemma exists_isAddFreimanIso_range {s t : ℕ} {a b : Fin t → ℕ}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (h : ∀ p : FreimanRelationIndex s t, freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    ∃ f : ℕ → ℕ, IsAddFreimanIso s (Set.range a) (Set.range b) f := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ → ℕ, f ∘ a = b :=
    ⟨Function.extend a b 0, funext (ha.extend_apply b 0)⟩
  refine ⟨f, ?_, fun u v hu hv hu_card hv_card ↦ ?_⟩
  · rw [Set.range_comp]
    exact hb.injOn_range.bijOn_image
  · obtain ⟨p, hp⟩ := exists_sum_map_eq_sum_fin hu hu_card
    obtain ⟨q, hq⟩ := exists_sum_map_eq_sum_fin hv hv_card
    rw [hp f, hq f, ← u.map_id, ← v.map_id, hp id, hq id]
    exact (h (p, q)).symm

/-- Two sets with the same canonical relation code of order `s` are Freiman equivalent of
order `s`. -/
lemma freimanEquivalent_of_canonicalCode_eq {s t : ℕ} (ht : 0 < t) (X Y : SizedNatFinset t)
    (hcode : canonicalFreimanRelationCode (s := s) ht X =
             canonicalFreimanRelationCode (s := s) ht Y) :
    FreimanEquivalent s X.1 Y.1 := by
  obtain ⟨eX, hcodeX⟩ := exists_canonicalLabeling (s := s) ht X
  obtain ⟨eY, hcodeY⟩ := exists_canonicalLabeling (s := s) ht Y
  have h := exists_isAddFreimanIso_range (permutedFinsetTuple_injective X eX)
    (permutedFinsetTuple_injective Y eY)
    (freimanRelations_iff_of_code_eq ht (by rw [hcodeX, hcodeY, hcode]))
  rwa [range_permutedFinsetTuple, range_permutedFinsetTuple] at h

private lemma freimanRelationHolds_comp_iff {s t : ℕ} {A B : Set ℕ} {f : ℕ → ℕ}
    (hf : IsAddFreimanIso s A B f) {a : Fin t → ℕ} (ha : ∀ i, a i ∈ A)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds (f ∘ a) p ↔ freimanRelationHolds a p := by
  have h := hf.map_sum_eq_map_sum (s := Finset.univ.val.map fun i ↦ a (p.1 i))
    (t := Finset.univ.val.map fun i ↦ a (p.2 i)) (by simp [ha]) (by simp [ha]) (by simp)
    (by simp)
  rw [Multiset.map_map, Multiset.map_map] at h
  exact h

private lemma exists_perm_comp_eq {t : ℕ} (ht : 0 < t) {b c : Fin t → ℕ}
    (hc : Function.Injective c) (h : ∀ i, c i ∈ Set.range b) :
    ∃ e : Equiv.Perm (Fin t), b ∘ e = c := by
  have : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  have he : b ∘ Function.invFun b ∘ c = c := funext fun i ↦ Function.invFun_eq (h i)
  rw [← he] at hc
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hc.of_comp), he⟩

/-- Two `t`-sets that are Freiman equivalent of order `s` satisfy the same additive relations of
order `s`, after a permutation of their elements. -/
lemma freimanEquivalent_implies_freimanRelationEquivalent {s t : ℕ} (ht : 0 < t)
    {A B : Finset ℕ} (hA : A.card = t) (hB : B.card = t)
    (h : FreimanEquivalent s A B) :
    FreimanRelationEquivalent (s := s) (⟨A, hA⟩ : SizedNatFinset t)
      (⟨B, hB⟩ : SizedNatFinset t) := by
  obtain ⟨f, hf⟩ := h
  have hmem (i : Fin t) : finsetTuple A hA i ∈ (A : Set ℕ) :=
    range_finsetTuple A hA ▸ Set.mem_range_self i
  obtain ⟨e, he⟩ := exists_perm_comp_eq ht (b := finsetTuple B hB) (c := f ∘ finsetTuple A hA)
    (fun i j hij ↦ finsetTuple_injective A hA (hf.bijOn.injOn (hmem i) (hmem j) hij))
    (fun i ↦ range_finsetTuple B hB ▸ hf.bijOn.mapsTo (hmem i))
  refine ⟨e, fun p ↦ ?_⟩
  change _ ↔ freimanRelationHolds (finsetTuple B hB ∘ e) p
  rw [he, freimanRelationHolds_comp_iff hf hmem]

/-- Sets obtained by adjoining `d` elements to some member of the `4`-class of `base`. -/
def extensionsOfFreimanClass (base : Finset ℕ) (d : ℕ) : Set (Finset ℕ) :=
  {A | ∃ B : Finset ℕ, B ⊆ A ∧ B.card = base.card ∧
    A.card = B.card + d ∧ FreimanEquivalent 4 B base}

private lemma freimanRelationEquivalent_symm {s t : ℕ} {X Y : SizedNatFinset t}
    (h : FreimanRelationEquivalent (s := s) X Y) :
    FreimanRelationEquivalent (s := s) Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun p ↦ ?_⟩
  simpa only [permutedFinsetTuple, freimanRelationHolds_comp_perm,
    freimanRelationHolds, permuteFreimanRelation, Equiv.coe_trans,
    Function.comp_def, Equiv.apply_symm_apply] using
    (he (permuteFreimanRelation e.symm p)).symm

/-- A family of `n`-sets is covered by representatives in the family on which the canonical
relation code of order `s` is injective. -/
private lemma exists_injOn_canonicalCode_freimanClassCover {s n : ℕ} (hn : 0 < n)
    (family : Set (Finset ℕ)) (hfamily : ∀ A ∈ family, A.card = n) :
    ∃ reps : Finset (SizedNatFinset n), (∀ Y ∈ reps, Y.1 ∈ family) ∧
      Set.InjOn (canonicalFreimanRelationCode (s := s) hn) reps ∧
      CoversFreimanClasses s family (reps.image Subtype.val) := by
  obtain ⟨reps, hreps, hbij⟩ := Set.exists_subset_bijOn {X : SizedNatFinset n | X.1 ∈ family}
    (canonicalFreimanRelationCode (s := s) hn)
  lift reps to Finset (SizedNatFinset n) using
    Set.Finite.of_finite_image (Set.toFinite _) hbij.injOn
  refine ⟨reps, fun Y hY ↦ hreps hY, hbij.injOn, fun A hA ↦ ?_⟩
  have hX : (⟨A, hfamily A hA⟩ : SizedNatFinset n) ∈ {X : SizedNatFinset n | X.1 ∈ family} := hA
  obtain ⟨Y, hY, hcode⟩ := hbij.surjOn (Set.mem_image_of_mem _ hX)
  exact ⟨Y.1, Finset.mem_image_of_mem _ hY,
    freimanEquivalent_of_canonicalCode_eq hn _ Y hcode.symm⟩

private lemma card_eq_of_mem_extensionsOfFreimanClass {base A : Finset ℕ} {d : ℕ}
    (hA : A ∈ extensionsOfFreimanClass base d) : A.card = base.card + d := by
  obtain ⟨B, -, hB, hA, -⟩ := hA
  rw [hA, hB]

private lemma exists_extensionLabeling {base : Finset ℕ} {d : ℕ} (hbase : 0 < base.card)
    (X : SizedNatFinset (base.card + d)) (hX : X.1 ∈ extensionsOfFreimanClass base d) :
    ∃ a : Fin (base.card + d) → ℕ, Function.Injective a ∧ Set.range a = X.1 ∧
      ∀ p : FreimanRelationIndex 4 base.card,
        freimanRelationHolds (extensionBaseTuple a) p ↔
          freimanRelationHolds (finsetTuple base rfl) p := by
  obtain ⟨B, hB, hB_card, hX_card, hB_equiv⟩ := hX
  have hZ : (X.1 \ B).card = d := by
    grind [Finset.card_sdiff_add_card_eq_card hB]
  obtain ⟨e, he⟩ := freimanRelationEquivalent_symm
    (freimanEquivalent_implies_freimanRelationEquivalent hbase hB_card rfl hB_equiv)
  refine ⟨extensionFinsetTuple X.1 B hB_card hZ e, extensionFinsetTuple_injective hB_card hZ e,
    range_extensionFinsetTuple hB hB_card hZ e, fun p ↦ ?_⟩
  rw [extensionBaseTuple_extensionFinsetTuple X.1 B hB_card hZ e]
  exact (he p).symm

/-- Green's extension lemma in class-cover form. The sets obtained by adjoining `d` elements to
a member of the `4`-class of `base` lie in at most `(1 + |base| ^ 4) ^ ((d + 1) ^ 4)` classes of
order `2`. -/
lemma exists_extensionFreimanClassCover (base : Finset ℕ) (d : ℕ)
    (hbase : base.Nonempty) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 2 (extensionsOfFreimanClass base d) representatives ∧
      representatives.card ≤
        (1 + base.card ^ 4) ^ ((d + 1) ^ 4) := by
  have hl : 0 < base.card := hbase.card_pos
  obtain ⟨reps, hmem, hinj, hcover⟩ := exists_injOn_canonicalCode_freimanClassCover (s := 2)
    (Nat.add_pos_left hl d) (extensionsOfFreimanClass base d)
    (fun _ ↦ card_eq_of_mem_extensionsOfFreimanClass)
  choose! label hlabel_inj hlabel_range hlabel using fun X (hX : X ∈ reps) ↦
    exists_extensionLabeling hl X (hmem X hX)
  refine ⟨reps.image Subtype.val, hcover, Finset.card_image_le.trans ?_⟩
  rw [← Finset.card_image_of_injOn hinj]
  exact card_canonicalFreimanRelationCode_image_of_fixed_extensionBase hl reps (fun X ↦ X) label
    hlabel_inj hlabel_range fun X hX Y hY p ↦ (hlabel X hX p).trans (hlabel Y hY p).symm

/-- Sets of size `u` contained in the restricted sumset of some member of the `8`-class of
`core`. -/
def remaindersFromCoreClass (core : Finset ℕ) (u : ℕ) : Set (Finset ℕ) :=
  {B | B.card = u ∧ ∃ C : Finset ℕ,
    C.card = core.card ∧ FreimanEquivalent 8 C core ∧ B ⊆ restrictedSumset C}

/-- Green's Lemma 17: after fixing the core's `8`-class, the possible remainders occupy at most
`choose |core ⊕ core| u` many `4`-relation classes. -/
lemma exists_remainderFreimanClassCover (core : Finset ℕ) (u : ℕ)
    (hcore : core.Nonempty) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 4 (remaindersFromCoreClass core u) representatives ∧
      (∀ R ∈ representatives, R.card = u) ∧
      representatives.card ≤ (restrictedSumset core).card.choose u := by
  have hl : 0 < core.card := hcore.card_pos
  obtain rfl | hu := Nat.eq_zero_or_pos u
  · refine ⟨{∅}, ?_, by simp, by simp⟩
    rintro A ⟨hA, -⟩
    obtain rfl := Finset.card_eq_zero.mp hA
    exact ⟨∅, by simp, id, isAddFreimanIso_id⟩
  obtain ⟨reps, hmem, hinj, hcover⟩ := exists_injOn_canonicalCode_freimanClassCover (s := 4) hu
    (remaindersFromCoreClass core u) (fun A hA ↦ hA.1)
  refine ⟨reps.image Subtype.val, hcover, ?_, Finset.card_image_le.trans ?_⟩
  · intro R hR
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.mp hR
    exact Y.2
  · rw [← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset, Finset.coe_image]
    refine ncard_restrictedSumset_subset_class_image_le hl hu ⟨core, rfl⟩ _ fun B hB ↦ ?_
    obtain ⟨-, C, hC_card, hC_equiv, hB_subset⟩ := hmem B hB
    exact ⟨⟨C, hC_card⟩, hB_subset, canonicalFreimanRelationCode_eq_of_equivalent hl
      (freimanEquivalent_implies_freimanRelationEquivalent hl hC_card rfl hC_equiv)⟩

/-- The bound for the number of Freiman classes of order `2` that cover
`smallRestrictedSumsetSets t m`. It is a sum over the number `d` of exceptional elements and the
size `l` of the core of the number of classes of the core, of the remainder and of the
extension. -/
def freimanClassCountBound (t m : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (exceptionCardBound t m + 1),
    ∑ l ∈ Finset.Icc 1 (coreCardBound t m),
      l ^ (16 * l) * m.choose (t - d) *
        (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4)

private lemma freimanEquivalent_trans {order : ℕ} {A B C : Finset ℕ}
    (hAB : FreimanEquivalent order A B) (hBC : FreimanEquivalent order B C) :
    FreimanEquivalent order A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf⟩

private lemma freimanEquivalent_translate (order a : ℕ) (A : Finset ℕ) :
    FreimanEquivalent order A (A.image (a + ·)) := by
  have hsum (w : Multiset ℕ) : (w.map (a + ·)).sum = w.card * a + w.sum := by
    rw [Multiset.sum_map_add]
    simp
  refine ⟨(a + ·), ?_, fun u v _ _ hu hv ↦ ?_⟩
  · rw [Finset.coe_image]
    exact (add_right_injective a).injOn.bijOn_image
  · rw [hsum, hsum, hu, hv, add_right_inj]

private lemma exists_exactSmallCoreFreimanClassCover (l m : ℕ) (hl : 0 < l) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 8
        {A | A.card = l ∧ (restrictedSumset A).card ≤ m} representatives ∧
      (∀ C ∈ representatives, C.card = l ∧ (restrictedSumset C).card ≤ m) ∧
      representatives.card ≤ l ^ (16 * l) := by
  obtain ⟨reps, hmem, hinj, hcover⟩ := exists_injOn_canonicalCode_freimanClassCover (s := 8) hl
    {A | A.card = l ∧ (restrictedSumset A).card ≤ m} (fun A hA ↦ hA.1)
  refine ⟨reps.image Subtype.val, hcover, ?_, Finset.card_image_le.trans ?_⟩
  · intro C hC
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hC
    exact hmem Y hY
  · exact (Finset.card_le_card_of_injOn _ (fun _ _ ↦ Finset.mem_univ _) hinj).trans_eq
      (card_freimanRelationCodes 8 l)

private lemma exists_nonemptyCoreDecomposition (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ A₁ ⊆ A,
      A₁.image (a + ·) ⊆ restrictedSumset A₀ ∧ A₀.Nonempty ∧ A₁.Nonempty ∧
      A₀.card ≤ coreCardBound t m ∧
      (A \ A₁).card ≤ exceptionCardBound t m := by
  have ht₁ := one_lt_of_smallSumsetClassCountThreshold_le ht
  have ht_real := one_lt_cast_of_smallSumsetClassCountThreshold_le ht
  have ht_pos : 0 < t := by grind
  have hm_pos : 0 < m := ht_pos.trans_le (card_le_of_card_restrictedSumset_le hA ht hm)
  by_cases hlarge : t ≤ coreCardBound t m
  · obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by grind)
    refine ⟨a, ha, A, subset_rfl, A.erase a, A.erase_subset a,
      image_add_erase_subset_restrictedSumset ha, ⟨a, ha⟩, ?_, hA ▸ hlarge, ?_⟩
    · rw [← Finset.card_pos, Finset.card_erase_of_mem ha]
      grind
    · rw [Finset.sdiff_erase_self ha, Finset.card_singleton, exceptionCardBound,
        Nat.one_le_ceil_iff]
      positivity
  · obtain ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, hcore, hexception⟩ :=
      exists_core_decomposition_with_card_bounds A hA ht hm
    have hpow : (t : ℝ) ^ (-(4 : ℝ) / 5) < coreSamplingRate t :=
      Real.rpow_lt_rpow_of_exponent_lt ht_real (by norm_num)
    have hcore_lt : 4 * coreSamplingRate t * m < t :=
      (Nat.le_ceil _).trans_lt (mod_cast not_le.mp hlarge)
    have hm_real : (0 : ℝ) < m := mod_cast hm_pos
    have hdiff_lt : (A \ A₁).card < t := by
      rw [← Nat.cast_lt (α := ℝ)]
      nlinarith
    have hA₁_nonempty : A₁.Nonempty := by
      rw [← Finset.card_pos]
      grind [Finset.card_sdiff_add_card_eq_card hA₁]
    refine ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, ?_, hA₁_nonempty, ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp [restrictedSumset, hA₁_nonempty.ne_empty] at htranslate
    · exact Nat.cast_le (α := ℝ).mp (hcore.trans (Nat.le_ceil _))
    · exact Nat.cast_le (α := ℝ).mp (hexception.trans (Nat.le_ceil _))

/-- The sets `A` of `smallRestrictedSumsetSets t m` that have a core of size `l` and a subset
`A₁` missing `d` elements, a translate of which lies in the restricted sumset of the core, are
covered by few classes of order `2`. The class of order `8` of the core, then the class of order
`4` of the translate of `A₁`, then the class of order `2` of `A` are chosen in turn. -/
private lemma exists_freimanClassCover_of_card_core_of_card_exception (t m d l : ℕ)
    (hl : 0 < l) :
    ∃ representatives : Finset (Finset ℕ),
      representatives.card ≤
        l ^ (16 * l) * m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) ∧
      ∀ A ∈ smallRestrictedSumsetSets t m, ∀ a : ℕ, ∀ A₀ ⊆ A, ∀ A₁ ⊆ A,
        A₁.image (a + ·) ⊆ restrictedSumset A₀ → A₁.Nonempty → A₀.card = l →
          (A \ A₁).card = d → ∃ Q ∈ representatives, FreimanEquivalent 2 A Q := by
  obtain hu | hu := Nat.eq_zero_or_pos (t - d)
  · refine ⟨∅, by simp, ?_⟩
    rintro A ⟨hA, -⟩ a A₀ - A₁ hA₁ - hA₁_nonempty - hd
    grind [Finset.card_sdiff_add_card_eq_card hA₁, hA₁_nonempty.card_pos]
  obtain ⟨coreReps, hcore_cover, hcore_spec, hcore_card⟩ :=
    exists_exactSmallCoreFreimanClassCover l m hl
  choose! remainderReps hremainder_cover hremainder_spec hremainder_card using
    fun C (hC : C.card = l) ↦
      exists_remainderFreimanClassCover C (t - d) (Finset.card_pos.mp (hC ▸ hl))
  choose! extensionReps hextension_cover hextension_card using
    fun R (hR : R.card = t - d) ↦
      exists_extensionFreimanClassCover R d (Finset.card_pos.mp (hR ▸ hu))
  refine ⟨coreReps.biUnion fun C ↦ (remainderReps C).biUnion extensionReps, ?_, ?_⟩
  · refine (Finset.card_biUnion_le_card_mul _ _
      (m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4)) fun C hC ↦ ?_).trans ?_
    · obtain ⟨hC_card, hC_sumset⟩ := hcore_spec C hC
      refine (Finset.card_biUnion_le_card_mul _ _ _ fun R hR ↦ ?_).trans
        (Nat.mul_le_mul_right _ ((hremainder_card C hC_card).trans
          (Nat.choose_le_choose _ hC_sumset)))
      have hR_card := hremainder_spec C hC_card R hR
      exact hR_card ▸ hextension_card R hR_card
    · rw [mul_assoc]
      exact Nat.mul_le_mul_right _ hcore_card
  · rintro A ⟨hA, hm⟩ a A₀ hA₀ A₁ hA₁ htranslate - hl' hd
    have hcards := Finset.card_sdiff_add_card_eq_card hA₁
    have hA₁_card : A₁.card = t - d := by grind
    obtain ⟨C, hC, hA₀C⟩ := hcore_cover A₀
      ⟨hl', (Finset.card_le_card (restrictedSumset_mono hA₀)).trans hm⟩
    have hC_card := (hcore_spec C hC).1
    obtain ⟨R, hR, hBR⟩ := hremainder_cover C hC_card (A₁.image (a + ·))
      ⟨by rw [Finset.card_image_of_injective _ (add_right_injective a), hA₁_card], A₀,
        hl'.trans hC_card.symm, hA₀C, htranslate⟩
    have hR_card := hremainder_spec C hC_card R hR
    obtain ⟨Q, hQ, hAQ⟩ := hextension_cover R hR_card A
      ⟨A₁, hA₁, hA₁_card.trans hR_card.symm, by grind,
        freimanEquivalent_trans (freimanEquivalent_translate 4 a A₁) hBR⟩
    exact ⟨Q, Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_biUnion.mpr ⟨R, hR, hQ⟩⟩, hAQ⟩

/-- Combinatorial assembly of the three class covers, before estimating the resulting sum. The
family `smallRestrictedSumsetSets t m` is covered by at most `freimanClassCountBound t m` Freiman
classes of order `2`. -/
lemma exists_smallRestrictedSumsetFreimanClassCover_raw (t m : ℕ)
    (ht : smallSumsetClassCountThreshold ≤ t) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 2 (smallRestrictedSumsetSets t m) representatives ∧
      representatives.card ≤ freimanClassCountBound t m := by
  choose! reps hcard hcover using fun d l (hl : 0 < l) ↦
    exists_freimanClassCover_of_card_core_of_card_exception t m d l hl
  refine ⟨(Finset.range (exceptionCardBound t m + 1)).biUnion fun d ↦
    (Finset.Icc 1 (coreCardBound t m)).biUnion (reps d), fun A hA ↦ ?_, ?_⟩
  · obtain ⟨a, -, A₀, hA₀, A₁, hA₁, htranslate, hA₀_nonempty, hA₁_nonempty, hcore, hexception⟩ :=
      exists_nonemptyCoreDecomposition A hA.1 ht hA.2
    obtain ⟨Q, hQ, hAQ⟩ := hcover (A \ A₁).card A₀.card hA₀_nonempty.card_pos A hA a A₀ hA₀ A₁
      hA₁ htranslate hA₁_nonempty rfl rfl
    refine ⟨Q, ?_, hAQ⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc]
    exact ⟨_, Nat.lt_succ_of_le hexception, _, ⟨hA₀_nonempty.card_pos, hcore⟩, hQ⟩
  · unfold freimanClassCountBound
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun d _ ↦ ?_)
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l hl ↦ ?_)
    exact hcard d l (Finset.mem_Icc.mp hl).1

end

end CountingSetsWithSmallSumset
