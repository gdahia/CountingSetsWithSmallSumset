/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreParameters
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ExtensionAndRemainderClasses
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationSpaces

/-!
# Representatives of the Freiman isomorphism classes of sets with small restricted sumset

This file follows Section 4 of Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*. Let `A` be a set of `t` elements of a vector space whose restricted sumset
has at most `m ≥ t` elements. Proposition 15 gives a small core `A₀ ⊆ A` and a set `A₁ ⊆ A` with
few elements missing such that a translate of `A₁` lies in the restricted sumset of `A₀`. The
Freiman isomorphism class of order `8` of `A₀` restricts the class of order `4` of `A₁`
(Lemma 17), which restricts the class of order `2` of `A` (Lemma 16). Counting the possibilities
at each step shows that all such `A` lie in few Freiman isomorphism classes of order `2`.

## Main definitions

* `coreCardBound t m`, `exceptionCardBound t m`: the bounds `⌈4 t ^ (-1 / 15) m⌉` and
  `⌈4 t ^ (-4 / 5) m⌉` for the size of the core and the number of exceptional elements.
* `freimanClassCountBound t m`: the sum that bounds the number of classes.

## Main statements

* `exists_representsFreimanIsoClasses_card_le_freimanClassCountBound`: for `t ≤ m`, the sets of
  `t` elements of a vector space whose restricted sumset has at most `m` elements lie in at most
  `freimanClassCountBound t m` classes of order `2`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

noncomputable section

/-- The integral upper bound for the size of Green's sampled core. -/
def coreCardBound (t m : ℕ) : ℕ :=
  ⌈4 * (t : ℝ) ^ (-(1 : ℝ) / 15) * m⌉₊

/-- The integral upper bound for the number of exceptional elements. -/
def exceptionCardBound (t m : ℕ) : ℕ :=
  ⌈4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m⌉₊

/-- The bound for the number of Freiman classes of order `2` of the `t`-sets whose
restricted sumset has at most `m` elements. It is a sum over the number `d` of exceptional
elements and the size `l` of the core of the number of classes of the core, of the remainder and
of the extension. -/
def freimanClassCountBound (t m : ℕ) : ℕ :=
  ∑ d ∈ range (exceptionCardBound t m + 1), ∑ l ∈ Icc 1 (coreCardBound t m),
    l ^ (16 * l) * m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4)

section Cancel

variable {G : Type*} [AddCancelCommMonoid G] [DecidableEq G]

private lemma image_add_erase_subset_restrictedSumset {A : Finset G} {a : G} (ha : a ∈ A) :
    (A.erase a).image (a + ·) ⊆ restrictedSumset A := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact mem_restrictedSumset.mpr ⟨a, ha, x, mem_of_mem_erase hx, (ne_of_mem_erase hx).symm, rfl⟩

private lemma freimanIsomorphic_image_add (n : ℕ) (a : G) (A : Finset G) :
    FreimanIsomorphic n A (A.image (a + ·)) := by
  refine ⟨(a + ·), ?_, ?_⟩
  · rw [coe_image]
    exact (add_right_injective a).injOn.bijOn_image
  · intro u v _ _ hu hv
    rw [Multiset.sum_map_add, Multiset.sum_map_add]
    simp [hu, hv]

private lemma four_mul_rpow_neg_four_fifths_mul_lt {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (hlarge : ¬t ≤ coreCardBound t m) :
    4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m < t := by
  refine lt_of_le_of_lt ?_ ((Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr (not_le.mp hlarge)))
  gcongr 4 * ?_ * _
  exact Real.rpow_le_rpow_of_exponent_le
    (one_lt_natCast_of_smallSumsetClassCountThreshold_le ht).le (by norm_num)

private lemma exists_nonempty_image_add_subset_restrictedSumset {A : Finset G} {t m : ℕ}
    (hA : #A = t) (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m)
    (hm : #(restrictedSumset A) ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ A₁ ⊆ A,
      A₁.image (a + ·) ⊆ restrictedSumset A₀ ∧ A₀.Nonempty ∧ A₁.Nonempty ∧
      #A₀ ≤ coreCardBound t m ∧ #(A \ A₁) ≤ exceptionCardBound t m := by
  by_cases hlarge : t ≤ coreCardBound t m
  · have ht₁ := one_lt_of_smallSumsetClassCountThreshold_le ht
    obtain ⟨a, ha⟩ : A.Nonempty := card_pos.mp (by grind)
    refine ⟨a, ha, A, subset_rfl, A.erase a, A.erase_subset a,
      image_add_erase_subset_restrictedSumset ha, ⟨a, ha⟩, ?_, hA ▸ hlarge, ?_⟩
    · rw [← card_pos, card_erase_of_mem ha]
      grind
    · rw [sdiff_erase_self ha, card_singleton, exceptionCardBound, Nat.one_le_ceil_iff]
      have hm_pos : 0 < m := by grind
      positivity
  · obtain ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, hcore, hexception⟩ :=
      exists_image_add_subset_restrictedSumset hA ht htm hm
    obtain ⟨x, hx⟩ : A₁.Nonempty := by
      rw [← card_pos]
      grind [card_sdiff_add_card_eq_card hA₁,
        Nat.cast_lt.mp (hexception.trans_lt (four_mul_rpow_neg_four_fifths_mul_lt ht hlarge))]
    obtain ⟨b, hb, -⟩ := mem_restrictedSumset.mp (htranslate (mem_image_of_mem _ hx))
    refine ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, ⟨b, hb⟩, ⟨x, hx⟩, ?_, ?_⟩
    · exact Nat.cast_le (α := ℝ).mp (hcore.trans (Nat.le_ceil _))
    · exact Nat.cast_le (α := ℝ).mp (hexception.trans (Nat.le_ceil _))

end Cancel

variable (F : Type*) {W : Type*} [Field F] [AddCommGroup W] [Module F W] [DecidableEq W]

include F in
/-- The sets `A` of `t` elements of `W` whose restricted sumset has at most `m` elements, and that
have a core of size `l` and a subset `A₁` missing `d` elements a translate of which lies in the
restricted sumset of the core, lie in few classes of order `2`. The class of order `8` of
the core, then the class of order `4` of the translate of `A₁`, then the class of order `2` of `A`
are chosen in turn. -/
private lemma exists_freimanClassRepresentatives_of_card_core_of_card_exception (t m d l : ℕ) :
    ∃ representatives : Finset (Finset W),
      #representatives ≤ l ^ (16 * l) * m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) ∧
      ∀ A : Finset W, #A = t → #(restrictedSumset A) ≤ m → ∀ a : W, ∀ A₀ ⊆ A, ∀ A₁ ⊆ A,
        A₁.image (a + ·) ⊆ restrictedSumset A₀ → A₁.Nonempty → #A₀ = l →
          #(A \ A₁) = d → ∃ Q ∈ representatives, FreimanIsomorphic 2 A Q := by
  obtain hu | hu := Nat.eq_zero_or_pos (t - d)
  · refine ⟨∅, by simp, ?_⟩
    rintro A hA - a A₀ - A₁ hA₁ - hA₁_nonempty - hd
    grind [card_sdiff_add_card_eq_card hA₁, hA₁_nonempty.card_pos]
  obtain ⟨coreReps, hcore_mem, hcore_rep, hcore_card⟩ :=
    exists_subset_representsFreimanIsoClasses_card_le_pow F 8
      (family := {A : Finset W | #A = l ∧ #(restrictedSumset A) ≤ m}) fun _ ⟨hA, _⟩ ↦ hA
  choose remainderReps hremainder_rep hremainder_spec hremainder_card using
    fun C : Finset W ↦ exists_representsFreimanIsoClasses_remaindersFromCoreClass_card_le C (t - d)
  choose! extensionReps hextension_mem hextension_rep hextension_card using
    fun (R : Finset W) (hR : #R = t - d) ↦
      exists_representsFreimanIsoClasses_extensionsOfFreimanClass_card_le (card_pos.mp (hR ▸ hu)) d
  refine ⟨coreReps.biUnion fun C ↦ (remainderReps C).biUnion extensionReps, ?_, ?_⟩
  · refine (card_biUnion_le_card_mul _ _
      (m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4)) ?_).trans ?_
    · intro C hC
      obtain ⟨-, hC_sumset⟩ := hcore_mem hC
      refine (card_biUnion_le_card_mul _ _ _ ?_).trans
        (Nat.mul_le_mul_right _ ((hremainder_card C).trans (Nat.choose_le_choose _ hC_sumset)))
      intro R hR
      have hR_card := hremainder_spec C R hR
      exact hR_card ▸ hextension_card R hR_card
    · rw [mul_assoc]
      exact Nat.mul_le_mul_right _ (hcore_card.trans_eq (by ring))
  · rintro A hA hm a A₀ hA₀ A₁ hA₁ htranslate - hl hd
    have hA₁_card : #A₁ = t - d := by grind [card_sdiff_add_card_eq_card hA₁]
    obtain ⟨C, hC, hA₀C⟩ :=
      hcore_rep A₀ ⟨hl, (card_le_card (restrictedSumset_mono hA₀)).trans hm⟩
    obtain ⟨R, hR, hBR⟩ := hremainder_rep C (A₁.image (a + ·))
      ⟨(card_image_of_injective _ (add_right_injective a)).trans hA₁_card, A₀, hA₀C, htranslate⟩
    have hR_card := hremainder_spec C R hR
    obtain ⟨Q, hQ, hAQ⟩ := hextension_rep R hR_card A
      ⟨A₁, hA₁, hA₁_card.trans hR_card.symm, by grind [card_sdiff_add_card_eq_card hA₁],
        (freimanIsomorphic_image_add 4 a A₁).trans hBR⟩
    exact ⟨Q, mem_biUnion.mpr ⟨C, hC, mem_biUnion.mpr ⟨R, hR, hQ⟩⟩, hAQ⟩

variable (W)

include F in
/-- Let `W` be a vector space over a field `F`, let `t ≥ 2 ^ 9000` and `t ≤ m`. The sets of `t`
elements of `W` whose restricted sumset has at most `m` elements lie in at most
`freimanClassCountBound t m` Freiman classes of order `2`. This is the combinatorial assembly of
the three families of representatives, before the estimate of the sum. -/
lemma exists_representsFreimanIsoClasses_card_le_freimanClassCountBound {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m) :
    ∃ representatives : Finset (Finset W),
      RepresentsFreimanIsoClasses 2 {A : Finset W | #A = t ∧ #(restrictedSumset A) ≤ m}
        representatives ∧
      #representatives ≤ freimanClassCountBound t m := by
  choose reps hcard hrep using
    exists_freimanClassRepresentatives_of_card_core_of_card_exception F (W := W) t m
  refine ⟨(range (exceptionCardBound t m + 1)).biUnion fun d ↦
    (Icc 1 (coreCardBound t m)).biUnion (reps d), ?_, ?_⟩
  · rintro A ⟨hA, hm⟩
    obtain ⟨a, -, A₀, hA₀, A₁, hA₁, htranslate, hA₀_nonempty, hA₁_nonempty, hcore, hexception⟩ :=
      exists_nonempty_image_add_subset_restrictedSumset hA ht htm hm
    obtain ⟨Q, hQ, hAQ⟩ := hrep #(A \ A₁) #A₀ A hA hm a A₀ hA₀ A₁ hA₁ htranslate
      hA₁_nonempty rfl rfl
    refine ⟨Q, ?_, hAQ⟩
    simp only [mem_biUnion, mem_range, mem_Icc]
    exact ⟨_, Nat.lt_succ_of_le hexception, _, ⟨hA₀_nonempty.card_pos, hcore⟩, hQ⟩
  · unfold freimanClassCountBound
    refine card_biUnion_le.trans ?_
    gcongr with d
    refine card_biUnion_le.trans ?_
    gcongr with l
    exact hcard d l

end

end CountingSetsWithSmallSumset
