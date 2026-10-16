/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Covers
public import CountingSetsWithSmallSumset.RestrictedSumset
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.ExtensionCodes

/-!
# The classes of extensions and of remainders

This file contains Lemmas 16 and 17 of Green, *Counting sets with small sumset, and the clique
number of random Cayley graphs*, in the form of covers by Freiman isomorphism classes, for finite
subsets of a commutative monoid with cancellation.

Lemma 16 bounds the number of classes of order `2` of the sets obtained by adding `d` elements to
a set in a fixed class of order `4`, through extension codes. Lemma 17 states that a subset of the
restricted sumset of a set `C` is Freiman isomorphic of order `4` to a subset of the restricted
sumset of any set that is Freiman isomorphic to `C` of order `8`. The paper uses the orders `6`
and `3` and the bound `l ^ (3 * t ^ 4)` in Lemma 16.

## Main definitions

* `extensionsOfFreimanClass base d`: the sets obtained by adding `d` elements to a set in the
  class of order `4` of `base`.
* `remaindersFromCoreClass core u`: the sets of `u` elements of the restricted sumset of a set in
  the class of order `8` of `core`.

## Main statements

* `exists_coversFreimanIsoClasses_extensionsOfFreimanClass_card_le`: Lemma 16 of Green, at most
  `(1 + |base| ^ 4) ^ ((d + 1) ^ 4)` classes of order `2`.
* `exists_subset_restrictedSumset_freimanIsomorphic`: Lemma 17 of Green.
* `exists_coversFreimanIsoClasses_remaindersFromCoreClass_card_le`: the remainders lie in at most
  `(|core ∔ core| choose u)` classes of order `4`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable {G : Type*} [AddCancelCommMonoid G]

/-! ### Extensions of a class of order `4` -/

/-- Sets obtained by adjoining `d` elements to some member of the class of order `4` of
`base`. -/
def extensionsOfFreimanClass (base : Finset G) (d : ℕ) : Set (Finset G) :=
  {A | ∃ B : Finset G, B ⊆ A ∧ #B = #base ∧ #A = #B + d ∧ FreimanIsomorphic 4 B base}

private lemma range_append {α : Type*} {l d : ℕ} (u : Fin l → α) (v : Fin d → α) :
    Set.range (Fin.append u v) = Set.range u ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases <;> simp
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd d i, Fin.append_left u v i⟩
    · exact ⟨Fin.natAdd l i, Fin.append_right u v i⟩

omit [AddCancelCommMonoid G] in
private lemma extensionBaseTuple_append {l d : ℕ} (u : Fin l → G) (v : Fin d → G) :
    extensionBaseTuple (Fin.append u v) = u := by
  funext i
  simp [extensionBaseTuple]

/-- A member of `extensionsOfFreimanClass base d` has an enumeration whose first `|base|` entries
satisfy the same relations with four terms on each side as a fixed enumeration of `base`. -/
private lemma exists_extensionLabeling {base : Finset G} {b₀ : Fin #base → G}
    (hb₀ : Function.Injective b₀) (hb₀r : Set.range b₀ = base) {d : ℕ} {A : Finset G}
    (hA : A ∈ extensionsOfFreimanClass base d) :
    ∃ a : Fin (#base + d) → G, Function.Injective a ∧ Set.range a = A ∧
      ∀ p : FreimanRelationIndex 4 #base,
        freimanRelationHolds (extensionBaseTuple a) p ↔ freimanRelationHolds b₀ p := by
  classical
  obtain ⟨B, hBA, -, hAB, f, hf⟩ := hA
  have hmem (i : Fin #base) : b₀ i ∈ (base : Set G) := hb₀r ▸ Set.mem_range_self i
  obtain ⟨z, hz, hzr⟩ := exists_injective_range_eq
    (by grind [card_sdiff_add_card_eq_card hBA] : #(A \ B) = d)
  refine ⟨Fin.append (Function.invFunOn f B ∘ b₀) z, Fin.append_injective_iff.mpr ⟨?_, hz, ?_⟩,
    ?_, ?_⟩
  · intro i j hij
    exact hb₀ (hf.invFunOn.bijOn.injOn (hmem i) (hmem j) hij)
  · intro i j hij
    obtain ⟨-, hzB⟩ :=
      mem_sdiff.mp (hzr ▸ Set.mem_range_self j : z j ∈ ((A \ B : Finset G) : Set G))
    exact hzB (hij ▸ hf.invFunOn.bijOn.mapsTo (hmem i))
  · rw [range_append, Set.range_comp, hb₀r, hf.invFunOn.bijOn.image_eq, hzr, ← coe_union,
      union_sdiff_of_subset hBA]
  · intro p
    rw [extensionBaseTuple_append]
    exact freimanRelationHolds_comp_iff hf.invFunOn hmem p

/-- **Lemma 16** of Green, in the form of a cover. The sets obtained by adjoining `d` elements to
a member of the class of order `4` of `base` lie in at most `(1 + |base| ^ 4) ^ ((d + 1) ^ 4)`
classes of order `2`. -/
theorem exists_coversFreimanIsoClasses_extensionsOfFreimanClass_card_le {base : Finset G}
    (hbase : base.Nonempty) (d : ℕ) :
    ∃ representatives : Finset (Finset G),
      ↑representatives ⊆ extensionsOfFreimanClass base d ∧
      CoversFreimanIsoClasses 2 (extensionsOfFreimanClass base d) representatives ∧
      #representatives ≤ (1 + #base ^ 4) ^ ((d + 1) ^ 4) := by
  obtain ⟨b₀, hb₀, hb₀r⟩ := exists_injective_range_eq (rfl : #base = #base)
  rw [← card_extensionCodeType]
  refine exists_subset_coversFreimanIsoClasses_card_le_of_code
    (fun A code ↦ ∃ a : Fin (#base + d) → G, Function.Injective a ∧ Set.range a = A ∧
      (∀ p : FreimanRelationIndex 4 #base,
        freimanRelationHolds (extensionBaseTuple a) p ↔ freimanRelationHolds b₀ p) ∧
      extensionCode a = code) ?_ ?_
  · intro A hA
    obtain ⟨a, ha, hrange, hrelations⟩ := exists_extensionLabeling hb₀ hb₀r hA
    exact ⟨_, a, ha, hrange, hrelations, rfl⟩
  · rintro A - B - code ⟨a, ha, hA, hab₀, rfl⟩ ⟨b, hb, hB, hbb₀, hcode⟩
    exact freimanIsomorphic_of_freimanRelationHolds_iff ha hA hb hB
      (freimanRelationHolds_iff_of_extensionCode_eq ⟨0, hbase.card_pos⟩ hcode.symm
        fun p ↦ (hab₀ p).trans (hbb₀ p).symm)

/-! ### Remainders in the restricted sumset of a class of order `8` -/

variable [DecidableEq G]

/-- **Lemma 17** of Green, with the orders `8` and `4`. If `C` is Freiman isomorphic of order `8`
to `core`, then every subset `B` of the restricted sumset of `C` is Freiman isomorphic of order `4`
to a subset of the restricted sumset of `core`. -/
theorem exists_subset_restrictedSumset_freimanIsomorphic {C core B : Finset G}
    (hC : FreimanIsomorphic 8 C core) (hB : B ⊆ restrictedSumset C) :
    ∃ D ⊆ restrictedSumset core, #D = #B ∧ FreimanIsomorphic 4 B D := by
  obtain ⟨f, hf⟩ := hC
  obtain ⟨b, hb, hbr⟩ := exists_injective_range_eq (rfl : #B = #B)
  choose c₁ hc₁ c₂ hc₂ hne hsum using fun i ↦
    mem_restrictedSumset.mp (hB (mem_coe.mp (hbr ▸ Set.mem_range_self i)))
  have hrelations (p : FreimanRelationIndex 4 #B) :
      freimanRelationHolds b p ↔ freimanRelationHolds (fun i ↦ f (c₁ i) + f (c₂ i)) p := by
    rw [freimanRelationHolds_pairSum_iff (s := 4) hf hc₁ hc₂, (funext hsum : c₁ + c₂ = b)]
  have hinjective := injective_of_freimanRelationHolds_iff hb hrelations
  refine ⟨univ.image fun i ↦ f (c₁ i) + f (c₂ i), ?_,
    by simp [card_image_of_injective _ hinjective],
    freimanIsomorphic_of_freimanRelationHolds_iff hb hbr hinjective (by simp) hrelations⟩
  rw [image_subset_iff]
  intro i _
  exact mem_restrictedSumset.mpr ⟨f (c₁ i), hf.bijOn.mapsTo (hc₁ i), f (c₂ i),
    hf.bijOn.mapsTo (hc₂ i), hf.bijOn.injOn.ne (hc₁ i) (hc₂ i) (hne i), rfl⟩

/-- Sets of size `u` contained in the restricted sumset of some member of the class of order `8`
of `core`. -/
def remaindersFromCoreClass (core : Finset G) (u : ℕ) : Set (Finset G) :=
  {B | #B = u ∧ ∃ C : Finset G, FreimanIsomorphic 8 C core ∧ B ⊆ restrictedSumset C}

/-- After fixing the class of order `8` of the core, the possible remainders lie in at most
`(|core ∔ core| choose u)` classes of order `4`. -/
lemma exists_coversFreimanIsoClasses_remaindersFromCoreClass_card_le (core : Finset G) (u : ℕ) :
    ∃ representatives : Finset (Finset G),
      CoversFreimanIsoClasses 4 (remaindersFromCoreClass core u) representatives ∧
      (∀ R ∈ representatives, #R = u) ∧ #representatives ≤ (#(restrictedSumset core)).choose u := by
  refine ⟨(restrictedSumset core).powersetCard u, ?_, ?_, (card_powersetCard _ _).le⟩
  · rintro B ⟨rfl, C, hC, hBC⟩
    obtain ⟨D, hD, hDB, hBD⟩ := exists_subset_restrictedSumset_freimanIsomorphic hC hBC
    exact ⟨D, mem_powersetCard.mpr ⟨hD, hDB⟩, hBD⟩
  · intro R hR
    obtain ⟨-, hR⟩ := mem_powersetCard.mp hR
    exact hR

end CountingSetsWithSmallSumset
