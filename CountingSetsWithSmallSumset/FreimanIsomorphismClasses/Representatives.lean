/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom

/-!
# Representatives of the Freiman isomorphism classes of a family of finite sets

Green, *Counting sets with small sumset, and the clique number of random Cayley graphs*, bounds
the number of Freiman isomorphism classes in a family of finite sets. Here such a bound takes the
form of a finite family of representatives such that every member of the family is Freiman
isomorphic to one of them. If the members of a family receive patterns from a finite type, and
members with the same pattern are Freiman isomorphic, then the family is represented by at most as
many of its members as there are patterns. Representatives transfer along an injective additive map.

## Main definitions

* `FreimanIsomorphic n A B`: the finite sets `A` and `B` are Freiman isomorphic of order `n`.
* `RepresentsFreimanIsoClasses n family representatives`: every member of `family` is Freiman
  isomorphic of order `n` to a member of `representatives`.

## Main statements

* `exists_subset_representsFreimanIsoClasses_card_le_of_pattern`: a family whose members with
  equal patterns are Freiman isomorphic is represented by at most as many of its members as there
  are patterns.
* `exists_representsFreimanIsoClasses_card_le_of_image`: representatives of the image of a family
  under an injective additive map give at most as many representatives of the family.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset

variable {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]

/-- The finite sets `A` and `B` are Freiman isomorphic of order `n`. -/
def FreimanIsomorphic (n : ℕ) (A B : Finset G) : Prop :=
  ∃ f : G → G, IsAddFreimanIso n (A : Set G) (B : Set G) f

lemma FreimanIsomorphic.refl (n : ℕ) (A : Finset G) : FreimanIsomorphic n A A :=
  ⟨id, isAddFreimanIso_id⟩

lemma FreimanIsomorphic.symm {n : ℕ} {A B : Finset G} (h : FreimanIsomorphic n A B) :
    FreimanIsomorphic n B A := by
  obtain ⟨f, hf⟩ := h
  exact ⟨_, hf.invFunOn⟩

lemma FreimanIsomorphic.trans {n : ℕ} {A B C : Finset G} (hAB : FreimanIsomorphic n A B)
    (hBC : FreimanIsomorphic n B C) : FreimanIsomorphic n A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf⟩

/-- Every member of `family` is Freiman isomorphic of order `n` to a member of
`representatives`. -/
def RepresentsFreimanIsoClasses (n : ℕ) (family : Set (Finset G))
    (representatives : Finset (Finset G)) : Prop :=
  ∀ A ∈ family, ∃ B ∈ representatives, FreimanIsomorphic n A B

lemma RepresentsFreimanIsoClasses.subset {n : ℕ} {family family' : Set (Finset G)}
    {representatives : Finset (Finset G)} (h : RepresentsFreimanIsoClasses n family representatives)
    (hsub : family' ⊆ family) : RepresentsFreimanIsoClasses n family' representatives :=
  fun A hA ↦ h A (hsub hA)

/-- Let every member of `family` have a pattern in the finite type `C`, and let members with a
common pattern be Freiman isomorphic of order `n`. Then `family` is represented by at most `|C|`
of its members. -/
lemma exists_subset_representsFreimanIsoClasses_card_le_of_pattern {C : Type*} [Fintype C] {n : ℕ}
    {family : Set (Finset G)} (pattern : Finset G → C → Prop)
    (hpattern : ∀ A ∈ family, ∃ c, pattern A c)
    (hiso : ∀ A ∈ family, ∀ B ∈ family, ∀ c, pattern A c → pattern B c → FreimanIsomorphic n A B) :
    ∃ representatives : Finset (Finset G), ↑representatives ⊆ family ∧
      RepresentsFreimanIsoClasses n family representatives ∧ #representatives ≤ Fintype.card C := by
  classical
  choose! pick hpick using fun c (h : ∃ A ∈ family, pattern A c) ↦ h
  refine ⟨(univ.filter fun c ↦ ∃ A ∈ family, pattern A c).image pick, ?_, ?_,
    card_image_le.trans (card_le_univ _)⟩
  · simp only [coe_image, coe_filter, mem_univ, true_and, Set.image_subset_iff]
    intro c hc
    grind
  · intro A hA
    obtain ⟨c, hc⟩ := hpattern A hA
    obtain ⟨hpickfamily, hpickpattern⟩ := hpick c ⟨A, hA, hc⟩
    exact ⟨pick c, mem_image_of_mem _ (by simpa using ⟨A, hA, hc⟩),
      hiso A hA _ hpickfamily c hc hpickpattern⟩

/-- An injective additive map is a Freiman isomorphism of every order from a finite set onto its
image. -/
lemma isAddFreimanIso_image_of_injective [DecidableEq H] (n : ℕ) {φ : G →+ H}
    (hφ : Function.Injective φ) (A : Finset G) :
    IsAddFreimanIso n (A : Set G) (A.image φ : Set H) φ where
  bijOn := by
    rw [coe_image]
    exact hφ.injOn.bijOn_image
  map_sum_eq_map_sum s t _ _ _ _ := by
    rw [← map_multiset_sum, ← map_multiset_sum, hφ.eq_iff]

/-- Let `φ` be a Freiman isomorphism of order `n` from every finite set onto its image. If the
images of the members of `family` are represented by `representatives`, then `family` is
represented by at most as many of its members. -/
lemma exists_representsFreimanIsoClasses_card_le_of_image [DecidableEq H] {n : ℕ} {φ : G → H}
    (hφ : ∀ A : Finset G, IsAddFreimanIso n (A : Set G) (A.image φ : Set H) φ)
    {family : Set (Finset G)} {representatives : Finset (Finset H)}
    (hrep : RepresentsFreimanIsoClasses n (image φ '' family) representatives) :
    ∃ representatives' : Finset (Finset G), ↑representatives' ⊆ family ∧
      RepresentsFreimanIsoClasses n family representatives' ∧
        #representatives' ≤ #representatives := by
  rw [← Fintype.card_coe representatives]
  refine exists_subset_representsFreimanIsoClasses_card_le_of_pattern
    (fun A (B : representatives) ↦ FreimanIsomorphic n (A.image φ) B) ?_ ?_
  · intro A hA
    obtain ⟨B, hB, hAB⟩ := hrep _ (Set.mem_image_of_mem _ hA)
    exact ⟨⟨B, hB⟩, hAB⟩
  · rintro A - A' - B ⟨f, hf⟩ ⟨f', hf'⟩
    exact ⟨_, (hφ A').invFunOn.comp (hf'.invFunOn.comp (hf.comp (hφ A)))⟩

end CountingSetsWithSmallSumset
