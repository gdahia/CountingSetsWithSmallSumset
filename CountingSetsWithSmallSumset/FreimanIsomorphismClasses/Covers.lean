/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom

/-!
# Covers of a family of finite sets by Freiman isomorphism classes

Green, *Counting sets with small sumset, and the clique number of random Cayley graphs*, bounds
the number of Freiman isomorphism classes in a family of finite sets. Here such a bound takes the
form of a finite family of representatives such that every member of the family is Freiman
isomorphic to one of them. If the members of a family receive codes from a finite type, and
members with the same code are Freiman isomorphic, then the family is covered by at most as many
of its members as there are codes. Covers transfer along an injective additive map.

## Main definitions

* `FreimanIsomorphic n A B`: the finite sets `A` and `B` are Freiman isomorphic of order `n`.
* `CoversFreimanIsoClasses n family representatives`: every member of `family` is Freiman
  isomorphic of order `n` to a member of `representatives`.

## Main statements

* `exists_subset_coversFreimanIsoClasses_card_le_of_code`: a family whose members with equal codes
  are Freiman isomorphic is covered by at most as many of its members as there are codes.
* `exists_coversFreimanIsoClasses_card_le_of_image`: a cover of the image of a family under an
  injective additive map gives a cover of the family of at most the same size.
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
def CoversFreimanIsoClasses (n : ℕ) (family : Set (Finset G))
    (representatives : Finset (Finset G)) : Prop :=
  ∀ A ∈ family, ∃ B ∈ representatives, FreimanIsomorphic n A B

lemma CoversFreimanIsoClasses.subset {n : ℕ} {family family' : Set (Finset G)}
    {representatives : Finset (Finset G)} (h : CoversFreimanIsoClasses n family representatives)
    (hsub : family' ⊆ family) : CoversFreimanIsoClasses n family' representatives :=
  fun A hA ↦ h A (hsub hA)

/-- Let every member of `family` have a code in the finite type `C`, and let members with a common
code be Freiman isomorphic of order `n`. Then `family` is covered by at most `|C|` of its
members. -/
lemma exists_subset_coversFreimanIsoClasses_card_le_of_code {C : Type*} [Fintype C] {n : ℕ}
    {family : Set (Finset G)} (code : Finset G → C → Prop)
    (hcode : ∀ A ∈ family, ∃ c, code A c)
    (hiso : ∀ A ∈ family, ∀ B ∈ family, ∀ c, code A c → code B c → FreimanIsomorphic n A B) :
    ∃ representatives : Finset (Finset G), ↑representatives ⊆ family ∧
      CoversFreimanIsoClasses n family representatives ∧ #representatives ≤ Fintype.card C := by
  classical
  choose! pick hpick using fun c (h : ∃ A ∈ family, code A c) ↦ h
  refine ⟨(univ.filter fun c ↦ ∃ A ∈ family, code A c).image pick, ?_, ?_,
    card_image_le.trans (card_le_univ _)⟩
  · intro B hB
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hB
    obtain ⟨-, hc⟩ := mem_filter.mp hc
    obtain ⟨hpickfamily, -⟩ := hpick c hc
    exact hpickfamily
  · intro A hA
    obtain ⟨c, hc⟩ := hcode A hA
    obtain ⟨hpickfamily, hpickcode⟩ := hpick c ⟨A, hA, hc⟩
    exact ⟨pick c, mem_image_of_mem _ (by simpa using ⟨A, hA, hc⟩),
      hiso A hA _ hpickfamily c hc hpickcode⟩

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

/-- Let `φ` be a Freiman isomorphism of order `n` from every finite set onto its image. A cover of
the images of the members of `family` gives a cover of `family` by at most as many of its
members. -/
lemma exists_coversFreimanIsoClasses_card_le_of_image [DecidableEq H] {n : ℕ} {φ : G → H}
    (hφ : ∀ A : Finset G, IsAddFreimanIso n (A : Set G) (A.image φ : Set H) φ)
    {family : Set (Finset G)} {representatives : Finset (Finset H)}
    (hcover : CoversFreimanIsoClasses n (image φ '' family) representatives) :
    ∃ representatives' : Finset (Finset G), ↑representatives' ⊆ family ∧
      CoversFreimanIsoClasses n family representatives' ∧
        #representatives' ≤ #representatives := by
  rw [← Fintype.card_coe representatives]
  refine exists_subset_coversFreimanIsoClasses_card_le_of_code
    (fun A (B : representatives) ↦ FreimanIsomorphic n (A.image φ) B) ?_ ?_
  · intro A hA
    obtain ⟨B, hB, hAB⟩ := hcover _ (Set.mem_image_of_mem _ hA)
    exact ⟨⟨B, hB⟩, hAB⟩
  · rintro A - A' - B ⟨f, hf⟩ ⟨f', hf'⟩
    exact ⟨_, (hφ A').invFunOn.comp (hf'.invFunOn.comp (hf.comp (hφ A)))⟩

end CountingSetsWithSmallSumset
