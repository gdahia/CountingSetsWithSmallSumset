/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The space of Freiman homomorphisms and Green's Freiman dimension

Let `F` be a field and `A` a finite subset of an abelian group. The maps `φ : A → M` into an
`F`-module `M` such that `φ a + φ b = φ c + φ d` whenever `a + b = c + d` form a subspace
`Hom₂(A, M)` of `A → M`. Green defines the Freiman dimension of `A` over `F` as
`r_F(A) = dim Hom₂(A, F) - 1`. The constant maps lie in `Hom₂(A, F)`, so `r_F(A) + 1` is the
dimension of `Hom₂(A, F)` when `A` is nonempty, and `r_F(A) ≤ |A| - 1`. Composition with a
Freiman isomorphism of order `2` identifies the spaces of homomorphisms of the two sets, so the
Freiman dimension is invariant under such isomorphisms.

## Main definitions

* `freimanHomSpace F M A`: the space `Hom₂(A, M)` of Freiman homomorphisms of order `2` from `A`
  to `M`.
* `freimanDimOver F A`: the Freiman dimension `r_F(A) = dim Hom₂(A, F) - 1`.

## Main statements

* `mem_freimanHomSpace_iff_isAddFreimanHom`: the restriction of `f` to `A` lies in `Hom₂(A, M)`
  if and only if `f` is a Freiman homomorphism of order `2` on `A`.
* `freimanDimOver_add_one`: `r_F(A) + 1 = dim Hom₂(A, F)` for nonempty `A`.
* `freimanDimOver_le_card_sub_one`: `r_F(A) ≤ |A| - 1`.
* `freimanDimOver_eq_of_isAddFreimanIso`: Freiman isomorphic sets have the same Freiman
  dimension.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Module

variable (F : Type*) [Field F] {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
  (M : Type*) [AddCommGroup M] [Module F M]

/-- `Hom₂(A, M)`: the maps `φ : A → M` such that `φ a + φ b = φ c + φ d` whenever
`a + b = c + d`. -/
def freimanHomSpace (A : Finset G) : Submodule F (A → M) where
  carrier := {φ | ∀ a b c d : A, (a : G) + b = c + d → φ a + φ b = φ c + φ d}
  add_mem' := by
    intro φ ψ hφ hψ a b c d h
    simp only [Pi.add_apply]
    rw [add_add_add_comm, hφ a b c d h, hψ a b c d h, add_add_add_comm]
  zero_mem' _ _ _ _ _ := rfl
  smul_mem' := by
    intro r φ hφ a b c d h
    simp only [Pi.smul_apply]
    rw [← smul_add, ← smul_add, hφ a b c d h]

/-- Green's Freiman dimension `r_F(A) = dim Hom₂(A, F) - 1`. -/
noncomputable def freimanDimOver (A : Finset G) : ℕ :=
  finrank F (freimanHomSpace F F A) - 1

variable {M}

variable {F} in
lemma mem_freimanHomSpace {A : Finset G} {φ : A → M} :
    φ ∈ freimanHomSpace F M A ↔ ∀ a b c d : A, (a : G) + b = c + d → φ a + φ b = φ c + φ d :=
  Iff.rfl

variable {F} in
/-- The restriction of `f` to `A` lies in `Hom₂(A, M)` if and only if `f` is a Freiman
homomorphism of order `2` on `A`. -/
lemma mem_freimanHomSpace_iff_isAddFreimanHom {A : Finset G} {f : G → M} :
    (fun a : A ↦ f a) ∈ freimanHomSpace F M A ↔ IsAddFreimanHom 2 (A : Set G) Set.univ f := by
  simp [isAddFreimanHom_two, mem_freimanHomSpace]

lemma mem_freimanHomSpace_of_isAddFreimanHom {A : Finset G} {B : Set M} {f : G → M}
    (hf : IsAddFreimanHom 2 (A : Set G) B f) : (fun a : A ↦ f a) ∈ freimanHomSpace F M A :=
  mem_freimanHomSpace_iff_isAddFreimanHom.2 (hf.superset (Set.subset_univ B))

/-- The constant maps are Freiman homomorphisms. -/
lemma const_mem_freimanHomSpace (A : Finset G) (m : M) :
    (fun _ ↦ m) ∈ freimanHomSpace F M A := by
  simp [mem_freimanHomSpace]

lemma one_mem_freimanHomSpace (A : Finset G) : 1 ∈ freimanHomSpace F F A :=
  const_mem_freimanHomSpace F A 1

variable {F} in
/-- The composition of a Freiman homomorphism with a linear map is a Freiman homomorphism. -/
lemma comp_mem_freimanHomSpace {N : Type*} [AddCommGroup N] [Module F N] {A : Finset G}
    {φ : A → M} (hφ : φ ∈ freimanHomSpace F M A) (L : M →ₗ[F] N) :
    L ∘ φ ∈ freimanHomSpace F N A := by
  intro a b c d h
  simp [← map_add, hφ a b c d h]

variable {F} in
/-- If `ψ : A → F` is a Freiman homomorphism, then so is `x ↦ ψ(x) m` for every `m ∈ M`. -/
lemma smul_const_mem_freimanHomSpace {A : Finset G} {ψ : A → F} (hψ : ψ ∈ freimanHomSpace F F A)
    (m : M) : (fun x ↦ ψ x • m) ∈ freimanHomSpace F M A := by
  intro a b c d h
  simp [← add_smul, hψ a b c d h]

lemma one_le_finrank_freimanHomSpace {A : Finset G} (hA : A.Nonempty) :
    1 ≤ finrank F (freimanHomSpace F F A) := by
  obtain ⟨x, hx⟩ := hA
  rw [Submodule.one_le_finrank_iff, Submodule.ne_bot_iff]
  exact ⟨1, one_mem_freimanHomSpace F A, fun h ↦ by simpa using congrFun h ⟨x, hx⟩⟩

lemma freimanDimOver_add_one {A : Finset G} (hA : A.Nonempty) :
    freimanDimOver F A + 1 = finrank F (freimanHomSpace F F A) :=
  Nat.sub_add_cancel (one_le_finrank_freimanHomSpace F hA)

lemma finrank_freimanHomSpace_le_card (A : Finset G) :
    finrank F (freimanHomSpace F F A) ≤ #A := by
  simpa using (freimanHomSpace F F A).finrank_le

lemma freimanDimOver_le_card_sub_one (A : Finset G) : freimanDimOver F A ≤ #A - 1 :=
  Nat.sub_le_sub_right (finrank_freimanHomSpace_le_card F A) 1

/-- Composition with a Freiman homomorphism from `A` onto `B` embeds `Hom₂(B, F)` into
`Hom₂(A, F)`. -/
lemma finrank_freimanHomSpace_le_of_isAddFreimanHom {A : Finset G} {B : Finset H} {f : G → H}
    (hf : IsAddFreimanHom 2 (A : Set G) B f) (hsurj : Set.SurjOn f A B) :
    finrank F (freimanHomSpace F F B) ≤ finrank F (freimanHomSpace F F A) := by
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (LinearMap.funLeft F F (hf.mapsTo.restrict f A B)).restrict ?_) ?_
  · intro φ hφ a b c d h
    exact hφ _ _ _ _ (hf.add_eq_add a.prop b.prop c.prop d.prop h)
  · intro φ ψ h
    exact Subtype.ext ((hf.mapsTo.restrict_surjective_iff.2 hsurj).injective_comp_right
      (congrArg Subtype.val h))

/-- The Freiman dimension is invariant under Freiman isomorphisms of order `2`. -/
lemma freimanDimOver_eq_of_isAddFreimanIso {A : Finset G} {B : Finset H} {f : G → H}
    (hf : IsAddFreimanIso 2 (A : Set G) B f) : freimanDimOver F A = freimanDimOver F B := by
  rw [freimanDimOver, freimanDimOver, le_antisymm
    (finrank_freimanHomSpace_le_of_isAddFreimanHom F hf.invFunOn.isAddFreimanHom
      hf.invFunOn.bijOn.surjOn)
    (finrank_freimanHomSpace_le_of_isAddFreimanHom F hf.isAddFreimanHom hf.bijOn.surjOn)]

end CountingSetsWithSmallSumset
