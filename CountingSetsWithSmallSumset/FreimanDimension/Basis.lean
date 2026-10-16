/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.FreimanDimension.HomSpace
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import CountingSetsWithSmallSumset.FreimanDimension.Interpolation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Freiman bases

Let `A` be a finite nonempty subset of an abelian group and `r = r_F(A)` its Freiman dimension over
a field `F`. Lemma 12 of Green applied to `Hom₂(A, F)` gives points `a₁, …, a_{r+1}` of `A` at
which the Freiman homomorphisms `A → F` can take any values, each exactly once. We call such
points a Freiman basis of `A`. Every `x ∈ A` then has coefficients `λ₁, …, λ_{r+1}` with sum `1`
such that `φ(x) = λ₁ φ(a₁) + ⋯ + λ_{r+1} φ(a_{r+1})` for every Freiman homomorphism `φ` from `A`
into any `F`-module `M`, and the homomorphisms `A → M` can also take any values at the `aᵢ`,
each exactly once. Hence `dim Hom₂(A, M) = (r + 1) dim M`. If the additive relations of `A` are
those of a subset of an `F`-module, then a homomorphism whose values at the `aᵢ` are affinely
independent is a Freiman isomorphism onto its image. This is Lemma 13 of Green, *Counting sets
with small sumset, and the clique number of random Cayley graphs*.

## Main definitions

* `IsFreimanBasis F A a`: the points `a₁, …, a_k` form a Freiman basis of `A` over `F`.

## Main statements

* `exists_isFreimanBasis`: `A` has a Freiman basis of `r_F(A) + 1` points.
* `IsFreimanBasis.bijective`: the homomorphisms `A → M` take any values at a Freiman basis, each
  exactly once.
* `IsFreimanBasis.exists_sum_eq_one`: the value of a homomorphism at `x ∈ A` is a fixed affine
  combination of its values at a Freiman basis.
* `IsFreimanBasis.isAddFreimanIso_of_affineIndependent`: a homomorphism with affinely independent
  values at a Freiman basis is a Freiman isomorphism onto its image.
* `exists_freimanBasis_of_module`: Lemma 13 of Green.
* `finrank_freimanHomSpace`: `dim Hom₂(A, M) = (r_F(A) + 1) dim M`.
* `card_freimanHomSpace`: `|Hom₂(A, M)| = |M| ^ (r_F(A) + 1)`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Module

variable {F : Type*} [Field F] {G : Type*} [AddCommMonoid G] {M : Type*} [AddCommGroup M]
  [Module F M]

variable (F) in
/-- The points `a₁, …, a_k` of `A` form a Freiman basis of `A` over `F`: every vector of `F^k` is
`(φ(a₁), …, φ(a_k))` for exactly one `φ ∈ Hom₂(A, F)`. -/
def IsFreimanBasis (A : Finset G) {k : ℕ} (a : Fin k → A) : Prop :=
  Function.Bijective fun φ : freimanHomSpace F F A ↦ fun i ↦ (φ : A → F) (a i)

variable (F) in
/-- A nonempty set `A` has a Freiman basis of `r_F(A) + 1` points. -/
lemma exists_isFreimanBasis {A : Finset G} (hA : A.Nonempty) :
    ∃ a : Fin (freimanDimOver F A + 1) → A, IsFreimanBasis F A a := by
  obtain ⟨a, -, ha, -⟩ :=
    exists_interpolation_points (freimanHomSpace F F A) (freimanDimOver_add_one F hA).symm
  exact ⟨a, ha⟩

namespace IsFreimanBasis

variable {A : Finset G} {k : ℕ} {a : Fin k → A}

/-- The homomorphism `ψᵢ ∈ Hom₂(A, F)` with `ψᵢ(aⱼ) = δᵢⱼ`. -/
private noncomputable def coord (ha : IsFreimanBasis F A a) (i : Fin k) : freimanHomSpace F F A :=
  Function.surjInv (Function.Bijective.surjective ha) (Pi.single i 1)

private lemma coord_apply (ha : IsFreimanBasis F A a) (i j : Fin k) :
    (ha.coord i : A → F) (a j) = (Pi.single i 1 : Fin k → F) j :=
  congrFun (Function.surjInv_eq (Function.Bijective.surjective ha) _) j

private lemma sum_coord_smul_mem (ha : IsFreimanBasis F A a) (w : Fin k → M) :
    (fun x ↦ ∑ i, (ha.coord i : A → F) x • w i) ∈ freimanHomSpace F M A := by
  rw [← sum_fn]
  exact Submodule.sum_mem _ fun i _ ↦ smul_const_mem_freimanHomSpace (ha.coord i).prop (w i)

private lemma sum_coord_smul_apply (ha : IsFreimanBasis F A a) (w : Fin k → M) (j : Fin k) :
    ∑ i, (ha.coord i : A → F) (a j) • w i = w j := by
  simp [coord_apply, Pi.single_apply]

/-- A homomorphism `A → M` is determined by its values at a Freiman basis. -/
lemma injective (ha : IsFreimanBasis F A a) (M : Type*) [AddCommGroup M] [Module F M] :
    Function.Injective fun φ : freimanHomSpace F M A ↦ fun i ↦ (φ : A → M) (a i) := by
  intro φ φ' h
  ext x
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff F]
  intro ℓ
  have hmem := comp_mem_freimanHomSpace (sub_mem φ.prop φ'.prop) ℓ
  have hzero : (⟨_, hmem⟩ : freimanHomSpace F F A) = 0 := by
    apply Function.Bijective.injective ha
    ext i
    simp [(congrFun h i : (φ : A → M) (a i) = (φ' : A → M) (a i))]
  simpa using congrFun (congrArg Subtype.val hzero) x

private lemma eq_sum_coord (ha : IsFreimanBasis F A a) {φ : A → M}
    (hφ : φ ∈ freimanHomSpace F M A) (x : A) : φ x = ∑ i, (ha.coord i : A → F) x • φ (a i) := by
  have h : (⟨φ, hφ⟩ : freimanHomSpace F M A) = ⟨_, ha.sum_coord_smul_mem fun i ↦ φ (a i)⟩ :=
    ha.injective M (funext fun j ↦ (ha.sum_coord_smul_apply (fun i ↦ φ (a i)) j).symm)
  exact congrFun (congrArg Subtype.val h) x

/-- **Lemma 13 (i)** of Green. For every `F`-module `M`, every vector of `M^k` is
`(φ(a₁), …, φ(a_k))` for exactly one `φ ∈ Hom₂(A, M)`. -/
theorem bijective (ha : IsFreimanBasis F A a) (M : Type*) [AddCommGroup M] [Module F M] :
    Function.Bijective fun φ : freimanHomSpace F M A ↦ fun i ↦ (φ : A → M) (a i) := by
  refine ⟨ha.injective M, ?_⟩
  intro w
  exact ⟨⟨_, ha.sum_coord_smul_mem w⟩, funext (ha.sum_coord_smul_apply w)⟩

private lemma sum_coord (ha : IsFreimanBasis F A a) (x : A) :
    ∑ i, (ha.coord i : A → F) x = 1 := by
  simpa using (ha.eq_sum_coord (one_mem_freimanHomSpace F A) x).symm

/-- **Lemma 13 (ii)** of Green. For every `x ∈ A` there are `λ₁, …, λ_k` with sum `1` such that
`φ(x) = λ₁ φ(a₁) + ⋯ + λ_k φ(a_k)` for every Freiman homomorphism `φ` from `A` to any `F`-module.
-/
theorem exists_sum_eq_one (ha : IsFreimanBasis F A a) (x : A) :
    ∃ c : Fin k → F, ∑ i, c i = 1 ∧ ∀ (M : Type*) [AddCommGroup M] [Module F M],
      ∀ φ ∈ freimanHomSpace F M A, φ x = ∑ i, c i • φ (a i) := by
  refine ⟨fun i ↦ (ha.coord i : A → F) x, ha.sum_coord x, ?_⟩
  intro M _ _ φ hφ
  exact ha.eq_sum_coord hφ x

/-- The coefficients of `x + y - z - w` in terms of a Freiman basis. -/
private noncomputable def relationCoeff (ha : IsFreimanBasis F A a) (x y z w : A) (i : Fin k) :
    F :=
  (ha.coord i : A → F) x + (ha.coord i : A → F) y - (ha.coord i : A → F) z -
    (ha.coord i : A → F) w

private lemma sum_relationCoeff (ha : IsFreimanBasis F A a) (x y z w : A) :
    ∑ i, ha.relationCoeff x y z w i = 0 := by
  simp [relationCoeff, sum_add_distrib, sum_sub_distrib, sum_coord]

private lemma add_sub_sub_eq_sum (ha : IsFreimanBasis F A a) {φ : A → M}
    (hφ : φ ∈ freimanHomSpace F M A) (x y z w : A) :
    φ x + φ y - φ z - φ w = ∑ i, ha.relationCoeff x y z w i • φ (a i) := by
  simp only [relationCoeff, add_smul, sub_smul, sum_add_distrib, sum_sub_distrib,
    ← ha.eq_sum_coord hφ]

/-- Let `g` be a Freiman isomorphism from `A` into an `F`-module `V`. If `φ ∈ Hom₂(A, M)` has
affinely independent values at a Freiman basis, then `φ` reflects the additive relations of `A`.
-/
lemma add_eq_add_of_affineIndependent (ha : IsFreimanBasis F A a) {V : Type*} [AddCommGroup V]
    [Module F V] {g : G → V} (hg : IsAddFreimanIso 2 (A : Set G) (g '' A) g) {φ : A → M}
    (hφ : φ ∈ freimanHomSpace F M A) (hind : AffineIndependent F fun i ↦ φ (a i)) {x y z w : A}
    (h : φ x + φ y = φ z + φ w) : (x : G) + y = z + w := by
  have hu : ∀ i, ha.relationCoeff x y z w i = 0 := by
    rw [affineIndependent_iff_of_fintype] at hind
    refine hind _ (ha.sum_relationCoeff x y z w) ?_
    rw [weightedVSub_eq_linear_combination _ (ha.sum_relationCoeff x y z w),
      ← ha.add_sub_sub_eq_sum hφ, h]
    simp
  rw [← hg.add_eq_add x.prop y.prop z.prop w.prop, ← sub_eq_zero, sub_add_eq_sub_sub,
    ha.add_sub_sub_eq_sum (mem_freimanHomSpace_of_isAddFreimanHom F hg.isAddFreimanHom)]
  simp [hu]

/-- **Lemma 13 (i)** of Green, second part. Let `g` be a Freiman isomorphism from `A` into an
`F`-module. If `f` is a Freiman homomorphism on `A` whose values at a Freiman basis are affinely
independent, then `f` is a Freiman isomorphism from `A` onto its image. -/
theorem isAddFreimanIso_of_affineIndependent (ha : IsFreimanBasis F A a) {V : Type*}
    [AddCommGroup V] [Module F V] {g : G → V} (hg : IsAddFreimanIso 2 (A : Set G) (g '' A) g)
    {f : G → M} (hf : IsAddFreimanHom 2 (A : Set G) Set.univ f)
    (hind : AffineIndependent F fun i ↦ f (a i)) :
    IsAddFreimanIso 2 (A : Set G) (f '' A) f := by
  have hrel {x y z w : G} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A)
      (h : f x + f y = f z + f w) : x + y = z + w :=
    ha.add_eq_add_of_affineIndependent hg (φ := fun x : A ↦ f x)
      (mem_freimanHomSpace_of_isAddFreimanHom F hf) hind
      (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (z := ⟨z, hz⟩) (w := ⟨w, hw⟩) h
  refine isAddFreimanIso_two.2 ⟨Set.InjOn.bijOn_image ?_, ?_⟩
  · intro x hx y hy hxy
    apply hg.bijOn.injOn hx hy
    simpa using (hg.add_eq_add hx hy hy hy).2 (hrel hx hy hy hy (by rw [hxy]))
  · intro x hx y hy z hz w hw
    exact ⟨hrel hx hy hz hw, hf.add_eq_add hx hy hz hw⟩

end IsFreimanBasis

variable (F) in
/-- **Lemma 13** of Green. Let `A` be a finite nonempty subset of an `F`-vector space `W`, and
`r = r_F(A)`. There are points `a₁, …, a_{r+1}` of `A` such that:
(i) for every `F`-module `M` and all `w₁, …, w_{r+1} ∈ M` there is a unique `φ ∈ Hom₂(A, M)` with
`φ(aᵢ) = wᵢ`, and if the `wᵢ` are linearly independent then `φ` reflects the additive relations
of `A`;
(ii) for every `x ∈ A` there are `λ₁, …, λ_{r+1}` with sum `1` such that
`φ(x) = λ₁ φ(a₁) + ⋯ + λ_{r+1} φ(a_{r+1})` for every Freiman homomorphism `φ` from `A` to any
`F`-module. -/
theorem exists_freimanBasis_of_module {W : Type*} [AddCommGroup W] [Module F W] {A : Finset W}
    (hA : A.Nonempty) :
    ∃ a : Fin (freimanDimOver F A + 1) → A,
      (∀ (M : Type*) [AddCommGroup M] [Module F M],
        Function.Bijective (fun φ : freimanHomSpace F M A ↦ fun i ↦ (φ : A → M) (a i)) ∧
        ∀ φ ∈ freimanHomSpace F M A, LinearIndependent F (fun i ↦ φ (a i)) →
          ∀ x y z w : A, φ x + φ y = φ z + φ w → (x : W) + y = z + w) ∧
      ∀ x : A, ∃ c : Fin (freimanDimOver F A + 1) → F, ∑ i, c i = 1 ∧
        ∀ (M : Type*) [AddCommGroup M] [Module F M], ∀ φ ∈ freimanHomSpace F M A,
          φ x = ∑ i, c i • φ (a i) := by
  obtain ⟨a, ha⟩ := exists_isFreimanBasis F hA
  refine ⟨a, ?_, ha.exists_sum_eq_one⟩
  intro M _ _
  refine ⟨ha.bijective M, ?_⟩
  intro φ hφ hind x y z w h
  exact ha.add_eq_add_of_affineIndependent (g := id) (by simpa using isAddFreimanIso_id) hφ
    hind.affineIndependent h

variable (F) in
/-- `dim Hom₂(A, M) = (r_F(A) + 1) dim M` for a nonempty set `A` and a finite-dimensional `M`. -/
lemma finrank_freimanHomSpace (M : Type*) [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {A : Finset G} (hA : A.Nonempty) :
    finrank F (freimanHomSpace F M A) = (freimanDimOver F A + 1) * finrank F M := by
  obtain ⟨a, ha⟩ := exists_isFreimanBasis F hA
  let E : freimanHomSpace F M A →ₗ[F] (Fin (freimanDimOver F A + 1) → M) :=
    LinearMap.pi fun i ↦ (LinearMap.proj (a i)).comp (freimanHomSpace F M A).subtype
  rw [(LinearEquiv.ofBijective E (ha.bijective M)).finrank_eq, finrank_pi_fintype]
  simp

variable (F) in
/-- `|Hom₂(A, M)| = |M| ^ (r_F(A) + 1)` for a nonempty set `A`. -/
lemma card_freimanHomSpace (M : Type*) [AddCommGroup M] [Module F M] {A : Finset G}
    (hA : A.Nonempty) :
    Nat.card (freimanHomSpace F M A) = Nat.card M ^ (freimanDimOver F A + 1) := by
  obtain ⟨a, ha⟩ := exists_isFreimanBasis F hA
  rw [Nat.card_congr (Equiv.ofBijective _ (ha.bijective M)), Nat.card_fun]
  simp

end CountingSetsWithSmallSumset
