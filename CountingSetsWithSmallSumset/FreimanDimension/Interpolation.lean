/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Interpolation points of a space of functions

Let `Φ` be a subspace of dimension `d` of the space of maps from a finite set `ι` to a field `F`.
The evaluations `φ ↦ φ(x)` at the points `x ∈ ι` span the dual of `Φ`, so `d` of them form a basis
of it. At the corresponding points `a₁, …, a_d` every vector of `F^d` is the vector of values of
exactly one `φ ∈ Φ`, and every evaluation is a fixed linear combination of the evaluations at the
`aᵢ`. This is Lemma 12 of Green, *Counting sets with small sumset, and the clique number of random
Cayley graphs*.

## Main statements

* `exists_interpolation_points`: Lemma 12 of Green.
-/

public section

namespace CountingSetsWithSmallSumset

open Module

variable {F : Type*} [Field F] {ι : Type*} [Finite ι]

/-- Some `finrank F Φ` points of `ι` determine every `φ ∈ Φ`, and every vector of values at them
is attained. -/
private lemma exists_bijective_eval (Φ : Submodule F (ι → F)) :
    ∃ a : Fin (finrank F Φ) → ι, Function.Bijective fun φ : Φ ↦ fun i ↦ (φ : ι → F) (a i) := by
  let t : ι → Dual F Φ := fun x ↦ (LinearMap.proj x).comp Φ.subtype
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F t
  have : Fintype κ := have := Finite.of_injective a ha; Fintype.ofFinite κ
  have hzero {φ : Φ} (hφ : ∀ k, (φ : ι → F) (a k) = 0) : φ = 0 := by
    have hle : Submodule.span F (Set.range t) ≤ LinearMap.ker (Dual.eval F Φ φ) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hφ k
    ext x
    simpa [t] using hle (Submodule.subset_span (Set.mem_range_self x))
  have hcard : Fintype.card κ = finrank F Φ := by
    refine le_antisymm ?_ ?_
    · rw [← finrank_span_eq_card hli]
      exact (Submodule.finrank_le _).trans Subspace.dual_finrank_eq.le
    · have := Fintype.ofFinite ι
      rw [← finrank_fintype_fun_eq_card (R := F)]
      refine LinearMap.finrank_le_finrank_of_injective (f := LinearMap.pi fun k ↦ t (a k)) ?_
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro φ hφ
      exact hzero (congrFun hφ)
  let e := Fintype.equivFinOfCardEq hcard
  let E : Φ →ₗ[F] (Fin (finrank F Φ) → F) := LinearMap.pi fun i ↦ t (a (e.symm i))
  have hE : Function.Injective E := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro φ hφ
    exact hzero fun k ↦ by simpa [E, t] using congrFun hφ (e k)
  exact ⟨a ∘ e.symm, hE, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hE⟩

/-- **Lemma 12** of Green. Let `Φ` be a space of dimension `d` of maps from a finite set `ι` to
`F`. There are distinct points `a₁, …, a_d` of `ι` such that every vector `f ∈ F^d` is
`(φ(a₁), …, φ(a_d))` for exactly one `φ ∈ Φ`, and for every `x ∈ ι` there are `λ₁, …, λ_d` with
`φ(x) = λ₁ φ(a₁) + ⋯ + λ_d φ(a_d)` for all `φ ∈ Φ`. If `Φ` contains the constant map `1`, then
`λ₁ + ⋯ + λ_d = 1`. -/
theorem exists_interpolation_points (Φ : Submodule F (ι → F)) {d : ℕ} (hd : finrank F Φ = d) :
    ∃ a : Fin d → ι, Function.Injective a ∧
      Function.Bijective (fun φ : Φ ↦ fun i ↦ (φ : ι → F) (a i)) ∧
      ∀ x, ∃ c : Fin d → F, (∀ φ ∈ Φ, φ x = ∑ i, c i * φ (a i)) ∧ (1 ∈ Φ → ∑ i, c i = 1) := by
  subst hd
  obtain ⟨a, hinj, hsurj⟩ := exists_bijective_eval Φ
  choose ψ hψ using fun i ↦ hsurj (Pi.single i 1)
  have hψa (i j : Fin (finrank F Φ)) : (ψ i : ι → F) (a j) = (Pi.single i 1 : Fin _ → F) j :=
    congrFun (hψ i) j
  have hexp {φ : ι → F} (hφ : φ ∈ Φ) (x : ι) : φ x = ∑ i, (ψ i : ι → F) x * φ (a i) := by
    have h : (⟨φ, hφ⟩ : Φ) = ∑ i, φ (a i) • ψ i := by
      apply hinj
      ext j
      simp [hψa, Pi.single_apply]
    simpa [mul_comm] using congrFun (congrArg Subtype.val h) x
  refine ⟨a, ?_, ⟨hinj, hsurj⟩, ?_⟩
  · intro i j h
    grind [hψa i j]
  · intro x
    refine ⟨fun i ↦ (ψ i : ι → F) x, fun φ hφ ↦ hexp hφ x, ?_⟩
    intro h1
    simpa using (hexp h1 x).symm

end CountingSetsWithSmallSumset
