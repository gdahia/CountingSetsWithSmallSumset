/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Counting sets with small sumset

Theorems 7, 8 and 9, Corollary 14 and Propositions 18, 19, 23 and 26 of Green, *Counting sets
with small sumset, and the clique number of random Cayley graphs*, numbered as in
arXiv:math/0304183v2. Statements about all sufficiently large sets are proved above an explicit
threshold, and statements about almost all sets are proved as bounds on the number of exceptional
sets. The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset Real SimpleGraph Filter Topology
open scoped Pointwise

namespace SumOfSetsInSeveralDimensions

/-- The affine dimension of a finite set `S ⊆ ℝ^D`: the dimension of the direction of the affine
span of `S`. -/
noncomputable def finsetAffineDim {D : ℕ} (S : Finset (Fin D → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (S : Set (Fin D → ℝ))).direction

/-- The coordinatewise inclusion of rational vectors into real vectors. -/
def rationalVectorToReal {d : ℕ} (v : Fin d → ℚ) : Fin d → ℝ := fun i ↦ (v i : ℝ)

/-- The set `X` has a Freiman model of dimension `d`: there is a Freiman isomorphism of order `2`
from `X` onto a subset of `ℚ^d` of affine dimension `d`. -/
def freimanModelDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) (d : ℕ) : Prop :=
  ∃ f : G → (Fin d → ℚ),
    IsAddFreimanIso 2 (X : Set G) ((X.image f : Finset (Fin d → ℚ)) : Set (Fin d → ℚ)) f ∧
      finsetAffineDim ((X.image f).image rationalVectorToReal) = d

/-- Freiman's dimension of `X`: the largest `d ≤ |X|` such that `X` has a Freiman model of
dimension `d`. -/
noncomputable def freimanDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) : ℕ := by
  classical
  exact Nat.findGreatest (freimanModelDim X) X.card

end SumOfSetsInSeveralDimensions

namespace CountingSetsWithSmallSumset

open SumOfSetsInSeveralDimensions

section RestrictedSumset

variable {G : Type*} [DecidableEq G]

/-- The restricted sumset, in which the two summands must be distinct. -/
def restrictedSumset [Add G] (A : Finset G) : Finset G :=
  ((A ×ˢ A).filter fun (a, b) ↦ a ≠ b).image fun (a, b) ↦ a + b

end RestrictedSumset

section CayleySumGraph

variable {G : Type*}

/-- The Cayley sum graph of `A`: distinct `x` and `y` are adjacent when `x + y ∈ A`. -/
def cayleySumGraph [Add G] (A : Set G) : SimpleGraph G :=
  fromRel fun x y ↦ x + y ∈ A

end CayleySumGraph

section RestrictedSumsetCardSets

variable (Γ : Type*) [Fintype Γ] [DecidableEq Γ] [Add Γ]

/-- **Definition 3** of Green. `S_k^m(Γ)` is the family of the sets `X ⊆ Γ` with `|X| = k` and
`|X ∔ X| = m`. -/
def restrictedSumsetCardSets (k m : ℕ) : Finset (Finset Γ) :=
  {X | #X = k ∧ #(restrictedSumset X) = m}

end RestrictedSumsetCardSets

section FreimanHomSpace

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
  Module.finrank F (freimanHomSpace F F A) - 1

end FreimanHomSpace

/-- **Theorem 7** of Green. If `log₂ N ≥ 2 ^ 9000`, at most `2 ^ N / N` subsets `A ⊆ ℤ/Nℤ` have a
Cayley sum graph with clique number greater than `160 * log₂ N`. -/
theorem card_cliqueNum_cayleySumGraph_gt_le' {N : ℕ} [NeZero N] (hN : 2 ^ 9000 ≤ logb 2 N) :
    (#{A : Finset (ZMod N) | 160 * logb 2 N < (cayleySumGraph (A : Set (ZMod N))).cliqueNum} :
      ℝ) ≤ 2 ^ N / N :=
  sorry

/-- **Theorem 8** of Green. If `log₂ N ≥ 2 ^ 9000`, some subset `A ⊆ ℤ/Nℤ` has a Cayley sum graph
with clique number and independence number at most `160 * log₂ N`. -/
theorem exists_cliqueNum_le_and_indepNum_le' {N : ℕ} [NeZero N] (hN : 2 ^ 9000 ≤ logb 2 N) :
    ∃ A : Finset (ZMod N), (cayleySumGraph (A : Set (ZMod N))).cliqueNum ≤ 160 * logb 2 N ∧
      (cayleySumGraph (A : Set (ZMod N))).indepNum ≤ 160 * logb 2 N :=
  sorry

/-- **Theorem 9** of Green, as a count. If `n ≥ 2 ^ 9000`, at most
`2 ^ 2 ^ n / n + 2 ^ 2 ^ n / 2 ^ n` subsets `A ⊆ 𝔽₂ⁿ` have a Cayley graph with clique number
outside `[n * log₂ n / 4, 308 * n * log₂ n]`. -/
theorem card_cliqueNum_addCayley_lt_or_gt_le' {n : ℕ} (hn : 2 ^ 9000 ≤ n) :
    (#{A : Finset (Fin n → ZMod 2) |
      (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum < n * logb 2 n / 4 ∨
        308 * n * logb 2 n < (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum} : ℝ) ≤
      2 ^ 2 ^ n / n + 2 ^ 2 ^ n / 2 ^ n :=
  sorry

/-- **Theorem 9** of Green. The proportion of the subsets `A ⊆ 𝔽₂ⁿ` whose Cayley graph has clique
number in `[n * log₂ n / 4, 308 * n * log₂ n]` tends to `1`. -/
theorem tendsto_card_le_cliqueNum_addCayley_le' :
    Tendsto (fun n : ℕ ↦ (#{A : Finset (Fin n → ZMod 2) |
      n * logb 2 n / 4 ≤ (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum ∧
        (addCayley (A : Set (Fin n → ZMod 2))).cliqueNum ≤ 308 * n * logb 2 n} : ℝ) / 2 ^ 2 ^ n)
      atTop (𝓝 1) :=
  sorry

/-- **Corollary 14** of Green. For a nonempty finite subset `A` of a vector space over a field `F`,
`r_F(A)` is the largest `d` such that `A` is Freiman isomorphic of order `2` to a subset of `F^d`
of affine dimension `d`. -/
theorem isGreatest_freimanDimOver' (F : Type*) [Field F] {W : Type*} [AddCommGroup W]
    [Module F W] {A : Finset W} (hA : A.Nonempty) :
    IsGreatest {d | ∃ f : W → (Fin d → F), IsAddFreimanIso 2 (A : Set W) (f '' A) f ∧
      Module.finrank F (vectorSpan F (f '' A)) = d} (freimanDimOver F A) :=
  sorry

/-- **Corollary 14** of Green for a set of integers: `r_ℚ(X) = dim Hom₂(X, ℚ) - 1` is Freiman's
dimension of `X`. -/
theorem freimanDimOver_rat_eq_freimanDim_int' (X : Finset ℤ) :
    freimanDimOver ℚ X = freimanDim X :=
  sorry

/-- **Proposition 18** of Green. Let `W` be a vector space over a field `F`, `t ≥ 2 ^ 9000` and
`m ≤ t ^ (31 / 30)`. There is a family of at most `(e * m / t) ^ t * exp (t ^ (31 / 32))` subsets
of `W` such that every set `A ⊆ W` of `t` elements with `|A ∔ A| ≤ m` is Freiman isomorphic of
order `2` to a member of the family. -/
theorem exists_coversFreimanIsoClasses_card_restrictedSumset_le' (F W : Type*) [Field F]
    [AddCommGroup W] [Module F W] [DecidableEq W] {t m : ℕ} (ht : 2 ^ 9000 ≤ t)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ∃ representatives : Finset (Finset W),
      (∀ A : Finset W, #A = t → #(restrictedSumset A) ≤ m →
        ∃ B ∈ representatives, ∃ f : W → W, IsAddFreimanIso 2 (A : Set W) (B : Set W) f) ∧
      #representatives ≤ (exp 1 * m / t) ^ t * exp (t ^ ((31 : ℝ) / 32)) :=
  sorry

/-- **Proposition 19** of Green. Let `0 < ε ≤ 1 / 2` and let `A` be a finite subset of an abelian
group with `|A| ≥ 16 / ε ^ 2`. Some `B ⊆ A` with `|B| ≤ 3 * log₂ (1 / ε) / ε * √|A|` has
`|B ∔ B| ≥ (1 - ε) * |A|`. -/
theorem exists_subset_card_le_and_le_card_restrictedSumset' {G : Type*} [DecidableEq G]
    [AddCommGroup G] {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) {A : Finset G}
    (hA : 16 / ε ^ 2 ≤ #A) :
    ∃ B ⊆ A, #B ≤ 3 * logb 2 (1 / ε) / ε * √(#A) ∧ (1 - ε) * #A ≤ #(restrictedSumset B) :=
  sorry

/-- **Proposition 23** (i) of Green. If `k ≥ 2 ^ 9000` and `m ≤ k ^ (31 / 30) / 2`, then
`|S_k^m(ℤ/Nℤ)| ≤ N ^ (1 + 4 * m / k) * (2 * e * m / k) ^ k * exp (k ^ (31 / 32))`. -/
theorem card_restrictedSumsetCardSets_zmod_le_of_le_rpow' (N : ℕ) [NeZero N] {k m : ℕ}
    (hk : 2 ^ 9000 ≤ k) (hm : (m : ℝ) ≤ k ^ ((31 : ℝ) / 30) / 2) :
    (#(restrictedSumsetCardSets (ZMod N) k m) : ℝ) ≤
      N ^ (1 + 4 * (m : ℝ) / k) * (2 * exp 1 * m / k) ^ k * exp (k ^ ((31 : ℝ) / 32)) :=
  sorry

/-- **Proposition 23** (ii) of Green. For `k ≥ 1`,
`|S_k^m(ℤ/Nℤ)| ≤ N ^ (1 + 4 * m / k) * k ^ (4 * k)`. -/
theorem card_restrictedSumsetCardSets_zmod_le' (N : ℕ) [NeZero N] {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (#(restrictedSumsetCardSets (ZMod N) k m) : ℝ) ≤ N ^ (1 + 4 * (m : ℝ) / k) * k ^ (4 * k) :=
  sorry

/-- **Proposition 26** (i) of Green. If `k ≥ 2 ^ 9000` and `m ≤ k ^ (31 / 30)`, then
`|S_k^m(𝔽₂ⁿ)| ≤ (2 ^ n) ^ (4 * m * log₂ k / k) * (e * m / k) ^ k * exp (k ^ (31 / 32))`. -/
theorem card_restrictedSumsetCardSets_pi_zmod_two_le_of_le_rpow' (n : ℕ) {k m : ℕ}
    (hk : 2 ^ 9000 ≤ k) (hm : m ≤ (k : ℝ) ^ ((31 : ℝ) / 30)) :
    (#(restrictedSumsetCardSets (Fin n → ZMod 2) k m) : ℝ) ≤
      ((2 : ℝ) ^ n) ^ (4 * m * logb 2 k / k) * (exp 1 * m / k) ^ k *
        exp (k ^ ((31 : ℝ) / 32)) :=
  sorry

/-- **Proposition 26** (ii) of Green. For `k ≥ 2`,
`|S_k^m(𝔽₂ⁿ)| ≤ (2 ^ n) ^ (4 * m * log₂ k / k) * k ^ (4 * k)`. -/
theorem card_restrictedSumsetCardSets_pi_zmod_two_le' (n : ℕ) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (#(restrictedSumsetCardSets (Fin n → ZMod 2) k m) : ℝ) ≤
      ((2 : ℝ) ^ n) ^ (4 * m * logb 2 k / k) * k ^ (4 * k) :=
  sorry

end CountingSetsWithSmallSumset
