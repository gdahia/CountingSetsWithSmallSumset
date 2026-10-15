/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Counting sets with small sumset: statements

Three bounds for finite sets of natural numbers, from Sections 3 and 4 of Green, *Counting sets
with small sumset, and the clique number of random Cayley graphs*, arXiv:math/0304183v2, and from
the proof of Proposition 23 of that paper. The statements of the paper are numbered as in that
version, where theorems, propositions, lemmas and corollaries share one counter. This module
imports Mathlib alone; the proofs are supplied by the companion `Solution` module.

* `ncard_setOf_card_eq_freimanDim_le_le`: there are at most `n ^ (r + 1) * t ^ (4 * t)` sets
  `X ⊆ {1, …, n}` with `t` elements and Freiman dimension at most `r`.
* `exists_forall_exists_isAddFreimanIso_card_le`: Proposition 18 for sets of natural numbers,
  with `t ≥ 2 ^ 9000` in place of `t` sufficiently large.
* `ncard_setOf_card_eq_freimanDim_le_card_add_le_le`: for `t ≥ 2 ^ 9000` and
  `s ≤ t ^ (31 / 30) / 2`, there are at most
  `n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ {1, …, n}` with `t`
  elements, Freiman dimension at most `r` and `|X + X| ≤ s`.

The Freiman dimension `freimanDim X` of a finite subset `X` of an abelian group is the largest
`d ≤ |X|` such that `X` is Freiman isomorphic of order `2` to a subset of `ℚ^d` that is not
contained in a proper affine subspace: the affine span over `ℝ` of the subset has dimension `d`
(`finsetAffineDim`). The paper defines the Freiman dimension of a set `X` of integers as
`dim Hom₂(X, ℚ) - 1`, where `Hom₂(X, ℚ)` is the space of the Freiman homomorphisms of order `2`
from `X` to `ℚ`. Its Corollary 14 states that this is the largest `d` as above. That corollary is
not formalized. The restricted sumset of `A` is the set of the sums `a + b` with `a, b ∈ A` and
`a ≠ b`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace SumOfSetsInSeveralDimensions

/-! ### The Freiman dimension -/

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

/-- The Freiman dimension of `X`: the largest `d ≤ |X|` such that `X` has a Freiman model of
dimension `d`. -/
noncomputable def freimanDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) : ℕ := by
  classical
  exact Nat.findGreatest (freimanModelDim X) X.card

end SumOfSetsInSeveralDimensions

namespace CountingSetsWithSmallSumset

open SumOfSetsInSeveralDimensions

/-! ### Statements -/

/-- There are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ {1, …, n}` with `t` elements and
Freiman dimension at most `r`. The paper does not state this. It follows from Lemma 11 with
`s = 2`, which bounds the number of Freiman isomorphism classes of order `2` of sets of `t`
elements by `t ^ (4 * t)`, and from Lemma 13 (i), by which a class of Freiman dimension `r` has
at most `n ^ (r + 1)` members in `{1, …, n}`. The proof of the second bound of Proposition 23
combines the two lemmas in this way. -/
theorem ncard_setOf_card_eq_freimanDim_le_le (n r t : ℕ) (ht : 0 < t) :
    {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r}.ncard ≤
      n ^ (r + 1) * t ^ (4 * t) :=
  sorry

/-- **Proposition 18** of Green, for sets of natural numbers. Let `t ≥ 2 ^ 9000` and
`m ≤ t ^ (31 / 30)`. There is a family of at most `(e * m / t) ^ t * exp (t ^ (31 / 32))` finite
sets such that every set `A` of `t` natural numbers whose restricted sumset has at most `m`
elements is Freiman isomorphic of order `2` to a member of the family. The paper takes `t`
sufficiently large and subsets of `F^t` for a field `F`. -/
theorem exists_forall_exists_isAddFreimanIso_card_le {t m : ℕ} (ht : 2 ^ 9000 ≤ t)
    (hm : m ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ∃ representatives : Finset (Finset ℕ),
      (∀ A : Finset ℕ, #A = t →
        #(((A ×ˢ A).filter fun (a, b) ↦ a ≠ b).image fun (a, b) ↦ a + b) ≤ m →
          ∃ B ∈ representatives, ∃ f : ℕ → ℕ, IsAddFreimanIso 2 (A : Set ℕ) (B : Set ℕ) f) ∧
      #representatives ≤ (Real.exp 1 * m / t) ^ t * Real.exp (t ^ ((31 : ℝ) / 32)) :=
  sorry

/-- Let `t ≥ 2 ^ 9000` and `s ≤ t ^ (31 / 30) / 2`. There are at most
`n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ {1, …, n}` with `t` elements,
Freiman dimension at most `r` and `|X + X| ≤ s`. The paper does not state this. The first bound
of Proposition 23 of Green is the same expression with `1 + 4 * m / t` in place of `r + 1` and
`m` in place of `s`, for the number of subsets of `ℤ/Nℤ` with `t` elements whose restricted
sumset has `m` elements. Its proof counts the subsets of `{1, …, N}` with `t` elements whose
restricted sumset has at most `2 * m` elements. Here the Freiman dimension is a parameter and
the bound `s` is on the sumset `X + X`, which contains the restricted sumset. -/
theorem ncard_setOf_card_eq_freimanDim_le_card_add_le_le (n r s t : ℕ) (ht : 2 ^ 9000 ≤ t)
    (hs : s ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2) :
    {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r ∧ #(X + X) ≤ s}.ncard ≤
      n ^ (r + 1) * (2 * Real.exp 1 * s / t) ^ t * Real.exp (t ^ ((31 : ℝ) / 32)) :=
  sorry

end CountingSetsWithSmallSumset
