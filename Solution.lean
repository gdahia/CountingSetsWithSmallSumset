/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.FreimanDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ClassCountBounds

/-!
# Counting sets with small sumset: proofs

Proofs of the statements of `Challenge.lean`. The definitions `finsetAffineDim`,
`rationalVectorToReal`, `freimanModelDim` and `freimanDim` are those of the package
SumOfSetsInSeveralDimensions. The three statements are `card_boundedFreimanDimSets`,
`exists_smallRestrictedSumsetFreimanClassCover` and
`smallSumsetFreimanDimSets_ncard_le_of_class_cover` of the library, with the definitions
`boundedFreimanDimSets`, `smallSumsetFreimanDimSets`, `smallRestrictedSumsetSets`,
`restrictedSumset`, `CoversFreimanClasses`, `FreimanEquivalent` and
`smallSumsetClassCountThreshold` unfolded.
-/

public section

open Finset
open scoped Pointwise

namespace CountingSetsWithSmallSumset

open SumOfSetsInSeveralDimensions

/-- There are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ {1, …, n}` with `t` elements and
Freiman dimension at most `r`. The paper does not state this. It follows from Lemma 11 with
`s = 2`, which bounds the number of Freiman isomorphism classes of order `2` of sets of `t`
elements by `t ^ (4 * t)`, and from Lemma 13 (i), by which a class of Freiman dimension `r` has
at most `n ^ (r + 1)` members in `{1, …, n}`. The proof of the second bound of Proposition 23
combines the two lemmas in this way. -/
theorem ncard_setOf_card_eq_freimanDim_le_le (n r t : ℕ) (ht : 0 < t) :
    {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r}.ncard ≤
      n ^ (r + 1) * t ^ (4 * t) :=
  mod_cast card_boundedFreimanDimSets n r t ht

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
      #representatives ≤ (Real.exp 1 * m / t) ^ t * Real.exp (t ^ ((31 : ℝ) / 32)) := by
  rw [← smallSumsetClassCountThreshold_def] at ht
  obtain ⟨representatives, hcover, hcard⟩ := exists_smallRestrictedSumsetFreimanClassCover ht hm
  exact ⟨representatives, fun A hA hAA ↦ hcover A ⟨hA, hAA⟩, hcard⟩

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
      n ^ (r + 1) * (2 * Real.exp 1 * s / t) ^ t * Real.exp (t ^ ((31 : ℝ) / 32)) := by
  rw [← smallSumsetClassCountThreshold_def] at ht
  exact smallSumsetFreimanDimSets_ncard_le_of_class_cover n r s t ht hs

end CountingSetsWithSmallSumset
