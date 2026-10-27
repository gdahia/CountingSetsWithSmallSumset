/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module  -- shake: keep-all

public import CountingSetsWithSmallSumset.AlmostAllSets
public import CountingSetsWithSmallSumset.BinaryGroups.CliqueNumber
public import CountingSetsWithSmallSumset.BinaryGroups.FreimanDimension
public import CountingSetsWithSmallSumset.BinaryGroups.IteratedSumsets
public import CountingSetsWithSmallSumset.BinaryGroups.LargeRestrictedSumsetSum
public import CountingSetsWithSmallSumset.BinaryGroups.RestrictedSumsetCardBounds
public import CountingSetsWithSmallSumset.BinaryGroups.Sumsets
public import CountingSetsWithSmallSumset.BinaryLowerBound.CliqueNumber
public import CountingSetsWithSmallSumset.BinaryLowerBound.Covariance
public import CountingSetsWithSmallSumset.BinaryLowerBound.SecondMoment
public import CountingSetsWithSmallSumset.BinaryLowerBound.SubspaceCount
public import CountingSetsWithSmallSumset.BinaryLowerBound.SubspaceDimension
public import CountingSetsWithSmallSumset.BinaryLowerBound.SubspacePairs
public import CountingSetsWithSmallSumset.CayleySumGraph
public import CountingSetsWithSmallSumset.CliqueCount
public import CountingSetsWithSmallSumset.CyclicGroups.CliqueNumber
public import CountingSetsWithSmallSumset.CyclicGroups.LargeRestrictedSumsetSum
public import CountingSetsWithSmallSumset.CyclicGroups.RamseyGraph
public import CountingSetsWithSmallSumset.CyclicGroups.RestrictedSumsetCardBounds
public import CountingSetsWithSmallSumset.CyclicGroups.Unfolding
public import CountingSetsWithSmallSumset.FreimanDimension.AffineModel
public import CountingSetsWithSmallSumset.FreimanDimension.Basis
public import CountingSetsWithSmallSumset.FreimanDimension.HomSpace
public import CountingSetsWithSmallSumset.FreimanDimension.Integers
public import CountingSetsWithSmallSumset.FreimanDimension.Interpolation
public import CountingSetsWithSmallSumset.FreimanDimension.IsomorphicCopies
public import CountingSetsWithSmallSumset.FreimanDimension.RationalVectors
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.BoundedFreimanDimSets
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Representatives
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.ExtensionReferences
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationSpaces
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.Relations
public import CountingSetsWithSmallSumset.FreimanLemma.RestrictedSumset
public import CountingSetsWithSmallSumset.LargeRestrictedSumset.LargeSubset
public import CountingSetsWithSmallSumset.LargeRestrictedSumset.SmallSubset
public import CountingSetsWithSmallSumset.LargeRestrictedSumset.SubsetAveraging
public import CountingSetsWithSmallSumset.LargeRestrictedSumset.SummingQuadruples
public import CountingSetsWithSmallSumset.RestrictedSumset
public import CountingSetsWithSmallSumset.RestrictedSumsetCardSets
public import CountingSetsWithSmallSumset.RpowBounds
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ClassCountBounds
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreAndRepresentatives
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreDecomposition
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreParameters
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ExtensionAndRemainderClasses

/-!
# Counting sets with small sumset

This library formalizes Ben Green, *Counting sets with small sumset, and the clique number of
random Cayley graphs*, Combinatorica 25 (2005), with the numbering of arXiv:math/0304183v2, where
all theorem-like statements share one counter. The Freiman dimension `r_F(A)` of a finite set `A`
is defined, as in the paper, as `dim Hom₂(A, F) - 1`. Statements for `t` or `k` sufficiently large
are proved for `t ≥ 2 ^ 9000` or a similar explicit bound. Statements about almost all sets are
proved as explicit bounds on the number of exceptional sets. Theorems 7 and 9 and Proposition 27
are also stated as limits, as in the paper.

## Main statements

* Definition 3: `restrictedSumsetCardSets`, the family `S_k^m(Γ)`.
* Lemma 10: `exists_isAddFreimanIso_range_of_freimanRelationSpace_eq`.
* Lemma 11: `exists_representsFreimanIsoClasses_card_le_pow`.
* Lemma 12: `exists_interpolation_points`.
* Lemma 13: `exists_freimanBasis_of_module`.
* Corollary 14: `isGreatest_freimanDimOver`, `isGreatest_freimanDimOver_of_isAddFreimanIso`, and,
  for Freiman's dimension `freimanDim`, `freimanDimOver_rat_eq_freimanDim_int` and
  `freimanDimOver_rat_eq_freimanDim_nat`.
* Proposition 15: `exists_image_add_subset_restrictedSumset`.
* Lemma 16: `exists_representsFreimanIsoClasses_extensionsOfFreimanClass_card_le`.
* Lemma 17: `exists_subset_restrictedSumset_freimanIsomorphic`.
* Proposition 18: `exists_representsFreimanIsoClasses_card_restrictedSumset_le`, and
  `exists_representsFreimanIsoClasses_card_restrictedSumset_le_of_injective` for sets with an
  injective additive map into a vector space, such as sets of natural numbers.
* Proposition 19: `exists_subset_card_le_and_le_card_restrictedSumset`.
* Corollary 20: `exists_subset_seven_mul_card_le_card_restrictedSumset`.
* Lemma 21: `freimanDim_mul_le_card_restrictedSumset`.
* Lemma 22: `freimanDim_zmodLift_le`.
* Proposition 23: `card_restrictedSumsetCardSets_zmod_le_of_le_rpow` (i) and
  `card_restrictedSumsetCardSets_zmod_le` (ii).
* Theorem 24 is the Plünnecke–Ruzsa inequality of Mathlib,
  `Finset.pluennecke_ruzsa_inequality_nsmul_add`.
* Lemma 25: `freimanDimOver_add_one_le_of_card_restrictedSumset_le`.
* Proposition 26: `card_restrictedSumsetCardSets_pi_zmod_two_le_of_le_rpow` (i) and
  `card_restrictedSumsetCardSets_pi_zmod_two_le` (ii).
* Theorem 7: `card_cliqueNum_cayleySumGraph_gt_le` and `tendsto_card_cliqueNum_cayleySumGraph_le`.
* Theorem 8: `exists_cliqueNum_le_and_indepNum_le`.
* Theorem 9: `card_cliqueNum_addCayley_lt_or_gt_le` and `tendsto_card_le_cliqueNum_addCayley_le`,
  with the upper bound `card_cliqueNum_addCayley_gt_le`.
* Proposition 27: `card_cliqueNum_addCayley_lt_le` and `tendsto_card_le_cliqueNum_addCayley`.
* Lemma 28: `card_finrank_inf_eq_le`.

The paper does not state the following counts of sets of natural numbers, which follow from
Lemma 11, Proposition 18 and the bound `n ^ (r + 1)` for the number of members of a Freiman
isomorphism class in `[n] = {1, …, n}`.

* `card_boundedFreimanDimSets`: there are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with
  `t` elements and Freiman dimension at most `r`.
* `smallSumsetFreimanDimSets_ncard_le`: if `t ≥ 2 ^ 9000` and
  `s ≤ t ^ (31 / 30) / 2`, there are at most
  `n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ [n]` with `|X| = t`,
  `freimanDim X ≤ r` and `|X + X| ≤ s`.
-/
