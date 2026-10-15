/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module  -- shake: keep-all

public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.DimensionAndCounting
public import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationAndExtensionCodes
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ClassCountBounds
public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreAndCovers

/-!
# Counting sets with small sumset

Sections 3 and 4 of Green, *Counting sets with small sumset, and the clique number of random
Cayley graphs*, for finite sets of natural numbers.

## Main statements

* `card_boundedFreimanDimSets`: there are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with
  `t` elements and Freiman dimension at most `r`.
* `exists_smallRestrictedSumsetFreimanClassCover`: if `t ≥ 2 ^ 9000` and `m ≤ t ^ (31 / 30)`, the
  sets of `t` natural numbers whose restricted sumset has at most `m` elements lie in at most
  `(e * m / t) ^ t * exp (t ^ (31 / 32))` Freiman isomorphism classes of order `2`.
* `smallSumsetFreimanDimSets_ncard_le_of_class_cover`: if `t ≥ 2 ^ 9000` and
  `s ≤ t ^ (31 / 30) / 2`, there are at most
  `n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ [n]` with `|X| = t`,
  `freimanDim X ≤ r` and `|X + X| ≤ s`.
-/
