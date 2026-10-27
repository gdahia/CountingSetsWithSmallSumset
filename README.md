# Counting sets with small sumset

Lean 4 proof of the results of Ben Green,
[*Counting sets with small sumset, and the clique number of random Cayley graphs*](https://arxiv.org/abs/math/0304183),
Combinatorica 25 (2005), 307–326. The paper bounds the number of sets of given size and given
size of restricted sumset in $\mathbb{Z}/N\mathbb{Z}$ and in $\mathbb{F}_2^n$. With these bounds
it shows that a random Cayley sum graph on $\mathbb{Z}/N\mathbb{Z}$ almost surely has clique
number $O(\log N)$, and that a random Cayley graph on $\mathbb{F}_2^n$, where $N = 2^n$, almost
surely has clique number of order $\log N \log \log N$.

## Results

The results of the paper are numbered as in version 2 of the arXiv preprint, where theorems,
propositions, lemmas and corollaries share one counter. Theorems 1 and 2 below are Theorem 7 of
the paper, Theorem 3 is its Theorem 8, and Theorems 4 and 5 are its Theorem 9. Theorems 7 and 9
of the paper are proved as limits, as in the paper, and as bounds for the number of exceptional
sets.

**Theorem 1** (`card_cliqueNum_cayleySumGraph_gt_le'`). Let $N$ be a positive integer. If
$\log_2 N \ge 2^{9000}$, then

$$\left|\lbrace A \subseteq \mathbb{Z}/N\mathbb{Z} : \omega(G_A) > 160 \log_2 N \rbrace\right| \le \frac{2^N}{N},$$

where $G_A$ is the Cayley sum graph of $A$, with an edge between distinct $x$ and $y$ when
$x + y \in A$ (`cayleySumGraph A`), and $\omega(G)$ is the clique number of $G$
(`SimpleGraph.cliqueNum`).

**Theorem 2** (`tendsto_card_cliqueNum_cayleySumGraph_le'`). As $N \to \infty$, we have

$$\frac{\left|\lbrace A \subseteq \mathbb{Z}/N\mathbb{Z} : \omega(G_A) \le 160 \log_2 N \rbrace\right|}{2^N} \to 1.$$

**Theorem 3** (`exists_cliqueNum_le_and_indepNum_le'`). Let $N$ be a positive integer. If
$\log_2 N \ge 2^{9000}$, then there is a set $A \subseteq \mathbb{Z}/N\mathbb{Z}$ with

$$\omega(G_A) \le 160 \log_2 N \quad \text{and} \quad \alpha(G_A) \le 160 \log_2 N,$$

where $\alpha(G)$ is the independence number of $G$ (`SimpleGraph.indepNum`).

**Theorem 4** (`card_cliqueNum_addCayley_lt_or_gt_le'`). Let $N = 2^n$. If $n \ge 2^{9000}$, then

$$\left|\lbrace A \subseteq \mathbb{F}_2^n : \omega(G_A) < \tfrac{1}{4} n \log_2 n \text{ or } \omega(G_A) > 308\, n \log_2 n \rbrace\right| \le \frac{2^N}{n} + \frac{2^N}{N},$$

where $G_A$ is the Cayley graph of $A$ (`SimpleGraph.addCayley A`), which is the Cayley sum graph of
$A$ since $x + y = y - x$ in $\mathbb{F}_2^n$.

**Theorem 5** (`tendsto_card_le_cliqueNum_addCayley_le'`). As $n \to \infty$, we have

$$\frac{\left|\lbrace A \subseteq \mathbb{F}_2^n : \tfrac{1}{4} n \log_2 n \le \omega(G_A) \le 308\, n \log_2 n \rbrace\right|}{2^N} \to 1.$$

Since $\log_2 N = n$, these are the constants $C_1 = 1/4$ and $C_2 = 308$ of the paper.

[Challenge.lean](CountingSetsWithSmallSumsetPalomar/Challenge.lean) contains these five
statements, under the library names with a prime and with `sorry` placeholders, together with the
definition of `cayleySumGraph`. [Solution.lean](CountingSetsWithSmallSumsetPalomar/Solution.lean)
proves each statement by the library theorem without the prime. The library and the solution
contain no `sorry`, and the theorems depend on no axioms other than `propext`, `Classical.choice`
and `Quot.sound`.

## Files

| Files in `CountingSetsWithSmallSumset/` | Contents |
| --- | --- |
| `RestrictedSumset.lean` | The restricted sumset |
| `RestrictedSumsetCardSets.lean` | Definition 3 |
| `CayleySumGraph.lean` | Cayley sum graphs, their cliques, and the Cayley graph in exponent $2$ |
| `RpowBounds.lean` | Inequalities for real powers of large numbers |
| `AlmostAllSets.lean` | Proportions of subsets with a property |
| `FreimanIsomorphismClasses/Representatives.lean` | Freiman isomorphic sets and representatives of the isomorphism classes of a family |
| `FreimanIsomorphismClasses/Relations.lean` | Additive relations of tuples |
| `FreimanIsomorphismClasses/RelationSpaces.lean` | Relation vectors and relation spaces over a field, Lemmas 10 and 11 |
| `FreimanIsomorphismClasses/ExtensionReferences.lean` | The extension references behind Lemma 16 |
| `FreimanIsomorphismClasses/MembersInInterval.lean` | The members in $[n]$ of a Freiman isomorphism class, used for Proposition 23 |
| `FreimanDimension/HomSpace.lean` | $\mathrm{Hom}_2(A, M)$ and $r_F(A)$ |
| `FreimanDimension/Interpolation.lean` | Lemma 12 |
| `FreimanDimension/Basis.lean` | Lemma 13 |
| `FreimanDimension/IsomorphicCopies.lean` | The number of Freiman isomorphic copies of a set |
| `FreimanDimension/AffineModel.lean` | Corollary 14 |
| `FreimanDimension/RationalVectors.lean` | Rational vectors as real vectors |
| `FreimanDimension/Integers.lean` | Corollary 14 for sets of integers and of natural numbers |
| `SmallSumsetIsomorphismClasses/CoreDecomposition.lean` | The random choice of the core in Proposition 15 |
| `SmallSumsetIsomorphismClasses/CoreParameters.lean` | Proposition 15 |
| `SmallSumsetIsomorphismClasses/ExtensionAndRemainderClasses.lean` | Lemmas 16 and 17 |
| `SmallSumsetIsomorphismClasses/CoreAndRepresentatives.lean` | Representatives of the classes of the sets with small restricted sumset |
| `SmallSumsetIsomorphismClasses/ClassCountBounds.lean` | Proposition 18 |
| `LargeRestrictedSumset/SummingQuadruples.lean` | Summing quadruples and the Cauchy–Schwarz bound |
| `LargeRestrictedSumset/SubsetAveraging.lean` | Subsets with few non-degenerate summing quadruples |
| `LargeRestrictedSumset/SmallSubset.lean` | Proposition 19 |
| `LargeRestrictedSumset/LargeSubset.lean` | Corollary 20 |
| `FreimanLemma/RestrictedSumset.lean` | Lemma 21 |
| `CyclicGroups/Unfolding.lean` | Lemma 22 |
| `CyclicGroups/RestrictedSumsetCardBounds.lean` | Proposition 23 |
| `CyclicGroups/LargeRestrictedSumsetSum.lean` | The sum of Section 7 for $\mathbb{Z}/N\mathbb{Z}$ |
| `CyclicGroups/CliqueNumber.lean` | Theorem 7, as a count and as a limit |
| `CyclicGroups/RamseyGraph.lean` | Theorem 8 |
| `CliqueCount.lean` | Cayley sum graphs with a large clique |
| `BinaryGroups/Sumsets.lean` | Sumsets and restricted sumsets in characteristic $2$ |
| `BinaryGroups/IteratedSumsets.lean` | Sums of distinct elements of an affinely independent set |
| `BinaryGroups/FreimanDimension.lean` | Lemma 25 |
| `BinaryGroups/RestrictedSumsetCardBounds.lean` | Proposition 26 |
| `BinaryGroups/LargeRestrictedSumsetSum.lean` | The sum of Section 7 for $\mathbb{F}_2^n$ |
| `BinaryGroups/CliqueNumber.lean` | The upper bound of Theorem 9, and Theorem 9 |
| `BinaryLowerBound/SecondMoment.lean` | The second moment method for a uniformly random set |
| `BinaryLowerBound/SubspaceCount.lean` | The number of subspaces of $\mathbb{F}_2^n$ of a given dimension |
| `BinaryLowerBound/SubspacePairs.lean` | Lemma 28 |
| `BinaryLowerBound/Covariance.lean` | The covariance terms for subspaces |
| `BinaryLowerBound/SubspaceDimension.lean` | The dimension of the subspaces in Proposition 27 |
| `BinaryLowerBound/CliqueNumber.lean` | Proposition 27 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Build

The Lean and Mathlib versions and the commit of SumOfSetsInSeveralDimensions are pinned in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library and the solution. `lake build Challenge` builds the
challenge, and its five `sorry` warnings are expected.

## Verification

`Challenge.lean` imports only the Mathlib modules `Mathlib.Analysis.SpecialFunctions.Log.Base`,
`Mathlib.Combinatorics.SimpleGraph.Cayley` and `Mathlib.Combinatorics.SimpleGraph.Clique`. It
defines `cayleySumGraph` as the library does and states the five theorems above with `sorry`.
[comparator.json](comparator.json) names these five theorems,
`CountingSetsWithSmallSumsetPalomar.Challenge` and `CountingSetsWithSmallSumsetPalomar.Solution`
as the modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as the permitted
axioms. The two modules sit in `CountingSetsWithSmallSumsetPalomar/` rather than at the root, so
that they do not clash with the `Challenge` and `Solution` modules of the projects this one
requires or is required by.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
