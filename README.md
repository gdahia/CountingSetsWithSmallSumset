# Counting sets with small sumset

Lean 4 proof of the results of Ben Green,
[*Counting sets with small sumset, and the clique number of random Cayley graphs*](https://arxiv.org/abs/math/0304183),
Combinatorica 25 (2005), 307–326. The paper bounds the number of sets of given size and given
size of restricted sumset in $\mathbb{Z}/N\mathbb{Z}$ and in $\mathbb{F}_2^n$. With these bounds
it shows that a random Cayley sum graph on $\mathbb{Z}/N\mathbb{Z}$ almost surely has clique
number $O(\log N)$, and that a random Cayley graph on $\mathbb{F}_2^n$, where $N = 2^n$, almost
surely has clique number of order $\log N \log \log N$.

The affine dimension of a finite set, Freiman's definition of the Freiman dimension and Freiman's
lemma come from
[SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions), the proof
of Ruzsa's lower bound for sumsets in several dimensions.

## Results

The statements of the paper are numbered as in version 2 of the arXiv preprint, where theorems,
propositions, lemmas and corollaries share one counter. Statements for sufficiently large
parameters are proved above explicit thresholds, and statements about almost all sets are proved
as bounds for the number of exceptional sets.

The restricted sumset of a finite set $A$ is $A \hat{+} A = \lbrace a + b : a, b \in A,\ a \ne b \rbrace$
(`restrictedSumset A`). For a finite abelian group $\Gamma$, $S_k^m(\Gamma)$ is the family of the
sets $X \subseteq \Gamma$ with $|X| = k$ and $|X \hat{+} X| = m$ (`restrictedSumsetCardSets Γ k m`,
Definition 3). The Cayley sum graph $G_A$ of $A \subseteq \Gamma$ has an edge between distinct $x$
and $y$ when $x + y \in A$ (`cayleySumGraph A`). In $\mathbb{F}_2^n$, where $x + y = y - x$, it is
Mathlib's Cayley graph `SimpleGraph.addCayley A`, and the statements for $\mathbb{F}_2^n$ use that
graph. We write $\omega(G)$ for the clique number (`SimpleGraph.cliqueNum`).

Two sets are Freiman isomorphic of order $2$ if there is a bijection between them that preserves
the equalities $a + b = c + d$ in both directions (`IsAddFreimanIso 2` in Mathlib). For a finite
set $A$ in an abelian group and a field $F$, $\mathrm{Hom}_2(A, F)$ is the space of the maps
$\varphi : A \to F$ with $\varphi(a) + \varphi(b) = \varphi(c) + \varphi(d)$ whenever
$a + b = c + d$ (`freimanHomSpace F F A`). Green defines the Freiman dimension of $A$ as
$r_F(A) = \dim \mathrm{Hom}_2(A, F) - 1$ (`freimanDimOver F A`). Freiman's dimension
(`SumOfSetsInSeveralDimensions.freimanDim`) is the largest $d \le |A|$ such that $A$ is Freiman
isomorphic of order $2$ to a subset of $\mathbb{Q}^d$ whose affine span in $\mathbb{R}^d$ is the
whole space.

**Theorem 7** (`card_cliqueNum_cayleySumGraph_gt_le'`). If $\log_2 N \ge 2^{9000}$, then

$$\left|\lbrace A \subseteq \mathbb{Z}/N\mathbb{Z} : \omega(G_A) > 160 \log_2 N \rbrace\right| \le \frac{2^N}{N}.$$

**Theorem 8** (`exists_cliqueNum_le_and_indepNum_le'`). If $\log_2 N \ge 2^{9000}$, there is a
set $A \subseteq \mathbb{Z}/N\mathbb{Z}$ such that the clique number and the independence number
of $G_A$ are at most $160 \log_2 N$.

**Theorem 9** (`card_cliqueNum_addCayley_lt_or_gt_le'` and
`tendsto_card_le_cliqueNum_addCayley_le'`). Let $N = 2^n$. If $n \ge 2^{9000}$, then

$$\left|\lbrace A \subseteq \mathbb{F}_2^n : \omega(G_A) < \tfrac{1}{4} n \log_2 n \text{ or } \omega(G_A) > 308\, n \log_2 n \rbrace\right| \le \frac{2^N}{n} + \frac{2^N}{N}.$$

Hence the proportion of the sets $A \subseteq \mathbb{F}_2^n$ with
$\frac{1}{4} n \log_2 n \le \omega(G_A) \le 308\, n \log_2 n$ tends to $1$. Since $\log_2 N = n$,
these are the constants $C_1 = 1/4$ and $C_2 = 308$ of the paper.

**Corollary 14** (`isGreatest_freimanDimOver'` and `freimanDimOver_rat_eq_freimanDim_int'`). Let
$A$ be a nonempty finite subset of a vector space over a field $F$. Then $r_F(A)$ is the largest
$d$ such that $A$ is Freiman isomorphic of order $2$ to a subset of $F^d$ of affine dimension $d$.
For a finite set $X$ of integers, $r_{\mathbb{Q}}(X)$ is Freiman's dimension of $X$.

**Proposition 18** (`exists_coversFreimanIsoClasses_card_restrictedSumset_le'`). Let $W$ be a
vector space over a field $F$, $t \ge 2^{9000}$ and $m \le t^{31/30}$. There is a family of at
most $(em/t)^t \exp(t^{31/32})$ finite subsets of $W$ such that every $A \subseteq W$ with
$|A| = t$ and $|A \hat{+} A| \le m$ is Freiman isomorphic of order $2$ to a member of the family.

**Proposition 19** (`exists_subset_card_le_and_le_card_restrictedSumset'`). Let
$0 < \varepsilon \le 1/2$ and let $A$ be a finite subset of an abelian group with
$|A| \ge 16/\varepsilon^2$. There is a set $B \subseteq A$ with

$$|B| \le \frac{3 \log_2(1/\varepsilon)}{\varepsilon} \sqrt{|A|} \quad \text{and} \quad |B \hat{+} B| \ge (1 - \varepsilon)|A|.$$

**Proposition 23** (`card_restrictedSumsetCardSets_zmod_le_of_le_rpow'` and
`card_restrictedSumsetCardSets_zmod_le'`). If $k \ge 2^{9000}$ and $m \le k^{31/30}/2$, then

$$|S_k^m(\mathbb{Z}/N\mathbb{Z})| \le N^{1 + 4m/k} \left(\frac{2em}{k}\right)^k \exp(k^{31/32}),$$

and for every $k \ge 1$ and every $m$, $|S_k^m(\mathbb{Z}/N\mathbb{Z})| \le N^{1 + 4m/k} k^{4k}$.

**Proposition 26** (`card_restrictedSumsetCardSets_pi_zmod_two_le_of_le_rpow'` and
`card_restrictedSumsetCardSets_pi_zmod_two_le'`). Let $N = 2^n$. If $k \ge 2^{9000}$ and
$m \le k^{31/30}$, then

$$|S_k^m(\mathbb{F}_2^n)| \le N^{4m \log_2 k / k} \left(\frac{em}{k}\right)^k \exp(k^{31/32}),$$

and for every $k \ge 2$ and every $m$, $|S_k^m(\mathbb{F}_2^n)| \le N^{4m \log_2 k / k} k^{4k}$.

[Solution.lean](Solution.lean) proves these twelve statements. [Challenge.lean](Challenge.lean)
contains them with `sorry` placeholders, together with the definitions they use, restated in
terms of Mathlib: `finsetAffineDim`, `rationalVectorToReal`, `freimanModelDim` and `freimanDim` of
SumOfSetsInSeveralDimensions, and `restrictedSumset`, `cayleySumGraph`,
`restrictedSumsetCardSets`, `freimanHomSpace` and `freimanDimOver` of this library. The library and
the solution contain no `sorry`, and the theorems depend on no axioms other than `propext`,
`Classical.choice` and `Quot.sound`. The statements of the challenge carry a prime; the library
proves them under the same names without it.

The other results of the paper are proved in the library. Theorems 4, 5 and 6, which the paper
cites, and Proposition 29, which it states without proof, are not formalized.

| Declaration | Statement |
| --- | --- |
| `exists_isAddFreimanIso_range_of_freimanRelationSpace_eq` | Lemma 10: two injective tuples in vector spaces over $F$ whose relations of order $s$ span the same subspace have ranges that are Freiman isomorphic of order $s$ |
| `exists_coversFreimanIsoClasses_card_le_pow` | Lemma 11: a family of at most $k^{2sk}$ sets meets every Freiman isomorphism class of order $s$ of $k$-element subsets of a vector space |
| `exists_interpolation_points` | Lemma 12: a $d$-dimensional space of functions on a finite set has $d$ points at which its members take any values, each exactly once |
| `exists_freimanBasis_of_module` | Lemma 13: $A$ has $r_F(A) + 1$ points at which the members of $\mathrm{Hom}_2(A, M)$ take any values, and, for $A$ in a vector space over $F$, a homomorphism with linearly independent values at these points satisfies no relations $\varphi(a) + \varphi(b) = \varphi(c) + \varphi(d)$ other than those of $A$ |
| `finrank_freimanHomSpace`, `card_freimanHomSpace` | $\dim \mathrm{Hom}_2(A, M) = (r_F(A) + 1) \dim M$ and $\lvert\mathrm{Hom}_2(A, M)\rvert = \lvert M\rvert^{r_F(A) + 1}$ |
| `ncard_isAddFreimanIso_le` | At most $\lvert F\rvert^{n(r_F(A) + 1)}$ subsets of $F^n$ are Freiman isomorphic to $A$ |
| `isGreatest_freimanDimOver_of_isAddFreimanIso`, `freimanDimOver_rat_eq_freimanDim_nat` | Corollary 14 for a set with a Freiman isomorphism into a vector space, and for a set of natural numbers |
| `exists_image_add_subset_restrictedSumset` | Proposition 15, for $t \ge 2^{9000}$ and any $m \ge t$ with $\lvert A \hat{+} A\rvert \le m$ |
| `exists_coversFreimanIsoClasses_extensionsOfFreimanClass_card_le` | Lemma 16, with order $4$ in place of $3$ |
| `exists_subset_restrictedSumset_freimanIsomorphic` | Lemma 17, with orders $8$ and $4$ in place of $6$ and $3$ |
| `exists_coversFreimanIsoClasses_card_restrictedSumset_le_of_injective` | Proposition 18 for sets with an injective additive map into a vector space, such as sets of natural numbers |
| `exists_subset_seven_mul_card_le_card_restrictedSumset` | Corollary 20: if $\lvert A\rvert \ge 46656$, some $C \subseteq A$ has $\lvert A\rvert \le 8\lvert C\rvert$ and $\lvert C \hat{+} C\rvert \ge 7\lvert C\rvert$ |
| `freimanDim_mul_le_card_restrictedSumset` | Lemma 21 (Freiman): $\lvert S \hat{+} S\rvert \ge r(\lvert S\rvert - (r + 1)/2)$ for $r$ Freiman's dimension of $S$ |
| `freimanDim_zmodLift_le` | Lemma 22: the lift of $A \subseteq \mathbb{Z}/N\mathbb{Z}$ to $\lbrace 1, \dots, N \rbrace$ has Freiman dimension at most $4\lvert A \hat{+} A\rvert / \lvert A\rvert$ |
| `Finset.pluennecke_ruzsa_inequality_nsmul_add` | Theorem 24, the Plünnecke–Ruzsa inequality, from Mathlib |
| `freimanDimOver_add_one_le_of_card_restrictedSumset_le` | Lemma 25: if $\lvert A\rvert = k \ge 2$ and $\lvert A \hat{+} A\rvert \le m$ in a vector space over $\mathbb{F}_2$, then $r_{\mathbb{F}_2}(A) + 1 \le 4m \log_2 k / k$ |
| `sum_card_restrictedSumsetCardSets_zmod_div_two_pow_le`, `sum_card_restrictedSumsetCardSets_pi_zmod_two_div_two_pow_le` | The sums of $\lvert S_j^m\rvert 2^{-m}$ over $7j \le m \le N$ in Section 7 are at most $N^{-2}$ |
| `card_lt_cliqueNum_cayleySumGraph_le` | The first step of the proofs of Theorems 7 and 9 |
| `card_cliqueNum_addCayley_gt_le` | The upper bound of Theorem 9: at most $2^N/N$ sets $A \subseteq \mathbb{F}_2^n$ have $\omega(G_A) > 308\, n \log_2 n$ |
| `card_cliqueNum_addCayley_lt_le`, `tendsto_card_le_cliqueNum_addCayley` | Proposition 27, for $n \ge 2^{16}$: at most $2^N/n$ sets $A \subseteq \mathbb{F}_2^n$ have $\omega(G_A) < \frac{1}{4} n \log_2 n$ |
| `card_finrank_inf_eq_le` | Lemma 28: at most $2^{n(2k - l)}$ pairs of $k$-dimensional subspaces of $\mathbb{F}_2^n$ meet in an $l$-dimensional subspace |
| `cayleySumGraph_eq_addCayley` | In a group of exponent $2$, the Cayley sum graph is Mathlib's Cayley graph |
| `card_boundedFreimanDimSets` | Not in the paper: at most $n^{r + 1} t^{4t}$ sets $X \subseteq \lbrace 1, \dots, n \rbrace$ have $t > 0$ elements and Freiman dimension at most $r$ |
| `smallSumsetFreimanDimSets_ncard_le_of_class_cover` | Not in the paper: if $t \ge 2^{9000}$ and $s \le t^{31/30}/2$, at most $n^{r + 1} (2es/t)^t \exp(t^{31/32})$ sets $X \subseteq \lbrace 1, \dots, n \rbrace$ have $t$ elements, Freiman dimension at most $r$ and $\lvert X + X\rvert \le s$ |

## Files

| Files in `CountingSetsWithSmallSumset/` | Contents |
| --- | --- |
| `RestrictedSumset.lean` | The restricted sumset |
| `RestrictedSumsetCardSets.lean` | Definition 3 |
| `CayleySumGraph.lean` | Cayley sum graphs, their cliques, and the Cayley graph in exponent $2$ |
| `RpowBounds.lean` | Inequalities for real powers of large numbers |
| `FreimanIsomorphismClasses/Covers.lean` | Freiman isomorphic sets and covers of a family by isomorphism classes |
| `FreimanIsomorphismClasses/Relations.lean` | Additive relations of tuples |
| `FreimanIsomorphismClasses/RelationCodes.lean` | Relation vectors over a field, Lemmas 10 and 11 |
| `FreimanIsomorphismClasses/ExtensionCodes.lean` | The extension codes behind Lemma 16 |
| `FreimanIsomorphismClasses/BoundedFreimanDimSets.lean` | Sets of natural numbers of bounded Freiman dimension |
| `FreimanDimension/HomSpace.lean` | $\mathrm{Hom}_2(A, M)$ and $r_F(A)$ |
| `FreimanDimension/Interpolation.lean` | Lemma 12 |
| `FreimanDimension/Basis.lean` | Lemma 13 |
| `FreimanDimension/IsomorphicCopies.lean` | The number of Freiman isomorphic copies of a set |
| `FreimanDimension/AffineModel.lean` | Corollary 14 |
| `FreimanDimension/RationalVectors.lean` | Rational vectors as real vectors |
| `FreimanDimension/Integers.lean` | Corollary 14 for sets of integers and of natural numbers |
| `SmallSumsetIsomorphismClasses/CoreDecomposition.lean` | The random choice of the core in Proposition 15 |
| `SmallSumsetIsomorphismClasses/CoreParameters.lean` | Proposition 15 |
| `SmallSumsetIsomorphismClasses/ExtensionAndRemainderCovers.lean` | Lemmas 16 and 17 |
| `SmallSumsetIsomorphismClasses/CoreAndCovers.lean` | The cover of the sets with small restricted sumset by classes |
| `SmallSumsetIsomorphismClasses/ClassCountBounds.lean` | Proposition 18 and the counts of sets of natural numbers |
| `LargeRestrictedSumset/SummingQuadruples.lean` | Summing quadruples and the Cauchy–Schwarz bound |
| `LargeRestrictedSumset/SubsetAveraging.lean` | Subsets with few non-degenerate summing quadruples |
| `LargeRestrictedSumset/SmallSubset.lean` | Proposition 19 |
| `LargeRestrictedSumset/LargeSubset.lean` | Corollary 20 |
| `FreimanLemma/RestrictedSumset.lean` | Lemma 21 |
| `CyclicGroups/Unfolding.lean` | Lemma 22 |
| `CyclicGroups/RestrictedSumsetCardBounds.lean` | Proposition 23 |
| `CyclicGroups/LargeRestrictedSumsetSum.lean` | The sum of Section 7 for $\mathbb{Z}/N\mathbb{Z}$ |
| `CyclicGroups/CliqueNumber.lean` | Theorem 7 |
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

[formalization.yaml](formalization.yaml) records the differences from the paper, the scope, and
the use of AI coding agents.

## Build

The Lean and Mathlib versions and the commit of SumOfSetsInSeveralDimensions are pinned in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
