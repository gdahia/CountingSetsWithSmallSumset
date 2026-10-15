# Counting sets with small sumset

Lean 4 proof of the results of Sections 3 and 4 of Ben Green,
[*Counting sets with small sumset, and the clique number of random Cayley graphs*](https://arxiv.org/abs/math/0304183),
Combinatorica 25 (2005), 307–326, for finite sets of natural numbers: a bound for the number of
Freiman isomorphism classes of sets with small restricted sumset, and bounds for the number of
subsets of $\lbrace 1, \dots, n \rbrace$ of given size and Freiman dimension. The statements have
the form used to count pairs of sets with a sumset of moderate size in Gabriel Dahia, João Pedro
Marciano and Victor Souza,
[*Dense sets without large sumsets*](https://arxiv.org/abs/2607.15269).

The proofs come from
[DenseSetsWithoutLargeSumsets](https://github.com/gdahia/DenseSetsWithoutLargeSumsets). The
affine dimension of a finite set and the definition of the Freiman dimension are those of
[SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions), the proof
of Ruzsa's lower bound for sumsets in several dimensions.

## Results

The statements of Green's paper are numbered as in version 2 of the arXiv preprint, where
theorems, propositions, lemmas and corollaries share one counter.

Two sets are Freiman isomorphic of order $s$ if there is a bijection between them that preserves
the equalities $a_1 + \dots + a_s = b_1 + \dots + b_s$ in both directions (`IsAddFreimanIso s` in
Mathlib). The restricted sumset of $A$ is the set of the sums $a + b$ with $a, b \in A$ and
$a \ne b$. The Freiman dimension `freimanDim X` (`SumOfSetsInSeveralDimensions.freimanDim`) of a
finite set $X$ is the largest $d \le |X|$ such that $X$ is Freiman isomorphic of order $2$ to a
subset of $\mathbb{Q}^d$ that is not contained in a proper affine subspace. The last condition is
stated with the affine dimension `finsetAffineDim` of the subset in $\mathbb{R}^d$, the dimension
of the direction of its affine span.

**Sets of bounded Freiman dimension**
(`CountingSetsWithSmallSumset.ncard_setOf_card_eq_freimanDim_le_le`). Let $t > 0$. There are at
most $n^{r + 1} t^{4t}$ sets $X \subseteq \lbrace 1, \dots, n \rbrace$ with $t$ elements and
Freiman dimension at most $r$.

**Isomorphism classes of sets with small restricted sumset**
(`CountingSetsWithSmallSumset.exists_forall_exists_isAddFreimanIso_card_le`). Let
$t \ge 2^{9000}$ and $m \le t^{31/30}$. There is a family of at most
$(em/t)^t \exp(t^{31/32})$ finite sets such that every set of $t$ natural numbers whose
restricted sumset has at most $m$ elements is Freiman isomorphic of order $2$ to a member of the
family.

**Sets with small sumset**
(`CountingSetsWithSmallSumset.ncard_setOf_card_eq_freimanDim_le_card_add_le_le`). Let
$t \ge 2^{9000}$ and $s \le t^{31/30}/2$. There are at most
$n^{r + 1} (2es/t)^t \exp(t^{31/32})$ sets $X \subseteq \lbrace 1, \dots, n \rbrace$ with $t$
elements, Freiman dimension at most $r$ and $|X + X| \le s$.

[Solution.lean](Solution.lean) proves the three. [Challenge.lean](Challenge.lean) contains the
same statements, with the definitions of `finsetAffineDim`, `rationalVectorToReal`,
`freimanModelDim` and `freimanDim`, in terms of Mathlib and with `sorry` placeholders. The
library and the solution contain no `sorry`, and the theorems depend on no axioms other than
`propext`, `Classical.choice` and `Quot.sound`.

| Statement | Library form | Green's paper |
| --- | --- | --- |
| `ncard_setOf_card_eq_freimanDim_le_le` | `card_boundedFreimanDimSets` | Not stated. Lemma 11 with $s = 2$ and Lemma 13 (i), combined as in the proof of the second bound of Proposition 23 |
| `exists_forall_exists_isAddFreimanIso_card_le` | `exists_smallRestrictedSumsetFreimanClassCover` | Proposition 18 |
| `ncard_setOf_card_eq_freimanDim_le_card_add_le_le` | `smallSumsetFreimanDimSets_ncard_le_of_class_cover` | Not stated. The count in the proof of the first bound of Proposition 23 |

The library forms are written with the definitions `boundedFreimanDimSets`,
`smallSumsetFreimanDimSets`, `smallRestrictedSumsetSets`, `restrictedSumset`,
`CoversFreimanClasses`, `FreimanEquivalent` and `smallSumsetClassCountThreshold`, which the
statements above unfold.

The statements differ from the paper as follows.

- Proposition 18 is for subsets of $F^k$ with $k$ elements, where $F$ is a field and $k$ is
  sufficiently large. Here the sets are sets of natural numbers and the threshold is
  $2^{9000}$. The number of classes is bounded through a family of sets that contains a member
  of each class. The members of the family need not have small restricted sumset, and two of
  them may be isomorphic.
- Proposition 23 bounds the number of subsets of $\mathbb{Z}/N\mathbb{Z}$ with $k$ elements
  whose restricted sumset has $m$ elements by $N^{1 + 4m/k} (2em/k)^k \exp(k^{31/32})$ if
  $m \le k^{31/30}/2$, and by $N^{1 + 4m/k} k^{4k}$ for every $m$. Its proof lifts such a set to
  a subset of $\lbrace 1, \dots, N \rbrace$ whose restricted sumset has at most $2m$ elements,
  counts the isomorphism classes of the lifts, and bounds their Freiman dimension by $4m/k$ with
  a lemma of Freiman (Lemmas 21 and 22). The statements here count subsets of
  $\lbrace 1, \dots, n \rbrace$, with the Freiman dimension as a parameter $r$. The reduction
  from $\mathbb{Z}/N\mathbb{Z}$ and Lemmas 21 and 22 are not formalized.
- The third statement bounds the sumset $X + X$, which contains the restricted sumset. Its proof
  applies the bound for the number of classes with $m = 2s$, as the paper does for the lifts.
  This is the source of the factor $2$.
- The paper defines the Freiman dimension of $X$ as $\dim \mathrm{Hom}_2(X, \mathbb{Q}) - 1$,
  where $\mathrm{Hom}_2(X, \mathbb{Q})$ is the space of the Freiman homomorphisms of order $2$
  from $X$ to $\mathbb{Q}$. Its Corollary 14 states that this is the largest $d$ in the
  definition above. The corollary is not formalized. The library proves that the dimension of
  the model of $X$ built from its relations is at most `freimanDim X`
  (`relationModelDim_le_freimanDim`), which is what the counts use.

## Proof and files

A tuple $a = (a_1, \dots, a_t)$ of natural numbers satisfies a relation of order $s$ when two
sums of $s$ of its coordinates are equal. The coefficient vectors of the relations that $a$
satisfies span a subspace of $\mathbb{Q}^t$, and $a$ satisfies exactly the relations whose
vectors lie in it. This subspace is spanned by $t$ of these vectors, so it is determined by a
code of $t$ relations, and there are $t^{2st}$ codes (Lemma 11). Two injective tuples with the
same code have ranges that are Freiman isomorphic of order $s$ (Lemma 10). A set receives the
least code of its enumerations.

For relations of order $2$, the quotient of the space of vectors of $\mathbb{Q}^t$ with zero
coefficient sum by the relations of $a$ contains a Freiman isomorphic copy of the range of $a$
that spans it. Its dimension `relationModelDim a` is therefore at most the Freiman dimension of
the range. The quotient of $\mathbb{Q}^t$ by the relations has dimension one more than
`relationModelDim a` and is spanned by the classes of that many coordinate vectors, so a tuple
with the same relations as $a$ is determined by its values at these coordinates (Lemmas 12 and
13). Hence a Freiman isomorphism class of dimension at most $r$ has at most $n^{r + 1}$ members in
$\lbrace 1, \dots, n \rbrace$, and the first statement follows from the bound $t^{4t}$ for the
number of codes.

Let $A$ be a set of $t \ge 2^{9000}$ natural numbers whose restricted sumset has at most $m$
elements. Proposition 15 gives $a \in A$, a core $A_0 \subseteq A$ with at most
$4 t^{-1/15} m$ elements, and $A_1 \subseteq A$ missing at most $4 t^{-4/5} m$ elements of
$A$, such that $a + A_1$ is contained in the restricted sumset of $A_0$. The element $a$ is
chosen so that few sums $a + b$ have fewer than $\lfloor t^{1/5} \rfloor$ representations, and
$A_0$ is a random subset of $A$ of density $t^{-1/15}$. A sum with at least $Q$ representations
has at least $\lfloor Q/2 \rfloor$ disjoint ones, where the paper uses $Q/3$. The expectation is
a finite sum over the functions from $A$ to `Bool` with product weights.

The class of order $8$ of $A_0$ is one of at most $l^{16l}$, where $l = |A_0|$. Given this
class, the class of order $4$ of $a + A_1$ is one of at most $\binom{m}{|A_1|}$, since a subset
of the restricted sumset of $A_0$ is isomorphic of order $4$ to a subset of the restricted
sumset of any set in the class of $A_0$ (Lemma 17). Given the class of order $4$ of $A_1$, the
class of order $2$ of $A$ is one of at most $(1 + |A_1|^4)^{(d + 1)^4}$, where
$d = |A \setminus A_1|$ (Lemma 16). The sum of the products of these three numbers over $l$ and
$d$ is `freimanClassCountBound t m`, and it is at most $(em/t)^t \exp(t^{31/32})$ when
$m \le t^{31/30}$. The paper uses the orders $6$, $3$ and $2$ and the bound $l^{3t^4}$ in
Lemma 16.

| Files in `CountingSetsWithSmallSumset/` | Contents |
| --- | --- |
| `FreimanIsomorphismClasses/RelationAndExtensionCodes.lean` | Relations of a tuple and their codes, the restricted sumset, the random choice of the core, the codes behind Lemmas 16 and 17 |
| `FreimanIsomorphismClasses/DimensionAndCounting.lean` | The model of a set built from its relations, coordinates that determine a tuple, canonical codes of sets, `card_boundedFreimanDimSets` |
| `SmallSumsetIsomorphismClasses/CoreAndCovers.lean` | Proposition 15 with explicit parameters, the classes of Lemmas 16 and 17, the sum `freimanClassCountBound` |
| `SmallSumsetIsomorphismClasses/ClassCountBounds.lean` | The estimate of the sum, Proposition 18, the members of a class in $\lbrace 1, \dots, n \rbrace$, the count of sets with small sumset |

The four files come from DenseSetsWithoutLargeSumsets. They were written there up to commit
`5f4b915` and rewritten on 11 October 2026 with the same definitions and main statements. Here
they are in the namespace `CountingSetsWithSmallSumset`, and they use `Finset.Icc 1 n` where that
repository uses its definition `interval n`.

The library imports one module of SumOfSetsInSeveralDimensions,
`SumOfSetsInSeveralDimensions.FreimanDimension`, for the definitions `rationalVectorToReal`,
`freimanModelDim` and `freimanDim`. That module imports
`SumOfSetsInSeveralDimensions.AffineDim`, which defines `finsetAffineDim`.

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the automation used.

## Verification

`Challenge.lean` states the three results above as
`CountingSetsWithSmallSumset.ncard_setOf_card_eq_freimanDim_le_le`,
`CountingSetsWithSmallSumset.exists_forall_exists_isAddFreimanIso_card_le` and
`CountingSetsWithSmallSumset.ncard_setOf_card_eq_freimanDim_le_card_add_le_le`. It restates the
definitions `finsetAffineDim`, `rationalVectorToReal`, `freimanModelDim` and `freimanDim` under
their names in the namespace `SumOfSetsInSeveralDimensions`, imports Mathlib alone and leaves the
three proofs as `sorry`; the restricted sumset is written out as the image of
$(a, b) \mapsto a + b$ on the pairs of distinct elements of $A$. `Solution.lean` proves the same
declarations from the library, with the definitions taken from SumOfSetsInSeveralDimensions.

`comparator.json` sets up the comparison of the two modules: it names the three theorems and
permits only the axioms `propext`, `Quot.sound` and `Classical.choice`. A comparator checks that
each of these theorems has the same statement in `Solution` as in `Challenge`, with the same
definitions behind it, and that its proof uses no other axioms.

## Build

The Lean and Mathlib versions and the commit of SumOfSetsInSeveralDimensions are pinned in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. SumOfSetsInSeveralDimensions is a
private repository for now, so Lake cannot fetch it over HTTPS without credentials.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
