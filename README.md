# PAdicOrderType

Lean 4 formalization of the paper *The order types of the supports of p-adic
algebraic Hahn series* by Shanwen Wang and Yijun Yuan. The project proves the
support order-type trichotomy, characterizes strict p-adic Puiseux series, and
determines when a Hahn series and its p-adic shadow are both algebraic.

The seven main declarations are collected in
[MainResults](PAdicOrderType/MainResults.lean), in the namespace `PAdicOrderType`.
Theorem, proposition, lemma, and definition numbers below and in the docstrings
refer to the paper.

## Mathematical results

Fix a prime `p`. Write `Q_p` for the p-adic field, `Fp` for the field with `p`
elements, and `Fpbar` for its algebraic closure. The p-adic Hahn field `L_p`
consists of canonical expansions with rational exponents, Teichmüller
coefficients, and well-ordered support. In Lean it is written `𝕃_[p]`, and the
support order type of a series `f` is `Ordinal.typeLT f.support`.

Here `ω` is the first infinite ordinal, and `ω^ω` denotes ordinal exponentiation.

### Support order types

For every `f` in `L_p` algebraic over `Q_p`, the support has order type a finite
ordinal, `ω`, or `ω^ω` (Theorem A). Equivalently, its order type is at most `ω`
or exactly `ω^ω`. If its support is bounded, it is finite (Theorem B,
Proposition 4.2). These conclusions also apply to elements of `PadicAlgCl p`
through the chosen embedding into the Hahn field.

| Conclusion | Lean declaration |
| --- | --- |
| Order-type dichotomy, equivalent to Theorem A | `typeLT_support_le_omega0_or_eq_omega0_pow_omega0` |
| Theorem B: bounded support is finite | `support_finite_of_isAlgebraic_of_isBounded` |
| Theorem A: finite / `ω` / `ω^ω` trichotomy | `typeLT_support_eq_nat_or_eq_omega0_or_eq_omega0_pow_omega0` |
| Dichotomy in the algebraic closure | `typeLT_support_padicAlgCl_le_omega0_or_eq_omega0_pow_omega0` |

### Strict p-adic Puiseux series

Let `Q_p^un` be the maximal unramified extension of `Q_p`. The strict p-adic
Puiseux field is the union of `Q_p^un(p^(1/T))` over all positive integers `T`,
inside the algebraic closure. The roots of `p` are chosen compatibly with the
Hahn embedding, as in Section 1.1 of the paper. Lean represents this field by
`pAdicStrictPuiseux p`.

An algebraic series in `L_p` has support order type at most `ω` if and only if
it lies in the image of this field (Theorem C, Proposition 4.3). Its image also
consists exactly of the series with uniformly bounded exponent denominators and
finite coefficient range: some positive integer `T` makes `T * q` integral for
every support exponent `q`, and the canonical coefficients take only finitely
many values.

| Conclusion | Lean declaration |
| --- | --- |
| Theorem C: Puiseux image characterized by support order type | `typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range` |
| Theorem C in the algebraic closure | `typeLT_support_padicAlgCl_le_omega0_iff_mem_pAdicStrictPuiseux` |

The implication from small support order type uses finite truncations and
Krasner's lemma. Conversely, a common exponent denominator makes each bounded
initial segment of the support finite.

### Bialgebraicity

For an ordinary Hahn series `f : HahnSeries ℚ 𝔽ᵃ_[p]`, its shadow replaces each
term `a * t^q` by the Teichmüller term `[a] * p^q`; this is the shadow map of
Definition 2.7. The construction preserves the support and canonical coefficient
function. The theorem `bialgebraic_tfae` packages the following equivalences as
`List.TFAE`:

1. `f` is algebraic over `Fp((t))`, and `shadow f` is algebraic over `Q_p`.
2. `shadow f` lies in the image of the strict p-adic Puiseux field.
3. `shadow f` is algebraic over `Q_p` and has support order type at most `ω`.
4. The exponents of `f` have a common positive denominator and `Set.range f.coeff`
   is finite.

The first three conditions are Theorem D (Proposition 4.4) of the paper. The
fourth is the explicit coefficient criterion used in the formal proof.

### Completed algebraic closures

The map `shadowHomeomorph` is a homeomorphism between ordinary and p-adic Hahn
series for their valuation topologies. The theorem
`image_shadow_closure_algebraicClosure_eq_range_ofPadicComplex` identifies the
shadow image of the closure of the elements algebraic over `Fp((t))` with the
embedded p-adic complex field `ℂ_[p]`. Together they give Proposition 2.9. These
results are developed in [ShadowMap](PAdicOrderType/ShadowMap.lean).

## Proof and correspondence with the paper

Kedlaya's upper bound gives support order type at most `ω^ω` (Proposition 2.11).
The main argument excludes all order types strictly between `ω` and `ω^ω`
(Theorem 4.1):

1. Choose the greatest finite rank `r` attained by an integer closed truncation,
   the essential rank, and the least integer cutoff `B(f)` attaining it, the
   essential truncation point (Lemma 2.12, Definition 2.13). Rank zero already
   gives order type at most `ω`.
2. For positive rank, quasi-twist recurrence (QTR, Definition 2.5) of the closed
   truncations (Corollary 2.10) makes coefficients invariant under insertion of a
   fixed number of zeros into sufficiently long zero gaps. The long-gap criterion
   (Lemma 3.6) turns the order-type bounds into separated digit blocks and a
   bound on the number of occupied blocks (Lemmas 3.8 and 3.9).
3. Group coefficients by their scaled exponent cosets, giving the coefficients
   `A_d` and the carry-free sums `S_n(u)` of Section 3.1. A rigid digit vector
   bounds the valuation of a polynomial value (Definition 3.3, Proposition 3.4).
   At the maximum block count, carries and contributions from lower polynomial
   degrees are excluded (Lemma 3.11), the coefficients do not depend on the block
   positions (Lemma 3.12), and the remaining coefficient is a finite interleaving
   sum (Definition 3.13, Lemma 3.14).
4. A lexicographic argument proves that a nonzero word family has a nonzero
   interleaving power. Universal Nullstellensatz certificates bound the possible
   cancellation by a constant depending only on the degree and rank, for fixed `p`
   (Lemma 3.15).
5. This bounds the additive valuation of polynomial values at larger truncations
   independently of their cutoff (Lemma 3.16, Proposition 3.1). An annihilating
   polynomial forces those valuations to grow without bound, giving a
   contradiction (Theorem 4.1).

| Paper result | Lean declaration or construction |
| --- | --- |
| Theorem A: support order-type trichotomy | `typeLT_support_eq_nat_or_eq_omega0_or_eq_omega0_pow_omega0` |
| Theorem B / Proposition 4.2: bounded-support finiteness | `support_finite_of_isAlgebraic_of_isBounded` |
| Theorem C / Proposition 4.3: strict Puiseux characterization | `typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range` |
| Theorem D / Proposition 4.4: bialgebraicity | `bialgebraic_tfae` |
| Definition 2.3 / Lemma 2.4: digit vectors and uniqueness of normalization | `DigitSeries`, `DigitSeries.IsP`, `DigitSeries.norm`, `DigitSeries.eq_of_norm_sub_isInt` |
| Definition 2.5: QTR functions | `IsQTR` |
| Theorem 2.6, Theorem 2.8, Proposition 2.11: results of Kedlaya | `kedlaya_2001a_theorem15`, `kedlaya_2017_theorem13_4`, `kedlaya_2001b_ordinal_bound` from `TrustworthyKedlaya` |
| Definition 2.7 / Proposition 2.9: shadow map and completed algebraic closures | `shadowHomeomorph`, `image_shadow_closure_algebraicClosure_eq_range_ofPadicComplex` |
| Corollary 2.10: QTR of closed truncations | `exists_local_qtr` |
| Lemma 2.12 / Definition 2.13: essential rank and essential truncation point | `essentialRank`, `essentialTruncationPoint` |
| Proposition 3.1: uniform polynomial estimate | `uniform_polynomial_bound` |
| Definition 3.3: rigid condition | `IsCollapse` |
| Proposition 3.4: reduction to a carry-free coefficient | `totalSum_eq_carryFree`, `exists_cosetSum_valued_le` |
| Definition 3.5 / Lemma 3.6: zero gaps and the long-gap criterion | `gapVector`, `typeLT_support_lt_iff_longGaps` |
| Definition 3.7: placing digit patterns on blocks | `placeAt`, `placeList` |
| Lemmas 3.8–3.9: tail clusters and separated placements | `isClustered_tailh_ofWordGap`, `tail_rep_data`, `exists_ray_marker` |
| Lemma 3.11: rigidity at maximum block count | `MarkerData.carry_free`, `hitBlocks_disjoint_of_maximal` |
| Lemma 3.12: invariance under moving blocks | `qtr_arithmeticPlacement`, `exists_aggregate_homogeneity` |
| Definition 3.13: interleavings | `shuffles`, `interleavingPower` |
| Lemma 3.14: interleaving identity | `power_coeff_placeList_eq_interleavingPower` |
| Lemma 3.15: uniform interleaving estimate | `interleavingPower_ne_zero`, `exists_interleaving_coefficient_valuation` |
| Lemma 3.16: bounded separated coefficient | `exists_top_ray_coeff` |
| Theorem 4.1: finite-rank exclusion | `typeLT_support_le_omega0_of_lt_omega0_pow_omega0` |

The formal polynomial estimate also allows nonmonic polynomials over the
unramified integral coefficient ring, with an additional term for the additive
valuation of the leading coefficient. The monic estimate of Proposition 3.1 is
its specialization. Coefficient calculations use multiplicative valuations in
ramified fields, normalized so that the chosen `T`-th root of `p` has value
`ofAdd (-1)`; the final estimates use the additive normalization `v_p(p) = 1`.

## Source organization

| Module or directory | Role |
| --- | --- |
| [MainResults](PAdicOrderType/MainResults.lean) | The seven main declarations: Theorems A–D |
| [ShadowMap](PAdicOrderType/ShadowMap.lean) | Shadow homeomorphism and completed algebraic closures (Section 2.3) |
| [OrderType](PAdicOrderType/OrderType) | Essential rank, essential cutoff, finite-rank exclusion, and support bounds (Lemma 2.12, Definition 2.13, Proposition 3.1, Section 4.1) |
| [Digits](PAdicOrderType/Digits) | Digit vectors, QTR, zero gaps, tail representatives, and separated blocks (Sections 2.2, 3.2 and 3.3) |
| [Coefficients](PAdicOrderType/Coefficients) | Ramified fields, Hahn lifts, coset sums, and carry-free coefficient estimates (Sections 3.1, 3.3 and 3.4) |
| [Interleaving](PAdicOrderType/Interleaving) | Word interleavings, nonvanishing, polynomial certificates, and valuation bounds (Sections 3.3 and 3.4) |
| [Puiseux](PAdicOrderType/Puiseux) | Strict Puiseux field, Krasner approximation, and finite-coefficient Laurent series (Propositions 4.3 and 4.4) |
| [References.HyperAlgebraic](PAdicOrderType/References/HyperAlgebraic.lean) | Finite coefficient range of algebraic p-adic Hahn series |

As described in Remark 1.2 of the paper, part of the formalization of the
authors' earlier work *p-adic Hahn series with sparse support* is copied and
merged into the local library. The original formalization is available at
<https://github.com/YijunYuan/FormalizedSparse/tree/4.33.0>.

## Build and use

The project pins Lean `v4.33.0` in [lean-toolchain](lean-toolchain). Its direct
dependencies are Mathlib, at commit `db584cd`, and `TrustworthyKedlaya`, which
supplies the Hahn-field infrastructure and the formalized results of Kedlaya used
in the paper: Theorem 2.6, Theorem 2.8, and Proposition 2.11 (Remark 1.1).
Versions are specified in [lakefile.toml](lakefile.toml) and resolved in
[lake-manifest.json](lake-manifest.json).

With the `elan` toolchain manager installed, run from the repository root:

```sh
lake build
```

The default build checks the library, [Challenge](Challenge.lean), and
[TargetsCheck](TargetsCheck.lean). The challenge holds the baseline theorem
statements; the target-check module imports the public results.
[comparator.json](comparator.json) selects the seven statements for
[Lean comparator](https://github.com/leanprover/comparator) and permits only
`propext`, `Classical.choice`, and `Quot.sound`.

To use the main results:

```lean
import PAdicOrderType.MainResults

open PAdicOrderType

#check typeLT_support_le_omega0_or_eq_omega0_pow_omega0
#check typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range
#check bialgebraic_tfae
```

Use `import PAdicOrderType` to include the shadow homeomorphism and completed
algebraic-closure results as well.

Released under the [Apache License 2.0](LICENSE).
