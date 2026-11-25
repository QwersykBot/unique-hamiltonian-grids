# Review of physical observation bounds

## Result and verification scope

**Source/API review: PASS.** This review covers ten modules that connect the existing physical weighted parity theorem to independent edge-report likelihoods and exact exterior observations. It also covers the normalization needed to compare the two observation distributions.

The coordinating AI agent read all ten complete sources and the actual producer receipts. Separate nonauthor AI agents reviewed each proof layer and the final compositions. The exterior bridge received a further full read from a reviewer who authored the noise and canonical-code layers but none of the five exterior bridge modules. The normalized exterior composition was reviewed by the author of the imported generic finite-TV lemma; that review is independent of the composition, not of its imported lemma. The generic finite-TV lemma itself received separate nonauthor review.

The isolated producer checks used Lean 4.19.0, compiler commit `6caaee842e94`, and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with warnings treated as errors. Their successful outputs contain exactly 63 new named audits, using only subsets of `propext`, `Classical.choice`, and `Quot.sound`. The code type and some geometry predicates have smaller or empty dependencies. Source review and inspection of producer receipts are distinct from a fresh build of the combined project.

The ordinary project gate is `python3 formal/verify.py` from the repository root. Its inventory now requires 111 proof modules and 793 exact named audits. The build, dependency pins, manifest identity, forbidden-token check, and exact-audit enforcement are unchanged; only the module/declaration inventories and scope messages were extended. The machine-readable `formal/verification.json` produced by an execution records its actual result. This source-review report does not substitute for that execution receipt.

**Combined project execution: PASS on 25 November 2026.** The ordinary Lake build and all 793 exact audits passed with warnings treated as errors. This execution used a warm project cache and pinned dependency checkouts mounted read-only. The six existing finite regressions and eight optimized-mode guards also passed. Two subsequent README clarifications made the existing length and activity hypotheses explicit; the final manifest and source inventory were checked again without changing any proof source or gate behavior.

All 101 previously published proof sources and all seven reviewed mathematical manuscript sources retain their exact bytes. All ten new proof sources are byte-identical to their frozen prototypes.

## Source snapshot

| Module | SHA256 | New audits |
|---|---|---:|
| [NoisyCylinderLikelihood](../NoisyCylinderLikelihood.lean) | `ce7213fb57f11d794d5e64924278318da29a1cb01ca3ab2cfba0e5636d29ed9f` | 10 |
| [FiniteParityObservation](../FiniteParityObservation.lean) | `95ae0f4d2076386c84e14f035156415a4cce3d7ad9f2b5e010f01ca1e89f2ed1` | 1 |
| [NoisyParityObservation](../NoisyParityObservation.lean) | `2985c325ae383fc93b8335a31243097c0fc6297a4594805ac5eca569f2956df9` | 3 |
| [ExteriorGeometry](../ExteriorGeometry.lean) | `e6950cce367814084ff5677fea83c250f1d28acda3d0bdbd3147a8cb7de92702` | 18 |
| [ExteriorEncoding](../ExteriorEncoding.lean) | `7ea1869decc322a20051e3e04872b58cce3b396e9307e9f0154e4429cba31a9d` | 7 |
| [ExteriorSymmetry](../ExteriorSymmetry.lean) | `8ee74ea1c5c73297fcdae44a643598884e7c7e8faeaab187de1b76138c43e1fb` | 12 |
| [WindowProduct](../WindowProduct.lean) | `b3844d5dfbaf097b922fcda88b257324c31f9ae71b50c871f10be2f62a6f3c42` | 1 |
| [ExteriorCountImbalance](../ExteriorCountImbalance.lean) | `1c3da8344377daf84389ae7b2231d1043c09a71d3e1db60df5ed662ef34b5555` | 1 |
| [CanonicalExteriorObservation](../CanonicalExteriorObservation.lean) | `7e9d9faf5b1ace2c43187611ee30defee10ca154bffe82b160ef930b06902940` | 8 |
| [ExteriorParityObservation](../ExteriorParityObservation.lean) | `9782ab87b363e4abc85175de5c8fb0e712b9638796a5577cb508bd63be69930d` | 2 |

## Physical likelihood and normalization

The report likelihood is a product over the actual unordered edge finset. It uses the selected-edge likelihood on selected edges and the absent-edge likelihood on all other actual edges. Thus absent observations are retained, each physical edge is charged once, and no cycle root, traversal, or realization witness adds multiplicity.

When every absent-edge likelihood is positive, the report mass factors as its common absent-edge product times the original physical weighted count with effective activity `w * (q1 / q0)`. The common factor may be arbitrarily small; the theorem requires fixed positive lower and finite upper bounds on the likelihood ratios, not a uniform lower bound on the absent-edge factors themselves. The constants precede length, the common prior field, and all likelihood fields.

The fixed-report posterior uses the pooled physical prior. Its denominator is the positive sum of the two report masses. An artificially equal prior on the two parity classes would introduce their separate partition functions and is not silently substituted. The finite-report TV theorem uses a finite report alphabet chosen after the constants and separately normalizes the two families of nonnegative masses. It proves positive class totals from positive pooled mass once a full contraction block is present.

The sharp finite-TV lemma allows unequal class totals and zero-mass atoms. From a common pointwise relative imbalance below one, it derives both positive totals and TV at most the same imbalance constant. Its proof treats zero imbalance separately and otherwise bounds the cross-multiplied differences before division by positive totals. No probability-measure interface or likelihood normalization is assumed by this algebraic lemma.

Interpreting the report families as a particular observation channel additionally requires its actual conditionally independent likelihoods and a complete normalized alphabet. The [observation note](../observations.md) states this distinction and explains fixed binary noise, the equal-prior testing implication, and counterexamples to claims about vanishing or correlated noise. Those interpretations are written consequences, not additional channel-normalization declarations in Lean.

## Exact physical exterior bridge

For `L = n + 2`, local slot `i` owns `H_i`, `D_i`, and `V_(i+1)`. Slots in `[a,b)` are free. The initial `V_0` and terminal `H_n`, `D_n`, `V_(n+1)` remain exterior. The positive-column guard in the vertical-edge predicate prevents truncated natural subtraction from misclassifying `V_0`. The condition `b <= n` protects terminal ownership.

The exterior event fixes both selected and absent edges. Its complete proof chain is physical edge membership, exact owned-mask constraints, product of the zero-one filters, physical selected-edge product times the event indicator, finite-sum transport along the counted equivalence, and finally the ordered matrix product. Equality of cardinalities alone is never used to justify transport of weighted sums.

The core flip preserves masks and positions, so the same exterior prescription and field work for both parity classes. The free-slot matrix is exactly the existing unfiltered weighted matrix. Outside that interval the matrices and boundary vectors may contain zeros; no positive-mass assumption is needed for the unnormalized inequality. The window theorem absorbs the prefix and suffix without changing the order of matrices. Equivariance of the suffix gives the correct paired terminal orientation.

The final bound uses the proved actual core connectivity and common returns of lengths two and three. Its constants precede `n`, `a`, `b`, the prescription, and the field. Empty free intervals yield exponent zero; impossible prescriptions yield zero masses. Bounds are imposed on all actual edges, not merely the free band. The statement covers one interval at fixed circumference and supplies existential, unevaluated constants.

## Canonical exterior laws

A total geometry carries ignored free-edge flags and therefore gives redundant descriptions of an observation. `CanonicalExteriorCode` chooses their false representative. False is only a placeholder: the physical agreement predicate still ignores those free edges, including selected ones.

Every finite edge set has exactly one canonical code. All codes remain in the finite sum; impossible Hamiltonian observations contribute zero. The exact partition identity shows that canonical exterior masses sum to the original `weightedParityCount`. This identity needs no interval-validity or weight-positivity premise.

The normalized exterior theorem uses that identity twice: to establish pooled observation positivity from the original pooled physical count, and to rewrite both derived class totals and every TV denominator back to the original weighted counts. It assumes positive pooled count and `N <= b - a`; it concludes positivity of both class totals. Individual prescriptions need not be realizable. The last condition makes the contraction exponent positive and the imbalance strictly less than one, including the case `rho = 0`.

## Limits

These are AI-authored proofs and internal nonauthor reviews. They do not establish human peer review, outside adoption, a new general contraction mechanism, or literature-wide priority. The contribution reviewed here is the exact physical connection and its normalization within this cylinder model. The Lean kernel and pinned dependencies remain trusted. Annular topological classification, circumference two, varying-circumference rates, multiple free bands, and general correlated observation channels are outside these formal statements.
