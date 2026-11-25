# Review of the physical weighted parity-count application

## Review result and verification status

**Source/API review: PASS, with no blocker identified.** This review covers the eight modules listed below as one application: actual physical edge-product counts, their ordered transfer identity, uniform finite relative imbalance, and both ratio limits for arbitrary length-dependent shared fields satisfying common positive lower and finite upper bounds on actual edges eventually.

The coordinating AI agent completed a full read of all eight sources. Separate nonauthor AI-agent reviews covered the generic weighted transfer, physical encoding, count formula, positivity, symmetry, bounds, and final compositions. These are reviews within the same research project. The development and recorded source reviews were performed by AI agents under a broad human research objective; they do not establish outside mathematical acceptance, independent adoption, human peer review, or literature-wide priority.

The isolated **producer checks** used Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with warnings treated as errors. Their actual recorded outputs contain exactly **44 named declaration audits**, distributed as `6 + 11 + 4 + 2 + 5 + 14 + 1 + 1`. Every listed declaration reports only `propext`, `Classical.choice`, and `Quot.sound`. This review inspected those producer results; it does not describe them as a fresh integrated replay.

**Ordinary-project integration check: PASS.** On 25 November 2026, the coordinating agent ran the packaged verifier with the pinned Lean 4.19.0 toolchain. The ordinary Lake build and exact audit passed for 101 proof modules and 730 named declarations, using only the permitted standard axioms. The repository snapshot check, six finite regressions, and eight optimized-mode guards also passed. All 93 previous proof sources and the seven reviewed mathematical manuscript sources retained their exact bytes. Source review, isolated producer checks, and this integrated execution are separate evidence.

## Complete source snapshot

The following pins cover all eight new modules. Links are relative to this review's intended location in `formal/reviews/`.

| Module | SHA256 | Audited declarations |
|---|---|---:|
| [WeightedFiniteTransfer](../WeightedFiniteTransfer.lean) | `61a9244a9d35cf89fc2c88309b16a7989cb9a94c1c7efa826263b87a9593c4c8` | 6 |
| [WeightedCylinderEncoding](../WeightedCylinderEncoding.lean) | `fb1c4b1017a4ebedc4ce5f74b2ec20859babb767f24543c79642bf87bd92c533` | 11 |
| [WeightedCountTransfer](../WeightedCountTransfer.lean) | `5c483cc96eba22153f27190e1ce9cdb5c453523276a8b691b2c5438b9c88a86c` | 4 |
| [WeightedCountPositivity](../WeightedCountPositivity.lean) | `0fac8a81e8498ad5fa80c37163ac4eabecc7f09fa00e291fbbb87ee5ee386487` | 2 |
| [WeightedCylinderSymmetry](../WeightedCylinderSymmetry.lean) | `9690a97abd7bc40fa5a2772e9962ab1a070596674bd1b5af9182a81b5d77112c` | 5 |
| [WeightedCylinderBounds](../WeightedCylinderBounds.lean) | `59fb868be968bad877f7ef53223777c7177d265d04b6e773f67acddad14412db` | 14 |
| [WeightedCountImbalance](../WeightedCountImbalance.lean) | `465fb06e6881b3ff7909c82dc1fa330461fa29d556df8c604670ce6453f457d1` | 1 |
| [WeightedCountRatio](../WeightedCountRatio.lean) | `608eb4a6ca34db8dc74de6a3ff75f20a6e66bf83bb256769a007aea46c3f885e` | 1 |

## Counted objects and exact edge ownership

The weighted count uses the existing [unordered Hamiltonian selections](../CountedHamiltonian.lean). For meridian-parity class `p`, it is

$$
Z_p(m,L;w)=\sum_{E\in\mathcal H_p(m,L)}\prod_{e\in E}w(e).
$$

Each `E` is a finite set of unordered physical edges on fixed labelled vertices, with a standard Hamiltonian-cycle realization as a proposition. The witnessing root, traversal, and realization proof add no multiplicity. Each selected physical edge appears once in the product. `weightedParityCount_one` recovers the existing natural parity count, cast to the coefficient semiring, when every physical weight is one.

The generic weighted-path layer sums the existing dependent `LabelledPath` and `Accepted` types. Initial, local, and terminal labels have independent weights, and local weights depend on their step position. The finite sum identity is proved from the recursive path types; the counts are not defined as matrix products. A zero-step path uses equality of its endpoints and has weight one, producing the identity matrix and pairing initial and terminal choices at the same state. Empty label types contribute zero.

For `L = n + 2`, the physical factorization assigns ownership as follows:

| Factor | Owned physical edges |
|---|---|
| Initial factor | Selected vertical edges in column `0`. |
| Local factor at `i`, for `0 ≤ i < n` | Selected horizontal and diagonal edges at source cut `i`, followed by the selected vertical mask in column `i + 1`. |
| Terminal factor | Selected horizontal and diagonal edges at cut `n`, followed by the selected vertical mask in column `n + 1`. |

These factors partition every selected V/H/D edge exactly once. The multiplicative ownership does not redefine the existing frontier parity. The product identities use the already proved physical-edge encoding; the total weighted-sum transport uses the existing [counted equivalence](../CountedTransferEquivalence.lean), not merely an equality of cardinalities.

The accepted-object factorization remains valid for `n = 0`: there are no local matrices, and the two endpoint factors own `V₀` and `H₀/D₀/V₁`. The full actual counted transfer identity is asserted only for `n ≥ 1`, equivalently `L ≥ 3`, exactly the range of the counted bijection. This does not omit the two-column exception by silently assigning it a transfer representation.

## Ordered matrices, bounds, and terminal pairing

`weightedParityCount_eq_ordered_transfer` expresses each actual count as the initial physical vector, then the ordered list of position-dependent local matrices, then the physical terminal vector. The list order is preserved. There is no assumption that distinct matrices commute.

The core flip changes the recorded parity while preserving every physical mask and row index. The label equivalences therefore preserve the local and terminal factors in the same physical cylinder, at the same positions, for the unchanged field `w`. Finite sums give simultaneous matrix symmetry and the precise terminal orientation

$$
g_1(s)=g_0(\operatorname{coreFlip}(s)).
$$

No initial-vector symmetry, field translation invariance, row rotation invariance, or relation between weights at different sites is required. Existential cycle witnesses establish label membership; they are neither counted nor assigned extra weights.

For a common lower bound `epsilon > 0` and real upper bound `M`, all weight assumptions concern actual ambient graph edges. Nonedge values are unrestricted. Each local factor contains at most three masked edge factors per row. The identity value for an unselected edge is handled by `min 1 epsilon` and `max 1 M`, giving

$$
a=\min(1,\epsilon)^{3m}>0,
\qquad
b=2^m\max(1,M)^{3m},
\qquad a\le b.
$$

There are at most `2^m` local labels for any ordered state pair because the only counted local data are vertical row masks. Thus every local matrix is nonnegative, at least `a` on the positive support of the fixed unweighted multiplicity matrix, and at most `b` everywhere. Initial and terminal vectors are nonnegative. All these bounds are uniform in length, position, states, and admissible physical field.

## Uniform finite estimate and varying-family limits

`exists_weightedParityCount_geometric_imbalance` has the required uniform quantifier order: after fixing `m ≥ 3`, `epsilon > 0`, and `M`, it chooses `N ≥ 2` and `0 ≤ rho < 1` **before** quantifying over every `L ≥ 3` and every admissible physical field. It proves

$$
|Z_0(m,L;w)-Z_1(m,L;w)|
\le
\rho^{\lfloor(L-2)/N\rfloor}
\bigl(Z_0(m,L;w)+Z_1(m,L;w)\bigr).
$$

The proof imports the actual core connectivity and same-state returns of lengths two and three. The existing [ordered matrix application](../MatrixContraction/OrderedApplication.lean) then derives positive blocks, retains the actual residual suffix, and supplies the finite contraction. The final proof rewrites both endpoints using the same actual ordered transfer identity. Its factor-list length is exactly `L - 2`. The constants remain existential and are not numerically evaluated. The finite estimate permits zero totals and does not assume positive counts at all short widths.

`weighted_parity_ratio_limits` accepts an arbitrary dependent family

```lean
w : ∀ L : ℕ, Sym2 (Vertex m L) → ℝ
```

with the same `epsilon` and `M` required to bound actual edges **only eventually**. Fields at different lengths need not agree on any common subcylinder. The theorem proves that both weighted counts are eventually strictly positive and that both ratios tend to one.

Positivity uses the frozen [unweighted positivity conclusions](../TriangularCountRatio.lean) and `weightedParityCount_pos_iff`. The latter holds at every width: each selected product is positive when its actual edge weights are positive, so the finite sum is positive exactly when the existing parity-selection subtype is nonempty. This is not circular and does not assume positive weighted counts as an input.

One tail threshold combines positive total with the finite imbalance bound. A finite shift applies the existing scalar ratio theorem, exact floor-count growth sends the error to zero, and the shift is removed at the filter level. Inverse continuity at the nonzero limit one gives the reciprocal orientation. Early zero counts or fields outside the eventual bounds do not affect either limit.

## Adversarial scope checks

The following written checks clarify the hypotheses; they are not additional
Lean declarations in this extension. Every Hamiltonian selection has $mL$
edges, so a constant physical field $c$ multiplies its entire parity count by
$c^{mL}$. If one parity class used the constant field two and the other used
one, their ratio would acquire the factor $2^{mL}$ even though both fields
lie in the same fixed interval $[1,2]$. The shared-field hypothesis is essential.

Mere strict positivity also permits one parity to dominate. At every sufficiently
large $L$, choose a Hamiltonian selection $E_L$ in that parity. Give its edges
weight one and every other edge weight $\delta_L=2^{-(3m+1)L}$. Any distinct
Hamiltonian selection uses an edge outside $E_L$, because both sets have
exactly $mL$ edges, so its product is at most $\delta_L$. There are at most
$2^{3mL}$ selections: the physical graph has at most $3mL$ edges. The chosen
parity count is therefore at least one, while the opposite count is at most
$2^{-L}$. A common upper bound alone does not give the ratio limit.

Rescaling every edge by $\delta_L^{-1}$ leaves the within-width parity ratio
unchanged and yields a field with common lower bound one but no common
finite upper bound. Thus a common lower bound alone also does not suffice.
More generally, a positive common rescaling at each length is harmless since
all Hamiltonian selections have equal cardinality. The theorem's absolute
bounds are sufficient; no claim that they are necessary for each individual
family is made.

## Limits of this review and result

The nonauthor review of the generic path layer checked zero-step equality, positional shifts, the observer product, and the ordered finite-sum identity. The physical-encoding review checked edge ownership, exact finite-sum transport, unit weights, and the `n = 0` versus `n ≥ 1` distinction. The matrix and separate nonauthor reviews checked fixed-position symmetry, uniform bounds and quantifiers, terminal orientation, eventual positivity, finite-shift removal, and both ratio orientations. The coordinating agent's full read connected all eight sources to the existing concrete counting and matrix interfaces. These bounded source reviews supplement the producer checks and the integrated execution recorded above; the source reviewers did not independently replay the complete build.

The conclusions concern the existing physical edge-product counts in the **combinatorial meridian-parity classes** for `m ≥ 3`. They do not establish the annular topological identification, a circumference-two multigraph theorem, an absolute exponential expansion, or a uniform statement over varying circumferences or fields lacking the shared lower and upper bounds in the theorem. No square-cylinder extension is supplied by these modules. The Lean kernel and pinned dependencies remain part of the trusted checking environment.
