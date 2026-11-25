# Checked triangular-cylinder parity balance

This Lean/mathlib project proves the concrete combinatorial ratio limit
underlying the [triangular-cylinder argument](../triangular_cylinder_asymptotics.md).
For a fixed circumference $m\ge3$, let $C_p(m,L)$ count the undirected
Hamiltonian edge selections on the consistently triangulated cylinder with
$L$ columns and wrap-edge parity $p\in\{0,1\}$. Then both counts are positive
for all sufficiently large $L$, and

$$
\frac{C_1(m,L)}{C_0(m,L)}\longrightarrow1,
\qquad
\frac{C_0(m,L)}{C_1(m,L)}\longrightarrow1.
$$

The main limit results are in [TriangularCountRatio](TriangularCountRatio.lean).
Their hypotheses are only the fixed natural circumference and $m\ge3$.
The exact counted correspondence, actual-state symmetry, connectivity,
and common return paths are all proved by the project. Hamiltonian cycles
are counted as unordered edge sets on fixed labelled vertices, with no
root or traversal multiplicity.

The [physical edge-product extension](#physical-edge-product-weights) proves
uniform geometric balance for arbitrary shared edge-weight fields with fixed
positive lower and upper bounds. The field may vary with row, column, edge
direction, and length; no translation symmetry is required.

The [physical observation extension](observations.md) applies this balance
to independent noisy reports of the edges and to exact observations outside
one unobserved band. It proves bounds for the actual physical masses and
their normalized distributions, including the required positivity of class
totals. The constants are existential and depend on the fixed circumference
and activity or likelihood-ratio bounds.

The formal results concern combinatorial meridian parity. Its identification
with annular contractibility, the circumference-two multigraph convention,
and absolute spectral asymptotics remain separate. The square-cylinder and
rectangular-grid results have not been formalized by this project.

The project uses Lean 4.19.0, compiler commit `6caaee842e94`, and Mathlib
commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. These are fixed historical
dependencies, recorded in `lean-toolchain` and `lake-manifest.json`.
The mathematical sources and their earlier review record are the publication
at commit [`79b692d`](https://github.com/QwersykBot/unique-hamiltonian-grids/tree/79b692d1b5127d440d91c016b15adc9ffa839590).

## Reproduce

With Python 3.10 or later and the pinned Lean/Lake toolchain available:

```sh
cd formal
python3 verify.py --fetch-cache
```

The optional flag fetches Mathlib's official compiled cache for the imports
used here. Subsequent checks can omit it. An isolated installation can be
selected with `--lake /absolute/path/to/lake`.

The verifier checks the repository manifest, local source inventory,
dependency commits and tracked-source cleanliness. It builds the ordinary
Lake project with warnings treated as errors and recompiles
[`ProofAudit.lean`](ProofAudit.lean), requiring its exact named declaration set.
Every report must use only a subset of `propext`, `Classical.choice`, and
`Quot.sound`. The local sources contain no proof placeholders, custom axioms,
unsafe declarations, or native decision procedures. A machine-readable local
receipt is written to `verification.json`.

The standard Lean commands are also available:

```sh
lake build
lake env lean -DwarningAsError=true ProofAudit.lean
```

These commands check the formal declarations. The Python verifier adds
snapshot, toolchain, dependency, and exact-audit checks. Mathlib's compiled
dependencies and the Lean kernel are part of the trusted environment;
this is not an independent-kernel check or human peer review.

## Concrete graph results

`TriangularCylinder.graph` has vertices `Fin m × Fin L`, for `m ≥ 3`.
Its edges are cyclic vertical steps, ordinary horizontal steps, and
diagonals that advance one row and one column. The graph is undirected,
while the diagonal orientation is consistent around the cylinder.
Hamiltonicity uses Mathlib's standard `Walk.IsHamiltonianCycle`.

| Module | Checked result |
|---|---|
| [CylinderSplice](CylinderSplice.lean) | Joins disjoint spanning paths by two seams; gives the resulting Hamiltonian cycle, exact edge set, and additive edge-weight identity. |
| [TriangularCylinder](TriangularCylinder.lean) | Constructs the two column embeddings and the concrete splice on the intended graph. |
| [TriangularParity](TriangularParity.lean) | Proves that the concrete splice adds the two meridian parities modulo two. |
| [EnumeratedWalk](EnumeratedWalk.lean) | Turns a bijective finite vertex enumeration with actual consecutive and closing edges into a standard Hamiltonian cycle. |
| [MeridianClassifier](MeridianClassifier.lean) | Classifies ordinary row successors and the last-to-first wrap, including its exact edge weight. |
| [AuxiliaryCycle](AuxiliaryCycle.lean) | Constructs the three-column auxiliary for every `m ≥ 3`, with parity one and the two exact missing boundary gaps. |
| [EdgeCoboundary](EdgeCoboundary.lean) | Proves endpoint cancellation for mod-two changes in edge weights, hence invariance on every closed walk. |
| [RowRotation](RowRotation.lean) | Proves row-shift parity invariance and produces an auxiliary selecting any prescribed left and right cyclic gaps. |

The parity is the sum, modulo two, of the indicators of edges crossing the
fixed last-to-first row meridian. Rotation invariance is derived by local
edge identities and cancellation of vertex potentials. No topological
classification is assumed or established by these declarations.

`exists_aligned_three_column_auxiliary` quantifies over the actual
circumference and both prescribed gaps. It supplies a Hamiltonian cycle
with parity one containing both selected boundary edges.
[SelectedEdgePresentation](SelectedEdgePresentation.lean) derives an
edge-first presentation in either requested orientation while preserving
the whole unordered edge list up to permutation.
[SelectedCylinderSplice](SelectedCylinderSplice.lean) therefore joins
arbitrarily rooted input cycles directly from selected-edge membership,
with the exact original-edge-set replacement and parity addition.

The [two-column](TwoColumnWitness.lean) and
[three-column](ThreeColumnWitness.lean) parity-zero witnesses are explicit
Hamiltonian cycles for every `m ≥ 3`. Their respective
[sole-cut](TwoColumnWitnessCut.lean) and
[last-cut](ThreeColumnWitnessCut.lean) results prove that the crossings
are exactly the first- and last-row horizontals. Each processed prefix is
exactly one spanning path. These are the graph facts needed for the
intended common-state returns; no transfer-return statement is asserted
by those files.

## Undirected counted objects and frontier replacement

[CountedHamiltonian](CountedHamiltonian.lean) defines a selection as a
finite set of unordered edges having a standard Hamiltonian-cycle
realization. The witnessing root and traversal are existential
propositions, so they are not additional counted data. The vertex labels
remain fixed. [GenericEdgeWeights](GenericEdgeWeights.lean) proves that
additive trail weights depend only on the selected edges; the concrete
parity is consequently independent of the cycle presentation.

[SelectedCharacterization](SelectedCharacterization.lean) and
[SelectedIff](SelectedIff.lean) prove that an admissible edge selection is
Hamiltonian exactly when its spanning selected graph is connected and
has two neighbors at every vertex. The reverse direction uses
[ConnectedTwoRegular](ConnectedTwoRegular.lean), a small standard-Hamiltonian
interface to Mathlib's existing component-spanning cycle theorem.
Admissibility explicitly excludes diagonal pairs and ambient nonedges;
the recovered Hamiltonian walk uses the entire original selected set.

[PhysicalEdges](PhysicalEdges.lean) proves that the disjoint vertical,
horizontal, and consistently oriented diagonal identifiers correspond
bijectively to the actual graph edges, for `m ≥ 3` and every column count.
This statement does not introduce a multigraph convention at `m = 2`.

[ColumnGeometry](ColumnGeometry.lean) encodes arbitrary selections by
Boolean V/H/D masks. [ColumnHamiltonian](ColumnHamiltonian.lean) restricts
that exact encoding to connected, two-regular selections and proves an
equivalence with the counted Hamiltonian edge sets, including equality of
each parity count. [ColumnWeights](ColumnWeights.lean) decomposes additive
weights into the physical column and cut choices. For meridian parity,
only the last-row vertical and diagonal bits contribute.

The frontier connectivity interfaces are separate from the counting types:

| Module | Checked result |
|---|---|
| [FrontierSubstitution](FrontierSubstitution.lean) | Replacing an attached prefix by another with the same boundary reachability preserves connectedness under every fixed suffix. |
| [FrontierAttachment](FrontierAttachment.lean) | Actual glued connectedness forces prefix attachment when the boundary is nonempty; a stronger version allows any boundary or suffix vertex. |
| [FrontierCongruence](FrontierCongruence.lean) | The same replacement preserves every suffix reachability query. A canonical boundary graph compresses this relation for connectivity computations. |
| [ColumnCut](ColumnCut.lean) | Splits an actual selected cylinder graph at its entire last processed column. The prefix owns boundary-column edges, and the canonical glue is isomorphic to the original graph. |

The concrete cut theorem derives the absence of long edges from the actual
cylinder adjacency. It then derives the prefix attachment invariant from
the original graph's connectedness. The compressed relation edges in
`FrontierCongruence` carry only connectivity information; their degrees
are not physical selected degrees.

[ColumnFragments](ColumnFragments.lean) normalizes prefixes and suffixes
independently of the lengths of their original completions, then proves
that their transported join has legal cylinder edges. The
[generalized degree sum](FrontierDegreesGeneral.lean) allows the prefix
to own boundary-column verticals while the suffix owns no boundary edges.
[ColumnCutOutgoing](ColumnCutOutgoing.lean) identifies each boundary
vertex's suffix neighbors as its selected horizontal and diagonal edges.
[ColumnBoundaryDegree](ColumnBoundaryDegree.lean) uses these facts to prove
that matching outgoing masks preserve degree two when fragments are mixed.
These interfaces separate ambient validity, connectivity, and degree.

[PrefixReplacement](PrefixReplacement.lean) composes these results into a
standard Hamiltonian realization of the mixed graph, with exactly its
constructed edge set. Connectedness and degree two of the mixed graph are
derived from the original selections and equality of their H/D and reach
fields. [FragmentRecovery](FragmentRecovery.lean) proves exact recovery of
both input fragments. [ColumnStepConnectivity](ColumnStepConnectivity.lean)
and [ProcessedPrefix](ProcessedPrefix.lean) prove that old H/D masks, the
old boundary relation, and one new V mask determine the next relation.
Attachment is derived from actual connected completions; a processed prefix
is allowed to have several components.

## Concrete boundary data and the two-column exception

[BoundaryState](BoundaryState.lean) gives a finite raw state at the complete
last processed column. It records two outgoing physical masks, the Boolean
reachability relation inside the actual processed prefix, and a mod-two
parity. The parity charges every selected physical edge whose source
column has been processed, including outgoing diagonals. Those outgoing
edges are absent from the prefix connectivity graph until their next
column is processed. The two conventions are proved explicitly.

Actual occurrence separately requires a standard Hamiltonian cycle in the
intended ambient graph. The raw parity flip is involutive and has no fixed
points. [CoreStateFlip](CoreStateFlip.lean), described below, proves closure
of the nonfull actual core under this flip.

[CommonWitnessState](CommonWitnessState.lean) computes the entire state of
the two- and three-column zero-parity witnesses: only the first- and
last-row horizontal crossings are selected, every pair of boundary rows
is connected inside the prefix, and parity is zero. It proves literal
equality of the two states and actual occurrence for every `m ≥ 3`.
[CommonReturns](CommonReturns.lean) uses these witnesses to prove the
common-state transfer returns of lengths two and three.

The [two-column zigzag](ZigzagException.lean) selects all horizontal and
diagonal edges and no vertical edges. Its actual selected graph is
connected and two-regular, and its meridian parity is one.
[ExceptionalState](ExceptionalState.lean) derives its raw state directly:
both outgoing masks are full, prefix reachability is equality of rows,
and assigned parity is one.

[FullCrossing](FullCrossing.lean) proves that a connected two-regular
selected graph containing every H/D edge at any one physical cut must
have exactly two columns. The proof embeds the actual zigzag cycle and
uses [CycleSaturation](CycleSaturation.lean) to show that this same cycle
must span the whole graph. Thus no Hamiltonian selection on at least
three columns has a full H/D cut.
[BoundaryVertical](BoundaryVertical.lean) independently derives a selected
vertical edge at each end of every such longer cylinder.

[EdgeReplacementReachability](EdgeReplacementReachability.lean) proves
that replacing an existing edge by a connected disjoint gadget and two
seams preserves the entire reachability relation on old vertices.
[SpliceSelectedGraph](SpliceSelectedGraph.lean) identifies the concrete
selected-edge splice with this replacement graph. Its coordinate,
restriction, and cycle-edge-deletion helpers justify the application inside
every old prefix, including cut zero.
[SplicePrefixReachability](SplicePrefixReachability.lean) preserves every old
prefix reachability query for the same constructed Hamiltonian splice, and
[SpliceStateFields](SpliceStateFields.lean) preserves its outgoing H/D and
reach fields. [SpliceAssignedParity](SpliceAssignedParity.lean) proves that
the assigned parity at every shifted old cut changes by the whole-cycle
parity increment. The physical V/D tail strictly beyond the cut is unchanged;
the outgoing D at the cut remains charged to the prefix.
[StateEndVertical](StateEndVertical.lean) obtains both selected end verticals
from a nonfull actual state, including a two-column witness.

## Generic ordered-matrix theorem

The main algebraic result is
`CylinderMatrixContraction.ordered_factor_family_ratio_tendsto_one` in
[OrderedApplication.lean](MatrixContraction/OrderedApplication.lean).

Let the index set be finite. Fix a nonnegative reference matrix `T`, a
state `v`, an involutive permutation `u`, and constants `0 < a ≤ b`.
Assume every ordered pair of states is joined by a positive entry of some
power of `T`, and that `(T²)(v,v)` and `(T³)(v,v)` are positive.

For every index `n`, let `F(n)` be an ordered list of matrices, with product
`P(n)`, and let `f(n), g(n)` be nonnegative boundary vectors. Each factor
must be nonnegative, at least `a` on the positive support of `T`, at most
`b` everywhere, and invariant under simultaneous application of `u` to
its two indices. Define

\[
Z_0(n)=f(n)\,P(n)\,g(n),\qquad
Z_1(n)=f(n)\,P(n)\,(g(n)\circ u).
\]

If `Z₀(n)+Z₁(n)>0` for every index and the original list lengths tend to
infinity, the theorem proves

\[
\frac{Z_0(n)}{Z_1(n)}\longrightarrow1.
\]

The factors and boundaries may vary with `n`. The factors need not commute
with one another, and no common growth constant is asserted.

The companion finite theorem derives constants `N ≥ 2` and `0 ≤ ρ < 1`,
uniform over all permitted lists and boundaries, such that

\[
|Z_0-Z_1|\le
\rho^{\lfloor |F|/N\rfloor}(Z_0+Z_1).
\]

The proof constructs the consecutive chunks, retains the actual right-hand
suffix, and derives both positive block bounds and divergence of the
block count. Neither block positivity nor a supplied decomposition is an
assumption of the final theorem. The finite estimate includes empty
factor lists and zero totals. The ratio theorem requires positive totals;
individual denominator positivity follows eventually from the estimate.
The constants are existential; no specific `N = 2 card(ι)` bound is proved
in this source.

| Module | Role |
|---|---|
| [Basic](MatrixContraction/Basic.lean) | Odd-vector cancellation and contraction through ordered positive blocks. |
| [Limits](MatrixContraction/Limits.lean) | Converts geometric imbalance into probability and ratio limits. |
| [PositiveBlocks](MatrixContraction/PositiveBlocks.lean) | Derives positive blocks from support connectivity, common-state returns of lengths two and three, and uniform factor bounds. |
| [OrderedApplication](MatrixContraction/OrderedApplication.lean) | Constructs the partition of each original factor list and composes the full generic result. |

## Exact labelled-path counts and their ratio

[FiniteTransfer](FiniteTransfer.lean) defines actual finite labelled paths.
A zero-step path has one equality witness when its endpoints coincide.
A successor path chooses its next state, one local label, and a shorter
path. Accepted objects additionally choose initial and terminal labels.
Sigma/product cardinality identities prove that their count is exactly
`f · M^n · g`, where `M(i,j)` counts the local labels from `i` to `j`.
The real-valued formula is an exact cast of that natural-number count.

[AcceptedRatio](AcceptedRatio.lean) applies the generic algebra to these
finite objects. Its hypotheses are paths between every pair of states,
returns of lengths two and three at the same state, nonempty total initial
and terminal choices, and an involutive state permutation with explicit
local-label and terminal-label equivalences. It proves that the two
accepted counts have ratio tending to one and that the denominator is
strictly positive eventually. It derives the positive-power threshold
and the entry bounds, and removes a finite shift to allow zero counts at
short lengths. Initial labels need no permutation symmetry.

This theorem counts its dependent accepted-object type. Identifying that
type with the intended Hamiltonian edge selections is established below;
no root or direction multiplicity is silently divided out.

## Exact triangular-cylinder counted correspondence

[ActualTransfer](ActualTransfer.lean) defines the finite core as actual
occurring raw states whose outgoing H/D masks are not both full. Initial,
local, and terminal labels contain only a physical vertical mask as data.
Their properties require occurrence in an actual Hamiltonian cycle; local
source and target cuts must occur consecutively in the same witness. The
witness's width, root, and traversal remain propositions, so they add no
counting multiplicity. Finiteness is classical and does not assert an
effective enumeration algorithm.

[CycleAccepted](CycleAccepted.lean) encodes the actual ordered cut sequence
of a Hamiltonian cycle. [AcceptedReconstruction](AcceptedReconstruction.lean)
defines reconstruction as a physical unordered edge finset and proves exact
recovery for the canonical encoding of an existing counted selection.
[AcceptedGraph](AcceptedGraph.lean) recovers all V/H/D masks for arbitrary
accepted data, and [AcceptedExtensionality](AcceptedExtensionality.lean)
shows that the full cut-state sequence and all V masks distinguish the
entire accepted object.

[BoundaryParity](BoundaryParity.lean) identifies the existing assigned-ID
sum with the physical V/D charges through each source column.
[BoundaryParityUpdates](BoundaryParityUpdates.lean) derives the initial,
consecutive, and terminal identities. The first cut charges its V and
outgoing D bits; a step adds the new V and new outgoing D bits; after the
last cut only the final-column V remains.
[AcceptedParity](AcceptedParity.lean) proves that every accepted object's
reconstructed physical edge sum has its stated terminal parity, without
assuming reconstructed connectedness.

[AcceptedRealization](AcceptedRealization.lean) proves that **every accepted
object has a standard Hamiltonian realization selecting exactly its
reconstructed edges**. The induction keeps a genuine Hamiltonian completion
of each processed prefix. The initial and local witnesses provide these
completions through exact prefix replacement. The terminal witness then
closes the graph at the requested width. [CompletionTransport](CompletionTransport.lean)
tracks the exact fragments when the cut advances. This realization theorem
also covers zero-step accepted objects.

[AcceptedStateRecovery](AcceptedStateRecovery.lean) recovers the recorded
reach fields once the reconstructed graph is connected. That premise is
supplied by the realization theorem.
[AcceptedUniqueness](AcceptedUniqueness.lean) combines all state fields and
proves the full right-inverse identity.
[CountedTransferEquivalence](CountedTransferEquivalence.lean) consequently
provides the mutual inverse maps and exact count formulas:

```lean
countedTransferEquiv hm hn p :
  ParitySelection hm p (n + 2) ≃ AcceptedObject hm p n

parityCount_eq_card_accepted hm hn p :
  TriangularCylinder.parityCount m (n + 2) hm p =
    Fintype.card (AcceptedObject hm p n)
```

Here `hm : 3 ≤ m` and `hn : 1 ≤ n`; the cylinder has `n + 2 ≥ 3` columns.
The source is exactly the existing counted selection type restricted by its
existing meridian parity. The two-column full-crossing exception is excluded
from the core, so the bijection is deliberately not asserted at `n = 0`.
The same module proves the natural and real transfer identities
`parityCount = f · M^n · g` in this range.

[TransferWitnesses](TransferWitnesses.lean) obtains nonempty initial and
parity-zero terminal choices from the concrete two-column perimeter witness.
[CycleIntervals](CycleIntervals.lean) constructs exact labelled paths
between ordered cuts of one longer actual cycle, with length equal to the
difference of their cut indices. It does not by itself supply common-state
returns or paths between arbitrary core states.

## Concrete symmetry, connectivity, and the ratio limit

[CoreStateFlip](CoreStateFlip.lean) closes the actual core under changing
only its parity bit. It prepends an actual aligned three-column auxiliary
of odd parity to an occurrence witness. The resulting state has unchanged
H/D masks and boundary reachability, and the opposite assigned parity.
The map is an involution on the existing core type.

[CoreLabelFlip](CoreLabelFlip.lean) proves explicit equivalences of the
counted local and terminal label types. For a local label, one actual joined
cycle realizes both flipped states at consecutive shifted cuts. Its physical
V mask is identical to the original label's mask. The terminal construction
also flips the whole-cycle parity. Both equivalences act as the identity on
mask data; their inverse constructions use the involution. No symmetry of
initial labels is needed.

[SpliceLeftState](SpliceLeftState.lean) preserves every old left state when
a cylinder is appended on the right. [CommonReturns](CommonReturns.lean)
self-splices the concrete two- and three-column witnesses, producing actual
paths of lengths two and three at the same `commonCoreState`.
[AuxiliaryParity](AuxiliaryParity.lean) constructs an aligned connector in
either parity class. [CoreConnectivity](CoreConnectivity.lean) uses two
actual splices and a connector matching the source witness's parity to put
any two core states into one Hamiltonian cycle. [StateInterval](StateInterval.lean)
then extracts the finite path between those two cuts of that same cycle.
Original occurrence witnesses may have only two columns; nonfullness gives
the selected end edges needed by the construction.

[TriangularCountRatio](TriangularCountRatio.lean) applies the generic
accepted-path ratio theorem to these concrete data, rewrites the actual
count formula only eventually for `n >= 1`, and removes the `n + 2` column
shift. It proves:

```lean
triangular_parity_ratio_limit (m : ℕ) (hm : 3 ≤ m) :
  (∀ᶠ L in atTop, 0 < parityCount m L hm 1) ∧
    Tendsto (fun L =>
      (parityCount m L hm 0 : ℝ) / (parityCount m L hm 1 : ℝ))
      atTop (𝓝 1)
```

The companion `triangular_parity_ratio_limit_reciprocal` proves the odd-over-
even orientation and eventual positivity of the even count. Its inverse-limit
step uses continuity at the nonzero limit one, allowing arbitrary short-length
zeros. Both conclusions concern the complete sequence of column lengths.

[TriangularCountImbalance](TriangularCountImbalance.lean) further proves
that, for each fixed $m\ge3$, there are an integer $N\ge2$ and a real
$0\le\rho<1$ such that every $L\ge3$ satisfies

$$
|C_0(m,L)-C_1(m,L)|\le
\rho^{\lfloor(L-2)/N\rfloor}\bigl(C_0(m,L)+C_1(m,L)\bigr).
$$

The constants depend on the fixed circumference and are not numerically
evaluated. The inequality uses no division and remains valid if counts
vanish at a short length. It bounds the imbalance relative to the total;
it does not assert that the absolute difference of the counts tends to zero.

## Physical edge-product weights

For a real weight field $w$ on the actual unordered physical edges, define

$$
Z_p(m,L;w)=\sum_{E\in\mathcal H_p(m,L)}\prod_{e\in E}w(e),
$$

where $\mathcal H_p(m,L)$ is the same existing parity subtype of undirected
Hamiltonian edge selections used for $C_p(m,L)$. The two classes use **the
same field** at each length. Roots, traversal directions, and the witnesses
that certify local realizability add no factors or multiplicity.

[WeightedCountImbalance](WeightedCountImbalance.lean) proves the following
uniform statement. Fix $m\ge3$, $\epsilon>0$, and $M\in\mathbb R$. There are
$N\ge2$ and $0\le\rho<1$ such that, for **every** $L\ge3$ and **every** field
satisfying $\epsilon\le w(e)\le M$ on actual graph edges,

$$
|Z_0(m,L;w)-Z_1(m,L;w)|\le
\rho^{\lfloor(L-2)/N\rfloor}\bigl(Z_0(m,L;w)+Z_1(m,L;w)\bigr).
$$

The constants are chosen before the length and weight field. They may depend
on $m,\epsilon,M$ and are not numerically evaluated. No bound is imposed on
nonedges. The field may assign different values to every row, column and
edge direction. The inequality has no denominator and remains meaningful
when both short-length counts vanish.

[WeightedCountRatio](WeightedCountRatio.lean) takes an arbitrary dependent
family `w : ∀ L : ℕ, Sym2 (Vertex m L) → ℝ`, with the same bounds required
only eventually. It proves that both weighted counts are positive eventually
and that both $Z_0/Z_1$ and $Z_1/Z_0$ tend to one. There is no consistency,
stationarity, or probabilistic assumption relating fields at different
lengths. Short initial lengths may violate the weight bounds or have zero
counts.

### Exact encoding and uniform estimates

At width $L=n+2$, the initial factor owns $V_0$; local step $i$ owns the
source cut's $H_i,D_i$ and the next column's $V_{i+1}$; the terminal factor
owns $H_n,D_n,V_{n+1}$. Every selected physical edge is charged exactly once.
The generic weighted path theorem then gives the ordered transfer product
$fM_0M_1\cdots M_{n-1}g_p$. The matrices need not commute.

The core flip preserves each H/D mask and every vertical-label mask. Its
local and terminal factors therefore evaluate the same field at the same
physical positions, even though larger cycles were used to prove label
realizability. The terminal vectors satisfy $g_1(s)=g_0(Js)$; no initial-vector
symmetry is assumed.

Each local label uses at most $3m$ physical factors. Padding unselected edges
by the factor one gives the common entry bounds

$$
a=\min(1,\epsilon)^{3m}>0,\qquad
b=2^m\max(1,M)^{3m}.
$$

The lower bound applies on every positive entry of the fixed unweighted
support. The upper bound uses at most $2^m$ actual vertical-mask labels.
The existing common-return and connectivity proofs give the positive blocks
needed by the ordered contraction theorem. Nonnegative boundary vectors
suffice; their magnitudes need no uniform bound.

| Module | Checked role |
|---|---|
| [WeightedFiniteTransfer](WeightedFiniteTransfer.lean) | Sums actual weighted paths and accepted objects into an ordered matrix product over a commutative semiring, including length zero. |
| [WeightedCylinderEncoding](WeightedCylinderEncoding.lean) | Preserves actual physical edge products and transports finite sums through the counted bijection for $n\ge1$; unit weights recover the original counts at every width. |
| [WeightedCountTransfer](WeightedCountTransfer.lean) | Composes the two identities into the physical ordered transfer formula. |
| [WeightedCountPositivity](WeightedCountPositivity.lean) | Positive physical weights make a weighted count positive exactly when the original unweighted count is positive, at every width. |
| [WeightedCylinderSymmetry](WeightedCylinderSymmetry.lean) | Proves same-position local symmetry and the paired terminal-vector identity. |
| [WeightedCylinderBounds](WeightedCylinderBounds.lean) | Proves the padded physical-factor, label-cardinality, matrix-entry, and boundary nonnegativity estimates. |
| [WeightedCountImbalance](WeightedCountImbalance.lean) | Establishes the uniform finite bound with constants before $L,w$. |
| [WeightedCountRatio](WeightedCountRatio.lean) | Establishes both eventual positive counts and both ratio limits for arbitrary eventually bounded fields. |

The two-column isolated zigzag remains outside the retained core transfer:
the exact weighted count-to-transfer identity requires $n\ge1$, or $L\ge3$.
The product identities on accepted objects at $n=0$ do not include that
additional counted cycle.

Strict positivity alone does not imply the uniform conclusion. A length-dependent
family can assign weight one to a chosen Hamiltonian cycle and decreasing positive
weights to all other edges, forcing its parity to dominate. Likewise,
different fields for the two classes can create an exponential imbalance.
The [weighted application review](reviews/weighted_application.md) records
these scope checks. Common absolute bounds are sufficient; no optimality
claim is made for the quantitative constants or hypotheses.

## Physical observations

The [observation note](observations.md) gives the full statements, interpretation,
and limits of two applications. Both use the original fixed-labelled,
unordered Hamiltonian edge selections and a shared physical edge-product
prior.

For independent reports, the likelihood includes every actual edge, whether
selected or absent. Factoring out the absent-edge likelihood turns each
fixed report into a new physical weight field. Fixed positive lower and
finite upper bounds on the likelihood ratios, together with the fixed
base-activity bounds, give a uniform geometric posterior-parity bound.
A finite-mass theorem also bounds the total variation
between the separately normalized report distributions. Interpreting these
as a specified observation channel requires its actual likelihoods and a
complete normalized report alphabet; this interpretation is distinguished
from the finite algebra in the note.

For exact exterior observations, let $L=n+2$ with $n\ge1$ and $0\le a\le b\le n$.
Local slots $a\le i<b$ leave $H_i,D_i,V_{i+1}$ unobserved; all other edges
have both their selected and absent values prescribed. If $Z_p^\sigma$ is
the physical weighted mass with exterior $\sigma$, the checked bound is

$$
|Z_0^\sigma-Z_1^\sigma|
\le \rho^{\lfloor(b-a)/N\rfloor}(Z_0^\sigma+Z_1^\sigma).
$$

The constants $N\ge2$ and $0\le\rho<1$ are chosen before the length,
interval, prescription, and common field. The theorem permits impossible
prescriptions and zero masses. A canonical code records each physical
exterior exactly once, and its masses sum to the original weighted parity
count. For $N\le b-a$ and positive pooled count, both class totals are
positive and the two normalized exterior laws have total variation at most
$\rho^{\lfloor(b-a)/N\rfloor}$.

| Modules | Checked role |
|---|---|
| [FiniteParityObservation](FiniteParityObservation.lean) | Sharp finite total-variation bound from a pointwise relative-imbalance inequality, including unequal class totals and zero-mass atoms. |
| [NoisyCylinderLikelihood](NoisyCylinderLikelihood.lean), [NoisyParityObservation](NoisyParityObservation.lean) | Exact physical likelihood factorization, uniform report-mass imbalance, pooled-prior posterior bias, and finite report-distribution total variation. |
| [ExteriorGeometry](ExteriorGeometry.lean), [ExteriorEncoding](ExteriorEncoding.lean) | Complete selected-and-absent exterior event, owned-mask filters, and its exact physical weighted transfer formula. |
| [ExteriorSymmetry](ExteriorSymmetry.lean), [WindowProduct](WindowProduct.lean), [ExteriorCountImbalance](ExteriorCountImbalance.lean) | Same-position filtered symmetry and contraction through one unrestricted interval, followed by the physical exterior-count inequality. |
| [CanonicalExteriorObservation](CanonicalExteriorObservation.lean), [ExteriorParityObservation](ExteriorParityObservation.lean) | Unique physical observation codes, exact mass partition, nonnegativity, and normalized total variation with the original class counts as denominators. |

These results concern fixed circumference and the stated common bounds.
The exterior theorem covers one interval and assumes bounds on all actual
edges. It does not supply numerical constants, a rate uniform in circumference,
or a general assertion for correlated noise. The [observation review](reviews/physical_observations.md)
records the physical correspondence and normalization checks.

## Scope beyond the formal theorem

The development does not contain the annular embedding and topological
classification needed to identify even parity with contractibility and odd
parity with noncontractibility. It does not cover circumference two's parallel
edge convention or a common leading exponential coefficient with a smaller
exponential error term. The physical weighted extension covers one shared
field with common positive bounds; arbitrary positive fields with unbounded
contrast are not covered. No uniform convergence rate in the circumference
is asserted.

## Review and provenance

The proof sources and review reports are AI-authored. Separate agents
reviewed the [graph statements](reviews/graph_statements.md),
[concrete auxiliary](reviews/auxiliary_cycle.md),
[zero-parity witnesses and selected-edge splice](reviews/zero_witnesses_and_splice.md),
[frontier substitution](reviews/frontier_substitution.md),
[undirected counted objects](reviews/counted_objects.txt),
[selected-edge characterization](reviews/selected_edge_characterization.json),
[ordered matrix argument](reviews/ordered_matrices.md), and
[finite labelled-transfer ratio](reviews/finite_labelled_transfer.md).
The auxiliary and zero-witness reviewer authored the imported enumeration
helper; those reports explicitly exclude independent review of that helper.
The repository steward also read the packaged sources. The conventional
project check validates their integration under the pinned dependencies.

Further reports in the [review directory](reviews/) cover concrete boundary
states and fragments, exact column-mask and parity-count correspondences,
physical weight decomposition, generalized boundary degrees, edge
replacement, selected end verticals, cycle saturation, and full-crossing
exclusion. Each report distinguishes source review from a compiler replay
and records its dependency and authorship limits.

The reports identify the earlier prototype hashes and may refer to paths
in the reviewers' workspaces. [`provenance.json`](provenance.json) maps
each prototype hash to the packaged source. Four graph files have only a
documentation-heading marker normalized; their proof text is unchanged.
All other packaged proof sources are byte-identical to their frozen
prototype versions. Compilation of the packaged files is checked afresh.

The [counted-correspondence review](reviews/counted_transfer_equivalence.md)
checks the unconditional realization and both inverse identities. The
[accepted-data helper reviews](reviews/accepted_helpers.md) distinguish
conditional relation recovery from unconditional physical parity recovery.
The [transfer and completion review](reviews/transfer_completion_and_states.md)
records the remaining state and prefix interfaces and their authorship
limits. Separate splice reports cover the exact selected-graph identity,
prefix restriction, and the three non-parity state fields.

The final stage is covered by the [state and return review](reviews/splice_returns_and_interval.md),
[all-pairs connectivity review](reviews/core_connectivity.md),
[core-flip review](reviews/core_state_flip.md),
[counted-label symmetry review](reviews/core_label_flip.md), and
[final ratio review](reviews/triangular_count_ratio.md).
The [finite imbalance review](reviews/triangular_count_imbalance.md) checks
the geometric strengthening and its quantifier order.
The [integration assessment](reviews/final_parity_interfaces.md) records the
remaining parity and coordinate interfaces, the counting conventions, and
the exact limits of these reviews.

The [weighted application review](reviews/weighted_application.md) records the
eight-module extension, exact physical counting convention, uniform quantifier
order, source-review provenance, and the integration gate. Earlier review
reports describe their own pinned checkpoints and may list weighted counts
among work that was then outside scope.

The [physical observation review](reviews/physical_observations.md) covers the
ten-module extension, exact likelihood and exterior-event identities,
canonical observation partition, normalization, and independent source-review
limits. The project verifier includes all of its declarations in the same
exact audit inventory.

The repository's [CC0 notice](../LICENSE.txt) applies to this original work.
Mathlib and Lean retain their own licenses. The concrete parity-count ratio
is a kernel-checked theorem under the pinned dependencies. Human review,
external adoption, and literature-wide priority have not been established.
