# Exact finite cylinder counting and supporting lemmas

This is a development checkpoint of Lean proofs supporting the
[triangular-cylinder argument](../triangular_cylinder_asymptotics.md).
It proves an exact finite correspondence between undirected Hamiltonian
edge selections and accepted labelled transfers for consistently triangulated
cylinders with circumference and length at least three. It also contains
generic ratio theorems for labelled transfers and products of varying
nonnegative matrices.
**Neither cylinder asymptotic theorem has been fully formalized.**
The concrete symmetry, support-connectivity, and return-path hypotheses of
the ratio theorem remain to be supplied.

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
points; closure of the actual occurring states under that flip is still
an application obligation.

[CommonWitnessState](CommonWitnessState.lean) computes the entire state of
the two- and three-column zero-parity witnesses: only the first- and
last-row horizontal crossings are selected, every pair of boundary rows
is connected inside the prefix, and parity is zero. It proves literal
equality of the two states and actual occurrence for every `m ≥ 3`.
It does not yet prove transfer returns of lengths two and three.

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
reach fields. Assigned-prefix parity under that splice remains separate.
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
  CountedHamiltonian.parityCount m (n + 2) hm p =
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

## Remaining cylinder obligations

To obtain the formal asymptotic ratio for the actual cylinder counts, the
development still needs closure of actual core states under the parity
flip, local-label and terminal-label equivalences under that involution,
paths between every pair of core states, and common-state returns of
lengths two and three. The checked generic ratio theorem then supplies
eventual positivity from these hypotheses and the concrete nonempty
boundary choices. Weighted applications also require their claimed
physical edge-weight bounds.

Identification of combinatorial parity with annular contractibility,
the circumference-two multigraph convention, and the stronger absolute
Perron asymptotics are additional obligations. The generic ratio theorem
does not discharge them.

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

The repository's [CC0 notice](../LICENSE.txt) applies to this original work.
Mathlib and Lean retain their own licenses. These results are a reproducible
supporting checkpoint, with no claim of human review, external adoption,
literature-wide priority, or a complete formal cylinder proof.
