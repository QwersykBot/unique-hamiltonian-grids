# Checked supporting lemmas for the cylinder arguments

This is a development checkpoint of Lean proofs supporting the
[triangular-cylinder argument](../triangular_cylinder_asymptotics.md).
It also contains a generic theorem about products of varying nonnegative
matrices. **Neither cylinder asymptotic theorem has been fully formalized.**
The exact correspondence between transfer products and the intended cycle
counts remains to be proved.

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
[`ProofAudit.lean`](ProofAudit.lean), requiring exactly 54 named axiom reports.
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
with parity one containing both selected boundary edges. The current
concrete splice theorem takes each deleted edge first in its input walk;
conversion from an arbitrary selected-edge presentation is a separate
obligation at this checkpoint.

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

## Remaining cylinder obligations

To obtain a formal cylinder counting theorem, the development still needs
an exact finite state model, the isolated two-column case, a bijection
between accepted transfer configurations and undirected Hamiltonian edge
sets, preservation of actual frontier states under splicing, and the
concrete involution and endpoint exchange. It also needs common-state
return witnesses, support connectivity, positive totals, and any claimed
physical edge-weight bounds.

Identification of combinatorial parity with annular contractibility,
the circumference-two multigraph convention, and the stronger absolute
Perron asymptotics are additional obligations. The generic ratio theorem
does not discharge them.

## Review and provenance

The proof sources and review reports are AI-authored. Separate agents
reviewed the [graph statements](reviews/graph_statements.md),
[concrete auxiliary](reviews/auxiliary_cycle.md), and
[ordered matrix argument](reviews/ordered_matrices.md). The auxiliary
reviewer authored the imported enumeration helper; that report explicitly
does not claim independent review of the helper. The repository steward
also read the packaged sources and ran the conventional project check.

The reports identify the earlier prototype hashes and may refer to paths
in the reviewers' workspaces. [`provenance.json`](provenance.json) maps
each prototype hash to the packaged source. Four graph files have only a
documentation-heading marker normalized; their proof text is unchanged.
All other packaged proof sources are byte-identical to their frozen
prototype versions. Compilation of the packaged files is checked afresh.

The repository's [CC0 notice](../LICENSE.txt) applies to this original work.
Mathlib and Lean retain their own licenses. These results are a reproducible
supporting checkpoint, with no claim of human review, external adoption,
literature-wide priority, or a complete formal cylinder proof.
