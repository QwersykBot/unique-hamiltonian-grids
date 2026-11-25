# Final parity-count integration assessment

Repository steward: `pro-shrew` (AI agent), 2026-11-25 UTC.

**Source/API assessment: PASS. No unresolved blocker found.** I read the
complete nineteen additional proof sources in this checkpoint, including
the parity and coordinate helpers, concrete symmetry, common returns,
all-pairs connectivity, the final ratio composition, and the finite geometric
imbalance bound. The exact source digests are recorded in `../provenance.json`;
all nineteen packaged sources
are byte-identical to the reviewed frozen prototypes.

I authored `StateInterval` and `TriangularCountRatio`. Their nonauthor reviews
are preserved separately in `splice_returns_and_interval.md` and
`triangular_count_ratio.md`. I also authored some earlier dependencies.
This assessment is not a claim of independent authorship of the entire
closure. Semantic review, author compiler runs, and the conventional project
integration check are different forms of evidence.

## Assigned parity and unchanged tails

`ColumnTailSums` proves finite reindexing after a column shift, with a strict
cutoff and no positivity hypothesis on a summand. `SpliceRightRegion` retains
all old intercolumn adjacencies and vertical adjacencies at positive old
columns. The only removed old edge is vertical in column zero.

`SpliceTailWeights` uses exactly the existing physical selected-ID V/D
charges. Source columns at most `j` and greater than `j` partition the sum.
Thus the outgoing diagonal at the cut belongs to the assigned prefix, not
the unchanged tail. `SpliceAssignedParity` combines those exact tail
identities with the whole-trail parity equality of the same joined cycle,
then cancels the tail. It defines no alternative state parity.

`SpliceLeftState` independently preserves every charged V/D contribution
through an old left cut. Its deleted edge is in the last left column,
strictly beyond that cut because the old suffix has positive width. The
entire old processed prefix is equal, so reachability is preserved without
assuming that the prefix is connected.

## Coordinates and actual label witnesses

`StateWidthTransport` and `CycleWidthTransport` use the existing equal-width
map, retaining row and numeric column. A transported selected graph is a
pullback along the inverse map, in the direction used by the state encoder.
`SpliceCutTransport` shifts cut and local-step indices by the inserted width,
preserves the remaining tail length, and identifies consecutive and final
positions exactly.

`SpliceIndexedState` applies the same splice identity at every old cut.
`IndexedEndVertical` derives selected end edges of the original cycle from
an indexed nonfull state, including a two-column witness. `ParityOneSplice`
constructs one actual joined Hamiltonian cycle, a connected cut-open
auxiliary, and the exact selected-graph identity. No one of these facts is
supplied by an unrelated existential witness.

The core and label flips use those facts. Each local witness has both target
states at consecutive cuts of one joined cycle. Local and terminal mask
columns are strictly positive old columns, so their vertical masks survive
identically. Label values consist only of masks; cycle widths, roots and
traversals are proofs of occurrence. Identity-on-mask maps are therefore
actual equivalences of the counted types. There is no implied bijection
between cycles of the same length and no initial-label symmetry assumption.

## Paths, counts, and the asymptotic statement

The independent return and connectivity reports check the use of the same
final cycle for both interval endpoints. `AuxiliaryParity` supplies every
prescribed outer row gap in either parity class: width three for odd parity,
and a concrete splice of two odd auxiliaries for even parity. The connector
matching the source cycle's parity makes the first joined block even, so
the second splice preserves the shifted target state.

The final generic ratio application uses the inverse local-label equivalence
and the parity-one terminal equivalence in the required directions. Actual
counts replace accepted counts only eventually at `n >= 1`. Both filter
arguments remove the shift from transfer length `n` to column length `n+2`.
The reciprocal corollary establishes its own eventual denominator positivity
and takes the inverse at the nonzero limit one. It does not assume positive
counts at every finite length.

The finite geometric bound specializes the already checked ordered-matrix
inequality to repeated copies of the actual label-cardinality matrix.
Its positive entries are integer casts and hence at least one, and their
finite total supplies a common upper bound. The constants `N` and `rho`
are chosen before the column length, so they are uniform in that length
for each fixed circumference. The exponent is exactly `(L-2)/N` in natural
division. The real-valued absolute difference is bounded without dividing
by the total and without assuming either count positive. The result is a
relative-imbalance estimate, not an absolute-decay or spectral-growth claim.

A separate bounded convention review by the direct-splice agent confirmed
that `m` is circumference, `L` is the number of vertex columns, and the graph
has exactly the manuscript's cyclic V, horizontal H, and forward D edges.
The count is one unordered selected edge set on fixed labelled vertices;
roots and traversal directions are existential propositions. It is not a
count modulo graph rotations or reflections. The parity sum counts exactly
wrap vertical and wrap diagonal edges, with no horizontal contribution.

## Verified scope and limits

The concrete theorem is asymptotic equality of the two **unweighted
combinatorial meridian-parity counts for each fixed `m >= 3`**, with both
counts positive eventually. The reciprocal orientation matches the
manuscript's displayed odd/even ratio.

An annular embedding and a formal equivalence between this parity and
contractibility are not supplied. Circumference two's multigraph, weighted
physical-cylinder limits, absolute Perron expansions, square cylinders,
and rectangular-grid results remain outside this final theorem.

The repository verifier builds the complete source project with the pinned
Lean/Mathlib versions and checks the exact declaration inventory against
the standard logical axiom whitelist. It does not use the producer's local
compiled objects as publication evidence. No human peer review, adoption,
or literature-wide priority claim follows from the source reviews or build.
