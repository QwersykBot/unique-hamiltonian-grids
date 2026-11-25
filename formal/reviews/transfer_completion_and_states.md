# Transfer states, prefix completion, and parity: source review

Reviewer: the repository steward, 2026-11-25 UTC. **PASS in the stated scope.**
The complete sources discussed here were read at the frozen hashes recorded
in `../provenance.json`. This is a statement, data, and composition review.
Producer strict-compilation and exact-axiom receipts were inspected; the
conventional project verifier and hosted workflow check the assembled source
closure separately. No human review or independent kernel is claimed.

## Actual states and counted data

`ActualTransfer` uses the frozen raw encoder. A core state is an actual
occurrence with nonfull outgoing H/D masks. The full-crossing theorem puts
every cut of a Hamiltonian cycle of width at least three in this core. The
two-column perimeter remains an allowed witness; the all-H/D exception is
excluded. Initial and terminal label witnesses may have two columns, while
a local witness must have an actual consecutive pair of nonterminal cuts.

The label data are just vertical masks. Width, cut position, root, traversal,
and Hamiltonicity are existential propositions, not additional counted
choices. Cut-width equivalences preserve numeric row and column labels.
Horizontal and diagonal physical-ID specifications retain their source-row
convention, including the cyclic row successor for a diagonal.

`CycleAccepted` reads all cuts in order and places the initial, local, and
terminal V masks in their actual column positions. `AcceptedReconstruction`
computes states and masks directly from the counted selection's edge finset.
An existential Hamiltonian presentation is eliminated only to prove the
occurrence and label properties. Exact edge recovery proves a forward
injection without choosing a traversal as data. Its source-local claim is
an injection; the later inverse is proved in the separate composition.

## Exact prefix replacement and one-column extension

`PrefixReplacement` derives mixed ambient validity, connectedness, and
degree two from two genuine selected completions with matching H/D/reach
fields. Attachment is derived from each original connected graph. Boundary
degree composition uses the suffix's lack of boundary-to-boundary edges;
the prefix may own selected verticals in that column. The selected-edge
characterization then supplies a standard Hamiltonian cycle using exactly
the mixed graph's edges. No property of the mixed graph is assumed.

`FragmentRecovery` proves exact P/Q recovery for the canonical transported
glue, requiring only that Q own no boundary-to-boundary edges. Empty prefix
interiors are permitted. Its H/D fields come from the retained suffix,
while its reach relation comes from the retained prefix.

`ColumnStepConnectivity` shows that within-column adjacencies are determined
by the physical V mask and that the old H/D masks plus the next V mask
determine the entire one-column suffix. Its reachability substitution uses
explicit attachment, not connectedness of a processed prefix.
`ProcessedPrefix` provides the physical normalization and derives that
attachment from connectedness of the original completed graphs. It permits
different lengths and different source cut positions.

`CompletionTransport` advances the cut by a coordinate reassociation,
preserves exact remaining suffixes, and identifies the actual shorter
processed graph. Its equality of extended prefix graphs requires exact old
prefix equality and physical extension choices, with no reconstructed
connectedness premise. That distinction is essential to the later induction.

`AcceptedRealization` maintains genuine completions and their exact prefix
graphs at all accepted cuts. Each local step uses the preceding completion
and the local label's actual witness. The comparison with the reconstructed
prefix needs only its ambient validity and exact masks. At the final cut,
both the retained prefix and the one-column suffix equal those of the
reconstructed graph. The full graph equality gives exact Hamiltonian edge
realization, including path length zero. The separate nonauthor review in
`counted_transfer_equivalence.md` checks this argument and the counted
inverse composition in detail.

## Existing parity and boundary observations

`BoundaryParity` does not replace the original parity. It identifies the
selected physical-ID sum filtered by source column at most the cut. The V
and D last-row terms are the exact meridian contributions. Outgoing D at
the current cut is charged even though that edge is not yet in prefix
connectivity. The identities also make sense for an arbitrary graph by
selecting only its physical cylinder edges.

`BoundaryParityUpdates` proves the initial, successor, and terminal sums.
The first cut has its first V and outgoing D charges. Each successor adds
one new V and one new outgoing D. After the last cut, only final-column V
remains. Actual trail parity equals the selected physical-ID sum, so terminal
label parity uses the existing walk and counted-selection definitions.

`AcceptedParity` uses these equations and exact V/D recovery to identify
every recorded cut parity without assuming reconstructed connectedness.
Its total selected-edge weight equals the recorded terminal class. An
existing counted selection is formed only when exact realization is supplied.
`AcceptedStateRecovery` explicitly assumes reconstructed connectedness for
R-field recovery; `AcceptedRealization` supplies it before the final inverse
is used. No circular connectedness assumption enters the bijection.

`FiniteTransferPaths` retains the ordered states and labels of each sequence.
`CycleIntervals` restricts the actual cut sequence of one cycle to an ordered
interval. Its length is the difference of cut values, and both endpoint
transports preserve the original label observations, including length zero.
`TransferWitnesses` obtains actual initial and parity-zero terminal choices
from the perimeter; it asserts no short-length count positivity or returns.

## Splice interfaces and end availability

The selected-splice graph, coordinate, prefix-restriction, and deletion
helpers were read in full. Their independent reports separately identify
which source was authored by each reviewer. The concrete old-prefix theorem
retains the same output Hamiltonian cycle, exact edge formula, and total
parity addition while deriving old-prefix reachability. Its cut-zero case
puts the removed old edge in the boundary and remains covered by the
restriction theorem. The H/D mask proof uses different-column adjacency,
which the deleted first-column vertical cannot alter.

`StateEndVertical` derives both end verticals for a nonfull actual state.
For at least three columns it uses the checked end-vertical theorem. At
two columns, positive suffix length forces the unique cut; a missing
vertical at either end forces both outgoing masks full. The conclusion
uses actual selected edge-list membership, as required by splicing. No
reference zigzag or uniqueness premise is needed.

## Independence and scope

The steward authored `FiniteTransferPaths`, `TransferWitnesses`,
`ColumnStepConnectivity`, `AcceptedExtensionality`, `AcceptedGraph`,
`AcceptedStateRecovery`, `AcceptedUniqueness`, and
`CountedTransferEquivalence`; this report is not an independent review of
those sources. Other agents read those helpers at their frozen pins.
The preserved helper and counted-correspondence reports cover their
statement and indexing checks without claiming a separate compiler replay.
All other new proof sources discussed above were independently read by the
steward. Exact producer pins map to packaged bytes in provenance.

The finite counted correspondence is complete for circumference at least
three and length at least three. Core parity-flip closure, transition and
terminal label symmetry, all-pairs support connectivity, common positive
returns, and the resulting asymptotic ratio remain separate obligations in
this checkpoint. Annular topology and the circumference-two multigraph
convention are also outside these statements.
