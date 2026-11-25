# Bounded full-source review of the counted correspondence

Reviewer: `/root/formal_matrix_contraction`. Result: **PASS, no source/API blocker identified**. Both complete source files were read; the stated source digests were checked. This was a bounded statement, data, indexing, and dependency-use review. No compiler replay, source edit, or configuration change was performed for the review.

## Reviewed sources

- `AcceptedRealization.lean`: SHA256 `60526f4eba6d1495b1b79659af0fefa90de5aba274f73435247890a23b8596a3`.
- `CountedTransferEquivalence.lean`: SHA256 `2bbb4a14e5b394755d7a397849c218f93816dacf45c45042db39a368d440e7a7`.

## Exact realization: no circular connectedness premise

`Genuine` is a proposition containing actual ambient inclusion, connectedness, degree two, and an actual standard Hamiltonian realization. Its constructors derive these properties through the existing checked connected/two-regular realization and exact prefix-replacement bridges.

`PrefixCompletion` retains a genuine completion of the processed prefix, equality of its entire selected prefix graph, and its outgoing H/D and reach fields. The initial completion comes from the actual initial label. At each successor step, the old genuine completion is mixed with the actual local-label witness. Connectedness needed for the reach update belongs to these two proved genuine graphs; reconstructed accepted connectedness is not assumed.

The comparison with the next accepted prefix uses ambient inclusion, exact old prefix, old H/D masks, and new V mask. It does not use a Hamiltonian or connectedness hypothesis on the reconstructed accepted graph. The successor arithmetic leaves a suffix of at least one column and preserves the intended processed-column index.

At the last cut, the actual terminal witness supplies a one-column suffix. Exact prefix equality and the last H/D/V masks yield suffix equality. The complete mixed graph is then proved equal to the reconstructed graph through the full vertex equivalence. The resulting genuine realization therefore selects exactly the reconstructed graph, not merely a graph with matching boundary data.

The final theorem converts edge-set equality to equality of the selected edge finsets using the existing no-edge-loss reconstruction result. Its only object input is an arbitrary `AcceptedObject hm p n`; no connectivity, realization, parity, or positive-length premise is added. Fin induction and the terminal argument cover `n = 0`.

## Counted bijection and transfer formula

`acceptedSelection` packages the existing reconstructed finset with the unconditional realization theorem and the already-proved existing selection-parity identity. It does not redefine parity.

The left inverse is exact physical edge recovery followed by two subtype extensionalities. The right inverse supplies the now-proved realization to the previously conditional accepted uniqueness theorem. The bijection explicitly requires `hn : 1 ≤ n`, hence width `n + 2 ≥ 3`, matching the range of the canonical counted-selection encoding and full-crossing exclusion. Unconditional realization at `n = 0` is not incorrectly promoted to a width-two bijection.

The source type is exactly the existing undirected `CountedHamiltonian.Selection`, restricted by the existing `selectionParity`. Data are finite sets of unordered edges on fixed vertex labels. Hamiltonian roots, directions, and traversals remain existential propositions. On the accepted side, labels are mask subtypes with proof-only realization witnesses. The inverse identities therefore address the intended objects without traversal multiplicity.

`parityCount_eq_card_paritySelection` identifies the existing finite filtered count with that precise subtype cardinality. The natural transfer formula then reuses `FiniteTransfer.card_accepted`, with the initial vector on the left, ordered matrix exponent `n`, and terminal parity family on the right. The real formula is the existing exact cast theorem. The local classical `DecidableEq (CoreState hm)` supplies the generic finite counting instances and changes no object definition or mathematical assumption.

## Scope

These modules prove exact realization and the finite counted correspondence in the stated ranges. They do not establish support connectivity, common positive returns, parity-flip transition symmetry, the ratio limit, or a topological interpretation of parity. The conventional full-source compiler gate remains a separate verification step.
