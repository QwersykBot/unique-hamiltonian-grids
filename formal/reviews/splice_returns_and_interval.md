# Splice-state, common-return, and interval source review

## Scope and provenance

Result: PASS; no statement, indexing, or composition blocker found. Reviewer: `/root/formal_matrix_contraction`. This was a bounded complete source/API review of the three target files below, with focused reads of their exact encoder, splice, parity, deletion, and interval dependencies. No proof source/configuration was edited, no Lean compiler or optional tests were run, and no independent kernel replay is claimed. Existing compiler receipts were read as author-supplied evidence; the conventional full-source gate remains separate.

`SpliceLeftState` and `CommonReturns` were authored by `/root/direct_splice_formalization`; `StateInterval` was authored by `/root`. The reviewer did not author these three modules, but authored frozen dependencies including `BoundaryParity` and `CycleIntervals`; this review is therefore independent of the target authors, not wholly independent of every dependency.

## Frozen target pins

| Source | Bytes | SHA256 |
|---|---:|---|
| SpliceLeftState.lean | 13144 | 136d457154ea3e7c63b5530c688f617ea68077f36ef9b973f7d80473b1f52604 |
| CommonReturns.lean | 8660 | e7071f8e42b4b3dd9668c1ceb82fa9055706ef940bab0fcc31f23d931afb6313 |
| StateInterval.lean | 1746 | ac1b574fadd028a149e8dbed3244c5c196b505c89e7d11d9e8f75031811bcbb4 |

All three digests were checked before and after review and remained unchanged.

## SpliceLeftState: PASS

The generic theorem assumes the exact replacement-graph identity and derives every old-left raw-state field; it does not assume state equality, connectedness, or Hamiltonicity. Its width equivalence preserves row and numeric column. For an old cut j with k >= 1, the deleted left V edge is at column j+k > j. Thus every adjacency whose first endpoint is at or before j is unchanged, including outgoing H/D from column j to j+1 and the entire induced processed prefix. This remains valid for j=0 and k=1.

`stateAt_parity_geometry` unfolds the existing assigned-ID sum. Both V and D sums use source column <=j, so outgoing D at the cut is included; it is not silently moved to the unprocessed tail. The filtered finite-sum bijection preserves numeric column values and proves surjectivity from the same cutoff. The extension contains no new charged V/D source <=j. Prefix equality yields exact reach equality, and the four field equalities yield the full raw state.

The existential wrapper obtains one actual selected-edge splice J and derives both its exact graph identity and state equality from that same J and edge-set formula. It retains total parity addition and the graph identity needed for subsequent right-state reasoning.

## CommonReturns: PASS

`stateAt_eq_of_zero_splice` applies to a specified J and exact replacement identity, not a second independently chosen splice. H/D come from unchanged intercolumn edges. Reach requires and uses connectedness of the inserted cut-open graph and actual selection of the removed old edge. Parity comes from the existing total-minus-tail argument with delta=0. The underlying tail split uses strictly-greater source columns for both V and D; it therefore complements the assigned <=j prefix correctly, including j=0. Trails are explicit and sufficient for exact walk-parity/selected-ID identification.

For the two-column witness, the proof self-splices the concrete perimeter cycle at its selected before-last-to-last row gap. Deleting the selected left HCC edge proves the insertion connected. The old left cut 0 and shifted old right cut 2 of the same width-four J both equal the concrete commonWitnessState. The actual interval yields length 2.

For the three-column witness, the same construction uses its actual last cut 1. In the resulting width-six J, cuts 1 and 4 both equal the same concrete commonWitnessState. The actual interval yields length 3. Both witness parities are proved zero by the frozen concrete witness theorems. Neither return is assumed, and there is no distinct base state for the two lengths.

`common_interval_return` converts raw-state equalities to subtype equalities with the already defined `commonCoreState m hm`; proof irrelevance changes no state data. All intermediate LocalLabels come from the one actual joined cycle via `cycleIntervalPath_nonempty`. Replacing m by q+1 covers every m>=3 and does not restrict circumference parity.

## StateInterval: PASS

`path_between_stateAt` takes two ordered nonterminal cut splits of the same actual HCC C, each with an explicit width equality and its actual endpoint state equation. `hL : 3 <= L` yields n=L-2>=1, exactly the domain needed for automatic core membership. Positive remaining widths force both cut values into Fin(n+1). `stateAt_split_eq_cutState` identifies the unique remaining width without moving row or column values.

The returned path length is exactly j'-j in increasing column order. Coincident cuts j=j' are allowed and give a zero-length path; first and last nonterminal cuts are allowed. The theorem neither asserts arbitrary supplied states occur together nor assumes an abstract path: both endpoints are tied to cuts of C, and all labels are supplied by that same C.

## Exact dependency interfaces inspected

- BoundaryState.assignedIds/stateAt (source cutoff <=j; outgoing D included), source SHA 552632d73c5b5b3f5bb8af1a9486284ecbbeb108e44feacbbd1ae49b53a8d5c5.
- ActualTransfer.widthEquiv/cutTail/cutGraph/cutState, source SHA 44ec78edb856a632a67c7de0e3820b6cf710f7baeb57f4a68cb8b7178d64a506.
- SpliceSelectedGraph.selected_splice_comap, source SHA 8a52141b45b2615567ec1df364646b2d4e4f48c471a47d555ce46bc42a51727f.
- SpliceAssignedParity (full source), SHA 4a1cc134b84a59d25297c22e67605cad071558f8017d5a47ec6a17df343d7649; SpliceTailWeights exact prefix/tail and tail-transport formulas.
- SpliceStateFields (full source), SHA 9428144777177a073dfc68b66bb7012301eaabded6ab6b77b80a71e034456b11; SplicePrefixReachability.old_prefix_reachable_iff_of_comap.
- SelectedCycleDeletion (full source), SHA 4e85e6dd8f1f5536f0ada1c72f8331f4c9b4e8d1dbc71d092db67cbbc4ffe00c.
- TransferWitnesses.commonCoreState, SHA 8c56c6370e04840b10a0afd4bd2993205f15e62b467877e3c5b8c7d824f17967.
- CycleIntervals (full source), SHA f1613b141415e98e92ccc64916af989a580523e14c19fd9099f21cdafe5100f8.
- CompletionTransport.stateAt_split_eq_cutState, source SHA 1847a48fd2697aaaff859d92f633bc6c3abaa2732546d171a7639d447d437f2b.

Existing author receipts: verification/splice_left_state_receipt.json; verification/common_returns_receipt.json; verification/state_interval/verification.json. This review makes no all-pairs connectivity, parity-label equivalence, or asymptotic conclusion. CoreConnectivity will receive a separate source review after freeze.
