# SpliceStateFields: independent semantic review

**Semantic PASS; no independent compilation was performed for this module.** The full six-theorem source and its existing producer log were read. Source: 4,184 bytes, SHA256 `9428144777177a073dfc68b66bb7012301eaabded6ab6b77b80a71e034456b11`.

The two coordinate identities correctly identify the shifted boundary and next column under the full-width reassociation. They preserve rows and apply to every row, including a diagonal's successor row.

`right_adj_iff_of_col_ne` uses the exact replacement identity. In the old-old part of that graph, only the chosen first-column vertical is removed. Any two vertices in different columns cannot be its two endpoints, so their selected adjacency is unchanged. Added seams have a new-block endpoint and therefore add no old-old adjacency. Neither gadget connectedness nor selected-edge membership is needed for this adjacency statement.

The horizontal and diagonal mask equalities apply this fact to old columns `j` and `j+1`. The diagonal remains indexed by its boundary source row and targets the same cyclic successor row. Both masks are compared after shifting the cut to `a+j`; the proof establishes equality of the entire row-indexed Boolean functions. The nonterminal hypothesis `1 <= k` is explicit. There is no restriction excluding `j=0`.

The reachability Boolean equality additionally assumes a connected inserted graph and that the removed old edge is selected. These are exactly the hypotheses of the reviewed old-prefix reachability theorem. Instantiating its old vertices with boundary stubs and simplifying `prefixEquiv_boundary` fixes both boundary row labels; the Boolean conversion consequently gives the exact boundary-reachability function, without a permutation or rotation.

The statements are conditional on the same exact splice graph identity. They do not independently construct the splice or assert equality of assigned-prefix parity. In particular, the three field equalities do not yet establish equality of the complete state. The existing producer log prints six declarations with standard axiom subsets; this note makes no separate compiler-replay claim. No source edits, compilation, tests, or packaging were performed.

Reviewed by `/root/strip_ports` on 2026-11-25.
