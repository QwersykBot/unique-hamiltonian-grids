# Independent review of three splice helpers

Reviewer: `charge_sectors`, 2026-11-25 UTC. **PASS in the stated scope.**

I read all three frozen source files and checked their relevant dependency interfaces. I then compiled each new module exactly once into this directory's initially empty `build/`, with warnings as errors. All three compilations succeeded, stderr was empty, and every resulting object matched the author's object hash. No frozen source, dependency, configuration, or existing build output was edited.

## Frozen inputs and replay outputs

| Module | Source SHA256 | Replayed object SHA256 |
| --- | --- | --- |
| `SplicePrefixCoordinates` | `2433a607d51ecc40c299d48b1a710e7a8b1ec24697b713e34eb576999ccc7e0d` | `4fa0856d272b286998a9dcf90766ab4442de0ac71640276e50a9371e8cabb86a` |
| `ReplacementRestriction` | `3bfb7b1bd342c291529cef81d15c95c625f4cc8d772515a70d079f8f50f46a96` | `c60d003b7bd36238a6c0c0116846a39e6f42996a9499022548c0000a91e6fe62` |
| `SelectedCycleDeletion` | `4e85e6dd8f1f5536f0ada1c72f8331f4c9b4e8d1dbc71d092db67cbbc4ffe00c` | `a5d2b715e3b34579d26627741d2121b8ce2e6a01617202a32b51cbf9f1d3ebf3` |

`compiler-receipt.json` records the complete command, working directory, `LEAN_PATH`, elapsed time, exit code, source/object hashes, output paths, and exact axiom reports for each compile. Individual stdout and stderr files preserve the compiler output.

## Source meaning

### Prefix coordinates

`columnSumEquiv` matches the existing physical `leftVertex` and `rightVertex` maps. `prefixEquiv` identifies a new block of `a` columns plus an old prefix of `j` interior columns and its boundary with the canonical enlarged prefix of `a+j` interior columns. The boundary row label is fixed; its physical column becomes `a+j`.

The checked `ColumnCut.prefixVertex` definition places interior columns at their original values and the boundary at the cut column. Consequently `fullWidth_prefixVertex_eq_physicalPrefix` expresses the exact intended equality of physical embeddings. `fullWidthEquiv` changes only the parenthesization of the width and retains the row and numeric column. The injectivity proof uses actual equivalences and the canonical injective prefix embedding.

Empty new or old interiors are permitted. In particular, `firstPrefixVertex` correctly lies in the boundary when `j=0`, and in interior column zero when `j>0`. The first-column identity's width hypothesis supplies the existing `firstCol` argument; no unnoticed positive-interior assumption is introduced. With `m=0`, row-indexed assertions are vacuous and the coordinate equivalences still make sense.

This module establishes coordinate equivalences and embedding equalities. An adjacency or selected-graph equality must be supplied separately.

### Restriction of edge replacement

`comap_replacementGraph` retains the whole gadget through the identity map and restricts old vertices along an injective map `f`. Both removed endpoints are expressly `f x` and `f y`. Injectivity converts endpoint tests in the two orientations of the removed unordered edge, and in both seams, to the corresponding tests on the restricted graph. The four sum-type adjacency cases establish graph equality directly.

`restricted_old_reachable_iff` applies the previously frozen edge-replacement theorem to `G.comap f`. Its selected-edge hypothesis is adjacency in that restricted graph, so it makes no unsupported inference from ambient reachability to restricted reachability. The gadget must be connected. Its two attachment vertices may coincide; no finite-type assumption is needed. An empty retained old type cannot supply the selected edge hypothesis.

### Deleting a selected Hamiltonian-cycle edge

The graph is exactly `fromEdgeSet C.edgeSet`, on the original vertex type. Each cycle edge survives this construction because it is a non-diagonal edge of the original simple graph. Transferring the walk to that selected graph preserves both its support and its edge list. The standard `Walk.IsHamiltonianCycle` hypothesis covers every vertex, which proves connectedness of the selected graph.

The selected edge remains on the transferred cycle, so Mathlib's bridge characterization excludes its being a bridge. `Connected.connected_delete_edge_of_not_isBridge` then gives connectedness after deletion. I checked these APIs and `IsHamiltonianCycle.mem_support` in the pinned Mathlib sources. The statement requires no finite-type instance; the supplied Hamiltonian walk already gives finite covering support. The selected-edge hypothesis excludes a diagonal edge and impossible degenerate cycles.

## Dependency and axiom scope

Lean: `4.19.0`, compiler commit `6caaee842e94`. Mathlib commit: `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Mathlib manifest SHA256: `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`. Mathlib tracked files were clean before and after replay.

`dependency-pins.json` records both source and imported-object hashes for the entire local import closure: `CylinderSplice`, `TriangularCylinder`, `FrontierSubstitution`, `FrontierAttachment`, `ColumnCut`, and `EdgeReplacementReachability`. Those twelve files and all three reviewed sources were checked before and after replay. Imported local dependency objects were reused only after checking their pins; this review does not claim to rebuild that closure. No author helper build directory was present on the replay `LEAN_PATH`.

The exact twelve audited declarations are:

- In `TriangularCylinder.SplicePrefixCoordinates`: `columnSumEquiv`, `columnSumEquiv_left`, `columnSumEquiv_right`, `ofPrefix_toPrefix`, `toPrefix_ofPrefix`, `prefixEquiv_boundary`, `fullWidth_prefixVertex_eq_physicalPrefix`, `physicalPrefix_injective`, and `prefixVertex_firstPrefixVertex`.
- In `CylinderFrontier.EdgeReplacement`: `comap_replacementGraph` and `restricted_old_reachable_iff`.
- In `CylinderFrontier`: `selected_cycle_delete_edge_connected`.

All reported axiom sets are subsets of `propext`, `Classical.choice`, and `Quot.sound`, and match the author's reports exactly. There is no `sorryAx` or custom axiom in this audit set.

This review covers the three helpers only. It establishes no cylinder splice, Hamiltonian-preservation, frontier-state, or counting-bijection theorem. The separate `SpliceSelectedGraph` and main prefix-reachability files were neither reviewed nor compiled here.
