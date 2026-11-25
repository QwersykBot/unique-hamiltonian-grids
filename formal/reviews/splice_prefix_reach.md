# Independent review: splice prefix reachability

**PASS.** The complete frozen source and its applied interfaces were read. One independent compilation of the new module reproduced the frozen object exactly. No helper or upstream source chain was rebuilt.

## Pins and replay

- Source: `SplicePrefixReachability.lean`, 6,415 bytes, SHA256 `67d6d9f38d9924194eaf91318464f7dfc016be1179bf3208f7b272e9b3fbc184`.
- Independent object: 199,016 bytes, SHA256 `af0a6092ccc9521b50e7b6a504dcf541450de66c8f637fa659b08a729d79f8f7`.
- Receipt SHA256: `aa567b68327fc3f4cf7b65823c57014e868e36f344afb6c3d4b3a8334a306991`.
- Dependency-pin file SHA256: `ded51662f047fa0bfccd56224ab3543abd887d27e4b6432d8467beec297ae41f`.
- Compiler-log SHA256: `b2a0feec51a915da5986095ae061847cfad3a6cf560739e32f49516892b7e29e`.

The fresh build used Lean 4.19.0 (`6caaee842e94`), pinned Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the recorded manifest. All thirteen local dependency source/object pairs and their first-resolved import paths were checked. The producer's target-module build was excluded. Compilation with `-DwarningAsError=true` exited zero with empty stderr; all four exact audit targets report only `propext`, `Classical.choice`, and `Quot.sound`. Inputs and the Mathlib tracked tree remained unchanged. The exact command, paths, audit names, and output are in the receipt and log.

## Source meaning and application checks

`joinedPrefix` takes the complete canonical prefix through physical column `a+j`. The full-width equivalence reassociates `(a+j)+1+k` and `a+(j+1+k)` without changing coordinate values. The prefix equivalence places all left-block vertices and all old-prefix vertices in this prefix. Its boundary clause fixes each `Fin m` row label exactly. The two comap equalities correctly express this coordinate identification and its factorization through the full two-block bijection.

The abstract reachability theorem assumes an exact replacement-graph identity, a connected inserted graph, and the selected old first-column edge. It derives injectivity of the old-prefix map from the existing canonical embeddings. Both removed old endpoints belong to the retained image: `firstPrefixVertex` puts them in the boundary when `j=0`, and in old-prefix column zero when `j>0`. Thus the restriction helper applies with its actual endpoint-in-image and injectivity requirements satisfied. The entire inserted graph is retained; no connectedness of the old prefix is needed.

The direction of `Iso.reachable_iff` is correct: reachability at the image vertices of the joined prefix is equivalent to reachability in its comap. After rewriting that comap as the restricted replacement, the generic old-vertex reachability theorem gives the exact old-prefix relation, for every pair of old-prefix vertices, including boundary vertices.

For the concrete existential theorem, the assumptions are `m >= 3`, left width `a >= 2`, old width `j+1+k >= 2`, two actual Hamiltonian-cycle walks, and selected vertical edges at the same `NextRow` gap in the left last column and old first column. The existing selected-edge splice theorem supplies one witness `J`. Its Hamiltonicity, total-parity sum, and exact edge-set formula are retained unchanged while adding reachability preservation for that same witness.

The inserted gadget is the exact selected graph of the left cycle with its chosen edge deleted. The deletion helper supplies connectedness. The selected-graph identity excludes additional ambient seam edges, so the restriction concerns the actual selected graph rather than the ambient cylinder. The old selected adjacency follows from the stated edge membership and distinctness furnished by the vertical-edge hypothesis. The reversed written order of the deleted right edge is harmless because edges are unordered.

There is no positive-cut assumption. At `j=0`, the chosen old edge lies entirely in the boundary and the proof still applies. `k=0` is also permitted whenever the old total-width hypothesis holds; no nonterminal state is asserted. The abstract theorem allows general connected gadgets, while the concrete application supplies the connected graph obtained from the Hamiltonian cycle.

The separate graph-module review and three-helper review reported PASS; this review checks their composition and applied interfaces rather than duplicating those reviews. A conceptual challenge likewise found no endpoint, containment, or empty-prefix obstruction.

## Scope

The theorem returns an actual Hamiltonian splice, its exact selected-edge formula, total-parity addition, and preservation of all old-prefix reachability under the fixed boundary labeling. It does not establish equality of the full boundary state, outgoing masks, or assigned prefix parity. No enumeration, additional theorem tests, or packaging was performed.

Reviewed by `/root/strip_ports` on 2026-11-25. Frozen inputs were preserved unchanged.
