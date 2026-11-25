# Independent review: column-cut boundary degrees

**Verdict: PASS for all six statements in the frozen module.** The complete source was read, the column-cut and outgoing-mask definitions were inspected, and one fresh module replay succeeded. Its object file is byte-identical to the producer's pinned output.

## Frozen input and reviewed interfaces

- Source: `../ColumnBoundaryDegree.lean`, 5,226 bytes.
- Source SHA256: `253de1f7cd3dab7661ec40cd33d41ebbff80e23979399fdb48ba1c9a06483d7e`.
- Namespace: `TriangularCylinder.ColumnCut`.
- Imports: `ColumnCutOutgoing` and `FrontierDegreesGeneral`.
- Dependency-pin file SHA256: `5dd252ae87917cc6ca2075f1fb69a704e7ba630b339f38653fd3ff4e106967a3`.
- Producer receipt SHA256: `3e629769dedef8591d4917e6b538ab68dc6ba932367f2e1fc3ac3ea6dd13b521`.

The six exported results transport neighbor cardinality through the existing column-cut graph isomorphism, recover each piece's interior degrees, sum its two boundary contributions, compare prefix boundary contributions when the physical outgoing masks agree, and prove degree two for the mixed canonical glue.

## Exact decomposition and cardinality transport

For a cut after column `j`, the prefix interior is `Vertex m j`, the shared boundary is `Fin m`, and the suffix interior is `Vertex m k`. The canonical vertex equivalence sends these to columns below `j`, column `j`, and columns above `j`, respectively. The prefix is the full induced restriction including the boundary. The suffix excludes every boundary-to-boundary edge. Thus every selected vertical edge within the boundary belongs to the prefix only.

`glue_parts_neighbor_ncard` applies the existing `glueIso` neighbor-set equivalence and transports `Set.encard` through `ENat.toNat`. This proves the displayed `ncard` equality without changing the vertex map. The two interior identities then use the already-reviewed canonical interior-neighbor lemmas; their chosen sum constructors correspond to the prefix and suffix embeddings exactly.

`parts_boundary_neighbor_ncard_sum` uses the generalized degree lemma with the suffix-only no-boundary-edge hypothesis. This is the appropriate hypothesis here: prefix boundary vertical edges are allowed. The mapped neighbor sets are disjoint because the interior tags differ and the suffix has no boundary neighbors. Their sum equals the degree of the physical boundary vertex `(r, boundaryCol j k)`.

These four results allow arbitrary natural `j,k`, including zero. All relevant vertex types are finite.

## Outgoing masks, lengths, and the mixed glue

The inspected physical mask definitions are:

- `horizontal r`: the edge from `(r,j)` to `(r,j+1)`;
- `diagonal r`: the edge from `(r,j)` to `(rowSucc r,j+1)`.

The diagonal bit is indexed by its boundary **source** row. It is not indexed by the destination row and is not an incoming-diagonal bit. The exact ambient adjacency and suffix restriction imply that these are the only possible suffix neighbors of boundary row `r`. Their endpoints are distinct for `m >= 3`. Consequently the suffix degree is the sum of these two Boolean indicators.

For two selected degree-two graphs, write their boundary contributions as `p + q = 2` and `p' + q' = 2`. Literal equality of the two outgoing mask functions on the common `Fin m` gives `q = q'`; the proof's `omega` step then establishes `p = p'`. No connectivity assumption or subtraction convention is hidden in this step.

In `mixed_parts_neighbor_ncard_two`, the retained prefix is from `H` with dimensions `j + 1 + oldSuffix`; the retained suffix is from `K` with dimensions `oldPrefix + 1 + k`. The theorem compares their masks at the same physical row labels. Its conclusion is degree two on the canonical vertex type

`Vertex m j ⊕ (Fin m ⊕ Vertex m k)`.

The proof preserves the prefix interior degrees from `H`, preserves the suffix interior degrees from `K`, and replaces the prefix boundary contribution from `H` by the equal one from `K`. The existing boundary sum for `K` then supplies two. Thus the argument has the correct direction for the stated mixed prefix/suffix.

Neither `j = oldPrefix` nor `oldSuffix = k` is required. Both original suffix lengths must be positive to define the outgoing masks, exactly as the theorem assumes. If `j = 0` or `oldPrefix = 0`, the corresponding prefix interior is empty and its interior statement is vacuous; the full boundary column, including its vertical edges, remains present. Boundary contributions `2 + 0`, `1 + 1`, and `0 + 2` are all covered. A separate conceptual review of these ownership and endpoint cases found no obstruction.

## Independent replay and pins

The replay used a previously absent output directory and excluded the producer's output directory from `LEAN_PATH`. It checked all 22 recorded dependency file hashes, representing 11 local modules. It also checked the actual first-resolved object for every local module. In particular, `FrontierSubstitution.olean` is first found in `root-extension-replay/build`; that object matches the recorded prepared-environment pin, so the search order introduces no unverified variant.

- Lean: 4.19.0, compiler commit `6caaee842e94`.
- Mathlib commit: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Mathlib manifest SHA256: `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`.
- The Mathlib tracked tree was clean before and after replay.
- One compilation with `-DwarningAsError=true` exited zero, with empty stderr.
- Each of the six printed theorem axiom reports contains exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Independent output: `build/ColumnBoundaryDegree.olean`, 129,320 bytes.
- Output SHA256: `d7d667ccd2276475e3e62c3cfcc8c68eff57b4e57840ffee8f674d271f54dfcf`, matching the producer pin.
- Independent receipt SHA256: `c32394db41a4f7e5c0db8db80615c68016835d1d67605efb53ccc67c9eeb3c25`.

The source contains no `sorry`, new `axiom`, `unsafe`, or `native_decide`. Source, producer receipt, dependency pins, and imported artifacts remained unchanged. Upstream sources were inspected where relevant and their artifacts were hash-checked; they were not rebuilt. The exact command, resolved imports, axiom lists, and hashes are recorded in `compiler-receipt.json`; `compiler.log` contains the output. In this pinned workspace, a later replay can use `python3 replay.py --output-dir /absolute/path/to/a/new/replay-directory`.

## Scope

The mixed conclusion is degree two for the canonical glue. It supplies no connectivity, Hamiltonicity, parity, state-equivalence, transfer, or counting result, and it does not itself transport the mixed graph into a new physical cylinder. Those are separate interfaces. No enumeration or unrelated test was performed for this review.

Reviewed by `/root/strip_ports` on 2026-11-25. The frozen source and producer artifacts were not edited.
