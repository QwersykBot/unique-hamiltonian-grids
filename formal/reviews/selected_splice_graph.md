# Independent review: SpliceSelectedGraph

## Result and review boundary

**PASS.** The frozen root-authored module was read in full, its public signatures and proof composition were reviewed, and it was compiled independently in a newly created empty build directory. No source/API defect was found. The fresh object is byte-for-byte identical to the frozen original.

The reviewer is `/root/splice_coordinates`; the author of the reviewed module is `/root`. This review covers `SpliceSelectedGraph.lean`. The reviewer authored the imported `SplicePrefixCoordinates.lean`, so its source/object pin checks are **not** an independent review of that helper. `ReplacementRestriction.lean` and `SelectedCycleDeletion.lean` are not dependencies of this replay and are not reviewed here.

Reviewed source: `SpliceSelectedGraph.lean`, 5,229 bytes.

- Source SHA256: `8a52141b45b2615567ec1df364646b2d4e4f48c471a47d555ce46bc42a51727f`.
- Frozen original object SHA256: `66bf6521d836484445dea0847c5100905a6178bbd832a541d16704dad65b1334`.
- Fresh independently compiled object SHA256: `66bf6521d836484445dea0847c5100905a6178bbd832a541d16704dad65b1334`.

## Source and API review

The module imports `SelectedCylinderSplice`, `SplicePrefixCoordinates`, and `EdgeReplacementReachability`. Its generic part uses arbitrary vertex types and sets of unordered edges. No finiteness assumption is introduced.

### Disjoint edge formula

`CylinderFrontier.EdgeReplacement.spliceEdges` puts the gadget/left block in `Sum.inl` and the old/right block in `Sum.inr`. It inserts seams from `inl a₀` to `inr b₀` and from `inr b₁` to `inl a₁`, removes the gadget edge `{a₀,a₁}`, and removes the old edge `{b₁,b₀}`. That last order agrees with the concrete splice formula. Since edges are elements of `Sym2`, it denotes the same unordered old edge as `{b₀,b₁}`.

The private image-membership lemma correctly quantifies over both orientations of an unordered pair; it does not assume injectivity where none is available.

`fromEdgeSet_spliceEdges` identifies this selected graph with `replacementGraph (fromEdgeSet EB) ((fromEdgeSet EA).deleteEdges {s(a₀,a₁)}) b₀ b₁ a₀ a₁`. Reviewing its four sum cases confirms that within-left edges, within-right edges, and both seam orientations match. Sum constructors separate the blocks. Diagonal pairs in either input set are discarded consistently by `fromEdgeSet` on both sides. The identity does not require the removed edges to be present or the attachment endpoints within a block to be distinct; those assumptions belong to later applications when needed.

### Transport through a vertex bijection

`fromEdgeSet_image_comap` pulls the graph reconstructed from an edge-set image back through the same equivalence. The proof uses injectivity both for edge-image membership and for preservation/reflection of inequality, so loop removal is handled correctly even if the original edge set contains diagonal pairs.

`image_spliceEdges` transports the complete inserted-seam and removed-edge formula through an equivalence. The use of `Set.image_diff` is justified by injectivity of the induced `Sym2.map`; this prevents another source edge from colliding with a removed edge. Image composition and pair mapping then produce the displayed physical formula.

### Concrete selected-splice equality

`TriangularCylinder.SpliceSelectedGraph.selected_splice_comap` takes the exact selected-edge formula as `hset`. Its output is the pullback of the selected graph of `J` under `columnSumEquiv m a b`, equated with replacement of the first-column edge of `B` by the selected graph of `A` with its last-column edge deleted.

The endpoint assignments are consistent throughout: row `r` attaches the last column of `A` to the first column of `B`, and row `s` provides the other seam. Both block maps coincide with `leftVertex`/`rightVertex` by the coordinate helper's computation rules. `Walk.edgeSet_map` turns the selected mapped walks into the corresponding unordered-edge images. The final proof then applies the two generic graph identities.

This theorem appropriately makes a **conditional structural claim** from `hset`. It does not need or assert Hamiltonicity, selected-edge membership, gadget connectedness, or reachability. These premises and conclusions must be supplied separately by the actual-splice construction and the subsequent reachability argument. The bounds on cylinder dimensions support the existing graph and endpoint definitions. No additional row-alignment hypothesis is hidden in this graph equality.

## Independent replay

The replay used Lean 4.19.0, compiler commit `6caaee842e94`, Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and manifest SHA256 `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`.

The verifier checked the target source and frozen original object, plus all ten local dependency source/object pairs, before and after compilation. It also checked the local import closure and tracked Mathlib cleanliness. The dependency modules were `ColumnCut`, `CylinderSplice`, `EdgeReplacementReachability`, `FrontierAttachment`, `FrontierSubstitution`, `SelectedCylinderSplice`, `SelectedEdgePresentation`, `SplicePrefixCoordinates`, `TriangularCylinder`, and `TriangularParity`. Their exact byte pins and resolved paths are recorded in `pins.json` and `compiler-receipt.json`.

Only the new target module was compiled. Existing pinned dependency objects and the prepared Mathlib cache were imported; this was not a rebuild of the complete toolchain or dependency closure. The original target build directory was excluded from `LEAN_PATH`, and the output directory began empty. Compilation used `-DwarningAsError=true` and returned exit code **0**.

All four exact audit targets passed, with no additional compiler output:

| Target | Reported axioms |
|---|---|
| `CylinderFrontier.EdgeReplacement.fromEdgeSet_spliceEdges` | `propext`, `Classical.choice`, `Quot.sound` |
| `CylinderFrontier.EdgeReplacement.fromEdgeSet_image_comap` | `propext`, `Quot.sound` |
| `CylinderFrontier.EdgeReplacement.image_spliceEdges` | `propext`, `Classical.choice`, `Quot.sound` |
| `TriangularCylinder.SpliceSelectedGraph.selected_splice_comap` | `propext`, `Classical.choice`, `Quot.sound` |

There was no `sorryAx`. The exact source has no `sorry`, `admit`, new `axiom`, or `unsafe` token. No frozen source or dependency was edited.

## Reproduction

From this directory, run `python3 verify.py`. The script always creates a new empty `fresh-build-*` directory and writes a new compiler log and receipt.

For another checkout with the same pinned bytes, pass `--prepared-root`, `--splice-root`, and `--frontier-root` as needed; `--review-root` changes only the output location. The prepared root can also be supplied through `CYLINDER_PREPARED_ROOT`. The corresponding prebuilt dependency objects and frozen original `graph-build/SpliceSelectedGraph.olean` must be present at the recorded relative locations. Hash checks fail if any frozen input differs.

This evidence supports the source/API review and reproducible graph equality. It is not evidence of completion of the later prefix-reachability theorem, nor of any counting or asymptotic result.
