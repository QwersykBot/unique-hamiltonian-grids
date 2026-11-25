# Statement-fidelity review: boundary states, column fragments, common witness state

Date: 2026-11-25. Reviewer: `/root/external_math_validation_route`.

## Findings and remaining gaps first

**Scoped pass: no mathematical statement-fidelity blocker or necessary source correction found. All three requested strict verifier replays passed.** The following application boundaries remain explicit:

- `ActualState` contains every raw state occurring at a nonterminal cut of an actual Hamiltonian cycle. It does not remove the isolated two-column state. The proved parity flip acts on `RawBoundaryState`; closure of actual states under flip is not proved here.
- `ColumnFragments` establishes legal ambient adjacency after mixing fragments from different original lengths. It does not assert that the join is degree two, connected, Hamiltonian, or has a specified parity.
- `CommonWitnessState` proves literal equality of all four raw fields at the designated two- and three-column cuts, and actual occurrence. It does not yet give transitions or closed transfer walks of lengths 2 and 3.
- The raw encoder `stateAt` accepts any simple graph on the displayed vertex type. An arbitrary encoded graph is not automatically ambient-valid or actual. Actual occurrence separately supplies a Hamiltonian walk in the actual cylinder graph and encodes its selected edges.

The modules' stated scope agrees with these limitations; I found no claim in their theorem statements that silently assumes the missing transfer theorem.

The supplied `CommonWitnessState` pin had a transcription omission. Its actual 64-character SHA-256 is `5c644a34f3b381ae3dd54569c5925912d39cfd4e76084b6138ecb345b40e51de`, including the `8` before `ecb`.

## Independence

I authored none of the three reviewed modules. I read each complete source and each complete verifier script. I authored `EnumeratedWalk`, which is a transitive dependency of the concrete witness construction; this review independently assesses the new instantiation/composition and does not independently certify that helper. I also authored `ConnectedTwoRegular` and `FrontierCongruence`; neither is in the inspected local dependency chain. My `ColumnCutOutgoing` is explicitly excluded and is not imported by these modules. No independence claim is made for any of my helpers.

I reused the previous concrete-witness review in `/workspace/scratch/4a160f238522/zero_witness_splice_statement_audit_20261125.md` for its frozen traversal results, and checked the new common-state arguments themselves. No frozen source or configuration was edited.

## Frozen source pins

Prototype root: `/workspace/scratch/4a160f238522/cylinder_formalization_20261125/`.

| Source | SHA-256 verified before and after replay |
|---|---|
| `BoundaryState.lean` | `552632d73c5b5b3f5bb8af1a9486284ecbbeb108e44feacbbd1ae49b53a8d5c5` |
| `ColumnFragments.lean` | `24bedfdbfe637f2432838d483b16cf2c431f96a5c8c23cff2eb416bd412f5391` |
| `CommonWitnessState.lean` | `5c644a34f3b381ae3dd54569c5925912d39cfd4e76084b6138ecb345b40e51de` |

Environment: Lean 4.19.0, commit `6caaee842e94`; Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; manifest SHA-256 `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`. The scripts checked that tracked Mathlib sources were unchanged.

## Boundary-state semantics

The cut parameters have their intended meaning: `j` earlier columns, boundary column `j`, and `k ≥ 1` unprocessed columns, for total length `j+1+k`. This includes the first cut (`j=0`) and guarantees a real next column. Boundary rows remain the distinct fixed labels `Fin m`.

The two mask bits test the actual physical edges from `(r,j)` to `(r,j+1)` and `(rowSucc r,j+1)`. Their endpoint interpretation follows the existing physical V/H/D identifier map, including the cyclic diagonal at the last row. They are not proxy relation edges.

`assignedIds` filters all physical identifiers by selected-edge membership and source column at most `j`. Vertical identifiers use their own column; horizontal and diagonal identifiers use the lower/source column. Thus outgoing edges are assigned already at the cut, while incoming edges have their earlier source assignment. The sum is over a finite set of identifiers. The frozen physical encoder proves those identifiers represent distinct actual edges for `m ≥ 3`, so this does not introduce duplicate physical-edge contributions.

In particular, selected outgoing wrap diagonals contribute to parity at their source column. They do not enter prefix connectivity: `reach` is the Boolean truth value of `Reachable` in `ColumnCut.prefixPart`, the restriction to processed vertices only. The next-column target is proved outside every prefix-coordinate image. The parity sum never uses the Boolean reachability relation.

Raw states form a finite product of two Boolean row masks, a Boolean row-pair relation, and `ZMod 2`. This does not impose validity on arbitrary raw relations. The encoder's relation is separately proved reflexive, symmetric, and transitive using actual graph reachability. Finiteness and actual-state `Fintype` instances are noncomputable existence constructions, not an executable enumeration of completable states.

`Occurs` quantifies over a standard `Walk.IsHamiltonianCycle` in the actual graph and stores the state of `fromEdgeSet C.edgeSet`. The chosen walk root/direction is only an existential witness to a proposition; it is not another coordinate of the state or its cardinality. The occurrence predicate does not assume the desired state-sufficiency property. Raw parity flip changes only the `ZMod 2` coordinate; its involutivity and absence of fixed points are correctly proved at that raw level.

## Fragment coordinates and mixed original lengths

`prefixCoord j` maps earlier columns unchanged and the shared boundary to the last column `j` of a `j+1`-column cylinder. `suffixCoord k` maps the shared boundary to column 0 and suffix column `c` to `c+1` in a `k+1`-column cylinder.

The original prefix coordinates differ from the normalized prefix by shift 0; the original suffix coordinates differ from the normalized suffix by the old boundary index. `forward_iff_of_coordinate_shift` preserves row labels and applies a common nonnegative column shift. It preserves equal-column and consecutive-column relations exactly, and therefore all V/H/D forward edges and their reversed traversal. It does not identify columns cyclically or introduce the opposite diagonal orientation.

`suffixAmbient` excludes all boundary-to-boundary edges; the prefix owns those physical edges. Its definition remains valid at `k=0`, when there is no suffix interior and it has no edges. Prefix definitions similarly allow `j=0`. These degenerate fragment cases do not change `stateAt`'s separate requirement `k ≥ 1`.

For arbitrary permitted fragments, `glue_permitted_le_comap` sends every actual prefix or suffix edge to a legal edge under the canonical column-cut bijection. `transportedGlue` uses that bijection's embedding, so transport cannot collapse distinct vertices. In `mixed_cut_parts_le`, the prefix may come from total length `j+1+oldSuffix` and the suffix from `oldPrefix+1+k`; the result has length exactly `j+1+k`. Neither old length remains in the normalized fragment permission predicate. No matching-length premise or unproved locality assumption is hidden in that statement.

## Exact common-state proof

The concrete common raw state has horizontal mask true exactly on the first and last rows, diagonal mask constantly false, reachability constantly true, and assigned parity zero. This is equality of the entire `RawBoundaryState`, not equality of a projection or equivalence up to row rotation.

The two-column witness is evaluated at `j=0,k=1`; the three-column witness at `j=1,k=1`. Thus their boundary columns are respectively the first and middle physical columns, with the same row labels after encoding. The existing exact cut-edge formulas supply the horizontal masks and exclude diagonals because `rowSucc r ≠ r` for `m ≥ 3`.

The private `prefix_reachable_of_walk` lemma is substantive: every vertex of the supplied walk must lie in processed columns, and every edge must be selected in the target graph. It constructs preimages in the actual prefix coordinate map, proves a graph homomorphism from the walk's connected support subgraph, and maps reachability between the two boundary vertices. It does not invoke connectivity of the full cylinder to obtain a path that could leave the prefix. The two spanning prefix walks satisfy those hypotheses and contain every boundary row, giving the universal boundary relation.

The parity argument uses the stronger pointwise fact that every selected witness edge has zero meridian weight. It therefore proves every summand of the assigned-ID subset sum vanishes. It does not incorrectly infer prefix parity zero merely from total cycle parity zero. This covers the odd-width nonwrap diagonal and the `m=3` endpoint through the frozen witness lemmas.

The selected-walk helper accounts correctly for Mathlib's `fromEdgeSet` removal of `Sym2.IsDiag`: that predicate means a loop with identical endpoints, not a triangular-grid diagonal. Actual simple-graph walk edges have no such loops, so the selected graph has exactly the walk's unordered edge set.

`witness_states_eq` proves the two displayed encodings equal for every `n ≥ 2`, circumference `n+1`. `commonWitnessState_occurs` packages every original `m ≥ 3` via `n=m-1` and the actual perimeter Hamiltonian cycle. Neither theorem assumes a common state or a return transition as a premise.

## Replayed verification commands and results

Executed sequentially, with the prototype as working directory:

```bash
python verify_boundary_state.py
python verify_column_fragments.py
python verification/verify_common_witness_state.py
```

All three exited 0. Each uses `-DwarningAsError=true`. Boundary replay rebuilds `PhysicalEdges` and `BoundaryState` in `verification/boundary_state_replay`; fragment replay writes `verification/column_fragments_replay`; common-state replay rebuilds only its source and audit module in `verification/build`. Imported frozen sources were not edited or rebuilt by these commands except the explicitly replayed physical encoder/state modules in their separate directory.

| Replay | Audited results | Receipt | Rebuilt main olean SHA-256 |
|---|---:|---|---|
| Boundary state | 21 | `verification/boundary_state_receipt.json` | `af63e3a586cbcbd83b4ce65ad974fdf6335df1afa3d545d903bdda2cce54d2f7` |
| Column fragments | 11 | `verification/column_fragments_receipt.json` | `8f4f9daa4e691e7733b404c0e8fb15e75fb1cdea39e0be192139bd9e75ebc070` |
| Common witness state | 16 | `verification/common_witness_state/verification.json` | `29c30df896722a5c52cd08d512d620a1826c006bf998846c981fcc22469152b1` |

All 48 audited results have only standard axioms; the scripts reject unexpected theorem sets or axiom dependencies. Boundary and fragment scripts additionally require their specified exact axiom sets and output olean hashes. The common-state script records its current source/output hashes rather than hard-coding its own frozen source pin, and records compiled dependency hashes; I separately checked the requested source pin and all fifteen compiled imports against the pre-replay receipt. Both rebuilt common-state outputs matched their previous frozen hashes.

Verifier script hashes were respectively `52b98b4d9793469ed720cd262bdd91608623ced7eaaeb23a0e5d4899c10ae6cd`, `f6ef5578d3a70b08ef379fe49aba0dde52052bc2ef9a2e3991f50d435863cf8d`, and `d1e1494ace2b45d2cb6eb0922c07a28b7dd22450ac5417387310820700c83001`.

The three resulting receipts have SHA-256 `83def0c4f4d048f2bcb4181bf4775329f861f360c43f2c7a85d10a1a6c85f784`, `9880da59d5c32cafbf7c642f6f886ccefe4fcebc5a8b1d6d3666f55a31a48147`, and `133eaf44aab1870dca1f20c51a8cdc183d0ffd12774d69d65d255f7a80a616d3` at the time of this review. The pinned Mathlib definitions inspected include `Reachable`, `fromEdgeSet`, `Walk.toSubgraph`, its support/edge membership lemmas and connectedness theorem, `Subgraph.coe`, and `Fintype.ofInjective`.

This review establishes no complete transfer-state theorem, counting bijection, annular topology correspondence, or cylinder asymptotic theorem.
