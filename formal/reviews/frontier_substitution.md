# Independent audit: FrontierSubstitution

**Verdict: PASS.** All 184 lines of `FrontierSubstitution.lean` were read independently, and the exact source was replayed successfully into a newly created output directory with warnings treated as errors. No source, configuration, or dependency was edited. The formal statements match the requested generic prefix-replacement theorem for undirected simple graphs.

## Pins and compiler evidence

- Source: `/workspace/scratch/b9dece22c080/frontier_formalization_20261125/FrontierSubstitution.lean`, 8,234 bytes.
- Source SHA256: `7f8ddf84f64e47b4d9e0c8e76b9b6e1e0a1fac91b17dc9c041a360d5c60baf69`.
- Lean: 4.19.0, toolchain commit `6caaee842e94`, x86_64 Linux release.
- Mathlib commit: `c44e0c8ee63ca166450922a373c7409c5d26b00b`; tracked working tree clean before replay.
- Mathlib `lake-manifest.json` SHA256: `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`.
- Fresh replay started: `2026-11-25T01:01:48.520272+00:00`.
- Compiler: exit code 0, empty stderr, `-DwarningAsError=true`.
- Fresh output SHA256: `dbe41f37a477d769b289253292de66441d6e5a21f5d25dde2e8b78b4240f48ec` (258,704-byte `FrontierSubstitution.olean`).
- Receipt: `compiler-receipt.json`, SHA256 `b9edee72dacfdc09dfa97b48feaa9aba315a8102a7b9b8c1fece30e6cc24c695`.

The receipt records the full command, working directory, captured output, and `LEAN_PATH`. The latter came from `lake env printenv LEAN_PATH` run inside the pinned Mathlib directory, with this review's initially empty build directory prepended. The module output did not exist before compilation. Existing pinned Mathlib dependencies were reused; this is a fresh module replay, not a rebuild of the dependency tree. Source and manifest hashes were checked again after compilation.

Both main theorems printed exactly these axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency, and the source introduces no extra axiom or admitted proof.

## Mathematical interface audit

**Embeddings and glue.** `prefixEmbedding` sends interior vertices to the left summand and boundary vertices to the middle summand of `I ⊕ (B ⊕ O)`. `suffixEmbedding` sends suffix interior vertices to the right summand and boundary vertices to the same middle summand. Both are proved injective. Their images cover the ambient vertex type and intersect exactly in the common boundary. The glue is precisely the join of the two mapped simple graphs. Distinct boundary stubs remain distinct; several may share a suffix neighbor without violating any hypothesis. Shared boundary edges are harmlessly merged by the simple-graph join.

**Assumptions.** `TouchesBoundary P` is exactly the assertion that every prefix interior vertex reaches some boundary vertex, and the same condition is required for `P'`. `hBoundary` in the two final equivalences is exactly equality of the prefixes' boundary reachability relations. No condition is imposed on suffix components, graph finiteness, degrees, matching structure, or geometric embedding.

**Proof mechanism.** The source selects a reachable boundary anchor for every old prefix vertex, fixing existing boundary vertices. `replacement` sends old interior vertices to those anchors and fixes the entire suffix. An old prefix edge yields a reachable pair of anchors in `P`, hence in `P'` by the boundary assumption. A suffix edge remains a suffix edge. Reachability then transfers by reflexive-transitive closure. Every new interior vertex reaches a boundary point fixed by the replacement map, using the new prefix's attachment hypothesis. These facts establish preconnectedness transfer in either direction.

**Empty boundary and connectedness.** If `B` is empty, each attachment hypothesis forces its prefix interior type to be empty. Thus both glues reduce to the same suffix graph on `O`. The anchor function does not require an inhabitant of an empty type: its domain is empty in that case. The code assumes neither `Nonempty B` nor any ambient nonemptiness for the preconnectedness equivalence. For connectedness, `hconn.nonempty.map replacement` supplies target nonemptiness separately from the preconnectedness proof. If all vertex types are empty, both glues are vacuously preconnected and neither is connected. No empty-case exception is silently excluded.

## Scope

`glue_preconnected_iff` and `glue_connected_iff` prove the requested generic replacement claim. The one-way helper theorems also allow inclusion, rather than equality, of boundary reachability. The use of classical choice for anchors is explicit and reflected in the reported axiom list.

This certificate establishes a connectivity theorem for glued simple graphs. It does not formalize cylinder frontier encodings, selected-edge degree conditions, Hamiltonicity, transfer matrices, or a counting bijection. Applying it to those settings requires their separate interface and realization proofs. No alternate proof or additional theorem was added during this review.
