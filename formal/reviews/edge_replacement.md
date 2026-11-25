# Independent review: edge replacement and old-vertex reachability

Date: 2026-11-25. Reviewer: `/root/strip_ports`. Verdict: **PASS within the stated reachability scope.**

The reviewer read the entire frozen source, checked the mathematical meaning of its definitions and proof directions, and performed one isolated source-only compiler replay. The source and dependency configuration were not edited. This is an agent review and Lean compiler replay, not a human review or a novelty assessment.

## Frozen input

- Source: `../EdgeReplacementReachability.lean`, 5,793 bytes.
- SHA256: `f8572d7602babec2b81766aa7f2f053dfaf689b7f0b8029bf4a4e3269fd94547`.
- Namespace: `CylinderFrontier.EdgeReplacement`.
- Sole import: `Mathlib.Combinatorics.SimpleGraph.Path`.
- No local-module dependency.

The main theorem is:

```lean
old_reachable_iff (G : SimpleGraph V) (A : SimpleGraph N)
    {x y : V} (hxy : G.Adj x y) (hA : A.Connected)
    (a b : N) (v w : V) :
  (replacementGraph G A x y a b).Reachable (Sum.inr v) (Sum.inr w) ↔
    G.Reachable v w
```

The attachment theorem is:

```lean
gadget_reaches_left (G : SimpleGraph V) (A : SimpleGraph N)
    (hA : A.Connected) (x y : V) (a b n : N) :
  (replacementGraph G A x y a b).Reachable (Sum.inl n) (Sum.inr x)
```

The attachment theorem deliberately does not require `hxy`; its proof only uses connectivity inside the gadget and the left seam.

## Adjacency audit

`replacementGraph G A x y a b` has vertex type `N ⊕ V`. Its definition has exactly these cases:

| Endpoints | Selected adjacency |
|---|---|
| `inl n`, `inl m` | `A.Adj n m` |
| `inl n`, `inr v` | `(n = a ∧ v = x) ∨ (n = b ∧ v = y)` |
| `inr v`, `inl n` | The same seam condition |
| `inr v`, `inr w` | `G.Adj v w ∧ ¬((v = x ∧ w = y) ∨ (v = y ∧ w = x))` |

The old-old clause removes both orientations of the one unordered edge. It matches the meaning of `G.deleteEdges {s(x,y)}` using Mathlib's `SimpleGraph.deleteEdges_adj` and `Sym2.eq_iff`. No equality to `deleteEdges` is claimed as an additional exported theorem. The mixed clauses add only the prescribed two seams. The symmetry proof handles the two deleted-edge orientations explicitly; looplessness follows from `A` and `G`, since mixed endpoints are in different summands.

## Proof audit

### Replacement reachability implies original reachability

`collapse x` fixes every old vertex and sends every gadget vertex to `x`.

- A gadget edge collapses to reflexive reachability at `x`.
- The left seam collapses to reflexive reachability at `x`.
- The right seam collapses to `x` reaching `y`, or the reverse, using `hxy`.
- A surviving old edge is still an edge of `G`.

`collapse_adj_reachable` covers all four summand cases and both seam alternatives. The private `transport_reachable` applies the existing `Relation.ReflTransGen.lift'` through `SimpleGraph.reachable_iff_reflTransGen`. It therefore transports finite walks without incorrectly requiring the collapse to be a graph homomorphism. On old endpoints the collapse is the identity, giving the forward implication of `old_reachable_iff`.

### Original reachability implies replacement reachability

`seam_path` concatenates the reversed left seam, the image of the gadget reachability from `a` to `b`, and the right seam. It supplies a replacement route from old `x` to old `y`.

`old_adj_reachable` explicitly separates the two orientations of the removed edge from every surviving old edge. Removed edges use this route or its reverse; surviving edges use their unchanged adjacency. The same reachability-transport API then handles an arbitrary original walk. No hypothesis that `G` is connected is needed: the theorem preserves the full equivalence relation on old vertices, including graphs with several components.

### Every gadget vertex attaches to the old graph

`gadget_reaches_left` maps the gadget reachability from `n` to `a`, then follows the left seam to old `x`. This proves the stated attachment for every `n`.

## Degenerate cases and assumptions

- `a = b` is allowed. The internal gadget route may be the zero-length walk, leaving the two-seam detour. Under `hxy`, the old endpoints are distinct, so coincident gadget endpoints do not identify the two old endpoints or the two seam edges.
- Neither vertex type is assumed finite. `SimpleGraph.Reachable` is existence of a finite walk, and the proofs use only this notion, so they apply unchanged to infinite graphs.
- There are no public `DecidableEq` or `DecidableRel` assumptions. The local `classical` in `old_adj_reachable` only supports the case split on whether an old adjacency is the removed edge.
- The supplied vertices already inhabit both summands. No unmentioned nonemptiness assumption is used.
- `hxy` is material to the forward collapse argument: without an original connection between `x` and `y`, a new bypass could merge old components.

## Scope boundary

The source claims reachability and attachment only. It does not claim preservation of degrees, Hamiltonian cycles, geometric embeddings, or counted objects. In particular, connectedness of `A` permits extra branches and does not ensure appropriate gadget degrees. The module contains no finite-state enumeration and no cylinder-specific premise. No obstruction was found within its stated scope.

## Independent compiler replay

- Lean: `4.19.0`, compiler commit `6caaee842e94`.
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Mathlib manifest SHA256: `5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752`.
- Tracked Mathlib files were clean.
- The build directory `build/` was newly created for this replay.
- `LEAN_PATH` contained that fresh directory followed by the pinned Mathlib path, with no producer build directory or local-module dependency.
- The source was compiled once with `-DwarningAsError=true` and `--root` set to the parent project directory.
- Compiler exit code: `0`; stderr: empty; frozen source hash unchanged afterward.

The fresh compiled module is 167,176 bytes and has SHA256:

```text
23fd7e5dae51c77d18be340638a86e5ebdffda7e7743849bd3597ff0609d5b35
```

This exactly matches the producer's compiled module; the producer's `.olean` was not reused.

Axiom reports:

| Theorem | Dependencies reported by Lean |
|---|---|
| `old_reachable_iff` | `propext`, `Classical.choice`, `Quot.sound` |
| `gadget_reaches_left` | None |

The detailed command, environment, hashes, output, and freshness record are in `compiler-receipt.json`; compiler output is in `compiler.log`. Receipt SHA256:

```text
a40fafecfa0d2a80669d613e6842408faa3f4d96dbcf9e1986c72fbf13bfecfc
```
