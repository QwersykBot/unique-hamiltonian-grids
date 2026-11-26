# Elementary verification of the unique six-deletion cycle

This is the `k=3` instance of **Misha Lavrov's known construction** for
`M(4k,4k) <= 2k`, given in his [25 October 2025 answer to the original
square-grid question](https://math.stackexchange.com/questions/5103789/minimum-of-black-squares-to-guarantee-uniqueness-of-loop-visiting-all-white-sq).
His one-based deletions are `(1,4),(1,8),(1,12),(11,3),(11,7),(11,11)`.
After conversion to zero-based coordinates, the quarter-turn
`(r,c) -> (11-c,r)` gives the deletion set used here. The
[rectangular-grid question](https://math.stackexchange.com/questions/5109188/minimum-number-of-forbidden-cells-for-a-unique-loop-on-m-times-n-grid)
provides the broader problem context. The upper bound is established prior
work; this document explains its verification in the packet.

The upper construction deletes row-major vertices
`D = [0,48,96,22,70,118]` from the 12 by 12 grid. There are 138 retained
vertices. `verify.py` proves that their induced graph has exactly one
Hamiltonian cycle without searching for or counting Hamiltonian cycles.

## Invariant and propagation

The verifier maintains two undirected graphs on the retained vertices:

- `forced`: edges that every possible Hamiltonian cycle must contain.
- `available`: edges that any possible Hamiltonian cycle may still use.

Initially no edge is forced, and all grid edges between retained vertices
are available. The invariant is that every Hamiltonian cycle contains all
forced edges and uses only available edges.

The degree rules preserve this invariant:

1. If a vertex has only two available incident edges, both must be used.
2. If a vertex already has two forced incident edges, no other incident
   edge can be used.

The verifier updates both endpoints when forcing or excluding an edge and
repeats these rules to a fixed point. A forced degree above two or an
available degree below two is treated as a contradiction, never as a
successful uniqueness proof.

## Excluding edges that would close a proper cycle

After degree propagation, consider an available but unforced edge `uv`
whose endpoints are in the same connected component of the forced graph.
If that component does not contain all 138 retained vertices, `uv` cannot
belong to a Hamiltonian cycle.

Indeed, the forced component already contains a path from `u` to `v`.
Adding `uv` would close a cycle wholly inside that proper component. All
of those edges would then have to occur in the proposed Hamiltonian cycle,
which cannot also span vertices outside the component. Thus excluding `uv`
preserves the invariant. A proper forced component already forming a cycle
is rejected as a contradiction.

The verifier excludes every such edge, repeats degree propagation, and
continues until no exclusion applies. Edges only become forced or
unavailable, so this process terminates on the finite grid. It never makes
a discretionary edge choice or branches.

## Existence and uniqueness

For this particular deletion set, the process ends with exactly two forced
incident edges at every retained vertex. The verifier then constructs the
forced edge mask and passes it to the unchanged independent
`check_certificate.validate_cycle` function. That function confirms that
the forced edges form one spanning cycle rather than several smaller
cycles. This proves existence.

By the invariant, every Hamiltonian cycle must contain every forced edge.
The forced edges already give degree two at every retained vertex, so no
different Hamiltonian edge set is possible. This proves uniqueness.

The verifier also checks the saved explicit upper witness and requires its
edge mask to equal the forced mask. The supplied frontier counter can be
run as an optional independent cross-check with `--frontier`; it is not
loaded or needed for the main proof.

The recorded verification took three outer propagation rounds and excluded
four proper-subtour-closing edges. It forced all 138 cycle edges. In the
certificate's full-grid edge order, the resulting mask is:

```text
aabbbbbba08889ceeeecc22223bbbbba08889ceeeecc22223bbbbba08889deeeec
```

The actual upper-check result and source hashes are included in
`data/upper-check-report.json`.

Combined with the complete lower-bound certificate explained in
`CHECKER_PROOF.md`, this elementary upper verification gives `M(12,12)=6`.
Sample mode establishes the upper result but does not establish complete
lower-bound coverage or equality.
