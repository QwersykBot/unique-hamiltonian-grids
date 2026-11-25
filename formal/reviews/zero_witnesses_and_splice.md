# Statement-fidelity audit: zero-parity witnesses and selected-edge splice

**Verdict: scoped pass; no statement-fidelity blocker found.**

This read-only review covers all six frozen sources below, the relevant imported graph/parity/splice definitions, pinned Mathlib predicates, and manuscript Lemmas 4 and 8. I authored none of these six modules. I did author the imported `EnumeratedWalk` helper: this is an independent review of the concrete instantiations and new presentation bridge, **not an independent audit of that helper**. No source was modified, build rerun, or finite enumeration performed.

## Source pins

All Lean modules are in `/workspace/scratch/4a160f238522/cylinder_formalization_20261125/`.

| Module | SHA-256 checked against actual source |
|---|---|
| `TwoColumnWitness.lean` | `7ecffe0c3cfcdd1e59c5db320d66e8e4cb84ff13674ce09a1f67ddb8d567f622` |
| `ThreeColumnWitness.lean` | `8ed3868cc8cd2895d38f3454b5f2d875c1fe96874aa8bbf23c4b171d158ff970` |
| `TwoColumnWitnessCut.lean` | `b9166361488dcd53c43d648daf6855f991b3504873906dcf788aa2e2a6170b8f` |
| `ThreeColumnWitnessCut.lean` | `efec19cd70d75fc447a74621bb6f3ac366b5c0bdf442d4e48b8bdcdd985d341a` |
| `SelectedEdgePresentation.lean` | `73e7d6ee71952a53756f1fb1c62aff2d6389f8e323e032c52d63fc68dc8f8617` |
| `SelectedCylinderSplice.lean` | `22890cdb2c618ea2824cc46a4a7e34b23583d463ce2957714932d2596b32aaef` |

Comparison manuscript: `/workspace/scratch/4a160f238522/cylinder_revision_worktree/triangular_cylinder_asymptotics.md`, SHA-256 `94ea00f83be85f6bb87b7a7362861da9e0c92fa42c84a5930c8817db45460066`.

## Graph and standard predicates

Vertices remain `Fin m × Fin L`. `graph` symmetrizes cyclic verticals, ordinary horizontals, and diagonals whose row successor accompanies increasing column. Columns do not wrap. `UnrolledStep` adds only the nonwrap instance of that diagonal and its reverse traversal; it does not add the opposite slope.

The conclusions use Mathlib's actual `Walk.IsHamiltonianCycle`: a nonempty cycle whose tail visits every vertex exactly once. `IsCycle` enforces nonrepeated edges and distinct tail support. They do not use the separate graph-level singleton Hamiltonicity convention. `Walk.edgeSet` means membership in the unordered edge list; prefix `IsPath` means nonrepeating support. I read these definitions in `Hamiltonian.lean`, `Path.lean`, and `Walk.lean` under `Mathlib/Combinatorics/SimpleGraph/`, pinned commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Exact traversals, including odd circumference and m=3

Both constructions use `m = n+1`, `n ≥ 2`. The existential wrappers recover every `m ≥ 3` with `n=m-1`; there is no extra parity or width restriction.

The two-column enumeration is rows `0,…,n` in column 0, then rows `n,…,0` in column 1, closing horizontally in row 0. This is exactly the released rectangle perimeter, up to walk root. Bijectivity and actual graph adjacency are proved, not supplied as witness hypotheses.

The three-column enumeration first lists its left/middle prefix with row `floor(i/2)`. Before the final two rows, even rows occur as `M_r,L_r`, odd rows as `L_r,M_r`. Its final four prefix entries are always

`M_(n-1), L_(n-1), L_n, M_n`.

It then traverses `R_n,…,R_0` and closes horizontally to `M_0`. For even `m`, this is precisely the manuscript's paired insertion at the specified even one-based rows. For odd `m`, entry into the fixed tail is the one-based diagonal `L_(m-2)–M_(m-1)`, followed by `M_(m-1)–L_(m-1)`, exactly manuscript (14).

Substituting `n=2` symbolically gives the required one-based `m=3` traversal

`M_1, L_1, M_2, L_2, L_3, M_3, R_3, R_2, R_1`, closing to `M_1`.

There is no missing pair-insertion premise at this endpoint. Its diagonal has the allowed increasing-row/increasing-column orientation. All enumerated steps have equal or numerically consecutive rows and therefore avoid the meridian pair `{m-1,0}` for `m ≥ 3`. Whole-cycle parity-zero proofs include the odd diagonal and closing edge. These are combinatorial parity results; annular contractibility is not formalized here.

## Outer gap, exact cut mask, exact prefix restriction

`beforeLastRow m = m-2` and `lastRow m = m-1`, so the selected joining edge is the released one-based gap `m-1`. Both witnesses retain it in each outer boundary column. The three-column middle column is not mistaken for its right joining boundary.

Each `lastCut_edges_iff` quantifies over every pair of endpoint rows, not merely known horizontal candidates. It says a selected crossing exists exactly when the rows coincide and are first or last. Thus both designated cuts have exactly `H_1,H_m` and no selected diagonal, including no wrap diagonal.

The prefix statements are exact selected-edge restrictions:

- `perimeterPrefixWalk` is a path covering exactly column 0, with consecutive nonwrap vertical edges.
- `threePrefixWalk` is a path covering exactly columns 0 and 1, from `M_0` to `M_n`, with the initial enumeration's consecutive edges.
- Both `*_pair_edges_iff` lemmas prove both directions for every unordered pair of processed endpoints. They exclude additional selected cycle edges inside the prefix; they are stronger than a path-inclusion statement.
- Both prefix paths have parity zero. The outgoing crossings are horizontal and also have zero meridian weight.

These facts support the mathematical conclusion that the entire last processed column lies in one prefix component. The modules do not package a full-column state or its reachability relation. The existential witness wrappers export whole-cycle Hamiltonicity/parity, outer joining edges, and the cut mask; the exact prefix facts remain separate theorems about the named concrete cycles.

## Arbitrary-root presentation and original-edge-set splice

`edge_decomposition` derives a directed occurrence in one of two orientations from unordered selected-edge membership. `exists_edge_first` accepts an arbitrary standard Hamiltonian closed walk, rotates its cut, and reverses it when necessary. It derives the requested first-edge orientation and preserves the entire unordered edge list up to `List.Perm`. Its append-swap proof preserves trailhood, nonemptiness, tail-support distinctness, and the exact one-visit condition. Edge-set equality and every additive unordered-edge weight follow from the permutation.

`exists_splice_of_selected_edges` consequently has no edge-first input premise. It requires `m ≥ 3`, `a,b ≥ 2`, an actual cyclic gap `NextRow r s`, two input Hamiltonian walks at arbitrary roots, and membership of the aligned boundary verticals. The right input's selected edge is presented in the opposite orientation so that the remaining paths join through the two horizontal seams.

The output is a standard Hamiltonian walk on the full `m × (a+b)` graph. Its edge-set formula uses the **original** `A.map leftHom` and `B.map rightHom`: delete their selected verticals at columns `a-1` and `a`, respectively, and insert exactly the horizontal seam edges in rows `r,s`. The reversed endpoint order in the right deletion denotes the same `Sym2` edge. The proof explicitly maps the edge-list permutations before substituting the original input sets into the surgery equation.

Its parity is `typeParity A + typeParity B`. The two deleted aligned verticals have equal mod-two weights, while both seams have zero weight, including at a wrap joining gap. Mapped input walks are required only to remain cycles; the proof does not incorrectly assume either embedded input alone is Hamiltonian on the larger joined vertex set.

## Existing verification evidence and scope

I inspected `verification/zero_witnesses/verification.json`, `verification/selected_edge_receipt.json`, and `verification/selected_cylinder_receipt.json`. All six reviewed source hashes match their receipts. The witness receipt records five successful warning-as-error compilations, including its audit module, with exactly 26 standard-axiom reports. Presentation and splice receipts record successful warning-as-error compilation and only `propext`, `Classical.choice`, and `Quot.sound`. Recorded local dependency source/olean hashes, and the presentation/splice output olean hashes, match current files. No builds were rerun.

No correction is required for the reviewed statement fidelity. This pass does not assert formal common-state equality, preservation of old frontier states, formal length-2/3 state returns, a transfer/counting bijection, annular topology, or the cylinder asymptotic theorem.
