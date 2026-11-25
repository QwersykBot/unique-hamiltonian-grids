# Concrete auxiliary-cycle statement-fidelity audit

Date: 2026-11-25. Reviewer: `/root/external_math_validation_route`.

## Verdict and independence scope

**Scoped pass.** The frozen `AuxiliaryCycle.lean` constructs exactly the released three-column auxiliary cycle for every circumference `m ≥ 3`. Its five principal results establish a standard Hamiltonian cycle in the concrete graph, combinatorial meridian parity one, the two exact boundary-gap characterizations, and an existence theorem quantified in the original circumference variable `m`. I found no blocking mismatch, hidden weakening, or necessary correction.

This is a separate source-level review of the concrete auxiliary instantiation and its statement fidelity. I authored the imported `EnumeratedWalk.lean` helper; this audit must not be represented as an independent review of that helper. Root is separately reviewing the generic constructor and rerunning the final dependency chain. I did not edit the reviewed sources, conduct finite tests, or rebuild them for this audit.

## Reviewed pins and evidence

All Lean modules below are under `/workspace/scratch/4a160f238522/cylinder_formalization_20261125/`.

| Module | SHA-256 |
| --- | --- |
| `AuxiliaryCycle.lean` | `1534298b48bf904d8d582f9e1394678fb1435955c684d23b05715b278c3b8589` |
| `MeridianClassifier.lean` | `f02907309c7dca23e85385c0eeaff89b0d323b005581ac4eea0f138e5b8ac5fb` |
| `EnumeratedWalk.lean` | `560bf7712190bb361701c93b2da3009f930d43651779283d6c351d006fe2d4ca` |
| `TriangularParity.lean` | `c5d90d59aa758f4074fc0a905c3c52ee8976fe1235fc8f9b55adc03ca355e8c3` |
| `TriangularCylinder.lean` | `6f4f4fe9f9603168ee6eb596a60a071e5471b992eddacb6d1c8a9ee26d47bf04` |
| `CylinderSplice.lean` | `d8c3e3445b48d56fc526985b798dcdcab05d7e4a3ecdf2154cb47942b9496cc4` |

Comparison source: `/workspace/scratch/4a160f238522/cylinder_revision_worktree/triangular_cylinder_asymptotics.md`, SHA-256 `94ea00f83be85f6bb87b7a7362861da9e0c92fa42c84a5930c8817db45460066`, displayed traversal (11) and its following boundary/parity assertions.

I read the complete auxiliary and classifier sources. The graph, parity, and standard Mathlib Hamiltonian definitions were inspected in the preceding statement-fidelity audit at these same dependency hashes. For the new cardinality bridge I also read the actual pinned `Fintype.bijective_iff_injective_and_card` theorem. The environment remains Lean 4.19.0, commit `6caaee842e94`, with Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Exact enumeration and traversal

Write the circumference as `m = n+1`, with `n ≥ 2`. Lean coordinates are zero-based. The domain of `auxVertex n hn` has `3n+3 = 3m` entries, and its cases are:

| Index range | Vertices in order | Number |
| --- | --- | --- |
| `0 ≤ i < n` | `(n,0), (n−1,0), …, (1,0)` | `n` |
| `n ≤ i < 2n` | `(1,1), (2,1), …, (n,1)` | `n` |
| `2n ≤ i < 3n+1` | `(n,2), (n−1,2), …, (0,2)` | `n+1` |
| `i = 3n+1` | `(0,1)` | `1` |
| Remaining index `i = 3n+2` | `(0,0)` | `1` |

The conditional bounds make every natural-number subtraction nontruncating on its intended segment. Each positive row in columns 0 and 1 occurs once; every row of column 2 occurs once; the last two entries supply the previously omitted row-zero vertices of columns 1 and 0. This independently explains the source's injectivity and equal-cardinality proof of bijectivity.

The cycle constructor starts at the final entry `(0,0)`, takes the closing edge to the initial entry `(n,0)`, then follows this tail. Translating each coordinate by one gives exactly

`(1,1), (m,1), …, (2,1), (2,2), …, (m,2), (m,3), …, (1,3), (1,2), (1,1)`.

There is no change of orientation, missing terminal vertex, or extra traversal multiplicity in this comparison. At `m=3`, equivalently `n=2`, the segment lengths are `2,2,3,1,1`; all segment transitions and the distinct closing row pair remain valid. The proof is uniform in `n` and does not rely on an unproved small-circumference exception.

## Adjacency and Hamiltonicity

Within each long segment, consecutive rows differ by one in an ordinary nonwrap vertical step. The four joins between segments are the horizontal steps `(1,0)→(1,1)`, `(n,1)→(n,2)`, `(0,2)→(0,1)`, and `(0,1)→(0,0)`. `SquareStep` expresses precisely these ordinary vertical or horizontal coordinate steps, and `squareStep_adj` proves that every such step is an edge of the actual `TriangularCylinder.graph`.

The final-to-initial edge `(0,0)→(n,0)` is the undirected reverse of the allowed cyclic row step `n→0`. It is established by `aux_closing_adj`, using the already defined graph's vertical edge theorem. Consequently, the witness lies entirely in the square-grid subgraph, as the released traversal does; the ambient graph still has the intended consistently oriented diagonals.

`auxiliaryCycle_isHamiltonianCycle` concludes Mathlib's `Walk.IsHamiltonianCycle` on `Vertex (n+1) 3`. Its inputs are only `n` and `2 ≤ n`. The proof supplies the concrete bijection and concrete adjacency data to the generic constructor. It does not assume Hamiltonicity, spanning coverage, or the existence of a desired witness. The enumeration has `3n+3` vertices and the closed traversal has the corresponding `3n+3` edges.

## Parity and exact boundary gaps

Every tail edge has row difference at most one. Since `n ≥ 2`, it cannot have unordered row pair `{n,0}`. `auxVertex_edgeWeight_zero` proves that its meridian indicator is zero. The closing edge has exactly that unordered pair and weight one. The sum over the exact constructed edge list therefore gives `auxiliaryCycle_typeParity = 1` in `ZMod 2`.

The classifier supplies a faithful split of `NextRow`: either ordinary successor, or last-to-first wrap. Its meridian-pair classification uses `m ≥ 3`, which excludes mistaking the reversed ordinary first gap for the wrap gap. No topological premise is imported into this arithmetic conclusion.

The boundary results are full equivalences for every positively oriented cyclic gap `NextRow r s`:

- At column 0, the selected ordinary vertical gaps have source rows `1,…,n−1`, and the closing edge supplies source row `n`. The only absent gap has source row 0. Thus `auxiliaryCycle_left_edges_iff` is exactly the manuscript's “every gap except 1.”
- At column 2, the descending traversal selects every ordinary gap with source row `0,…,n−1`. The wrap gap with source row `n` is absent. Thus `auxiliaryCycle_right_edges_iff` is exactly “every gap except m.”

The constructive membership witnesses also have the correct indices: `n−r−1` for a nonzero ordinary left gap, and `3n−r−1` for a nonwrap right gap. The absence proofs exclude the missing edge both from the closing edge and from all consecutive tail pairs. These are statements about the actual walk's undirected edges, and Hamiltonicity ensures the usual selected-edge interpretation.

## Original-circumference wrapper and remaining scope

`exists_three_column_auxiliary (m : ℕ) (hm : 3 ≤ m)` quantifies over the original `m`. It writes `m=(m−1)+1`, justified by `hm`, and obtains `n≥2`; it then supplies the same constructed walk in the same graph after substitution. The conclusion includes all four properties together: Hamiltonicity, parity one, exact left-gap equivalence, and exact right-gap equivalence. There is no remaining enumeration, adjacency, parity, or boundary-availability premise in this wrapper.

This establishes the unrotated auxiliary witness. Row-rotation transport and prescribed-gap alignment are separate obligations. The source does not formalize annular contractibility, actual frontier-state preservation, the parity involution on actual states, transfer primitivity, counting identities, or the limiting ratio. “Parity one” remains the precise verified claim.

## Compiler evidence inspected

The existing `verification/auxiliary_receipt.json` and `verification/AuxiliaryCycle.log` record a warnings-as-errors compile with exit code zero for the exact source hash above. All five printed results depend only on `[propext, Classical.choice, Quot.sound]`. The receipt also records the source and compiled-object hashes of all five local dependencies. I inspected the receipt and log without rerunning the compiler. The auxiliary and classifier sources contain no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` declaration.
