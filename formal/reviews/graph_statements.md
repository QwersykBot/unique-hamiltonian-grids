# Independent statement-fidelity audit: triangular-cylinder splice

Date: 2026-11-25. Reviewer: `/root/external_math_validation_route`.

## Verdict

**Scoped pass.** The reviewed concrete theorem states the intended complete-cycle splice on the consistently triangulated cylinder for every `m ≥ 3` and block lengths `a,b ≥ 2`. It concludes Mathlib's standard `Walk.IsHamiltonianCycle` on all vertices of the joined cylinder. I found no blocking mathematical mismatch or hidden weakening. The separately reviewed parity extension proves the intended finite mod-two edge identity, including the cyclic row gap.

This is an independent source-level audit of statement fidelity and the proof bridges used here. It is not human review, a new kernel-verification receipt, or verification of the full triangular-cylinder asymptotic theorem. I read the project sources and the pinned upstream definitions, inspected the existing compiler receipts and logs, and independently rechecked their source hashes. I did not edit the three reviewed files or rerun the already passing build.

## Exact reviewed objects

Project directory: `/workspace/scratch/4a160f238522/cylinder_formalization_20261125/`.

| File | SHA-256 |
| --- | --- |
| `CylinderSplice.lean` | `d8c3e3445b48d56fc526985b798dcdcab05d7e4a3ecdf2154cb47942b9496cc4` |
| `TriangularCylinder.lean` | `6f4f4fe9f9603168ee6eb596a60a071e5471b992eddacb6d1c8a9ee26d47bf04` |
| `TriangularParity.lean` | `c5d90d59aa758f4074fc0a905c3c52ee8976fe1235fc8f9b55adc03ca355e8c3` |

The first two files were the original review request. Their owner froze them during review and supplied the third as a separate incremental extension. Exact-byte review copies are in `/workspace/scratch/4a160f238522/triangular_formal_statement_audit_snapshot_20261125/`.

The local Mathlib checkout is at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with no tracked changes when checked. The toolchain file says `leanprover/lean4:v4.19.0`; the local binary reports Lean 4.19.0, commit `6caaee842e94`. The released manuscript used for comparison is `/workspace/scratch/4a160f238522/cylinder_revision_worktree/triangular_cylinder_asymptotics.md`, specifically its graph definition, meridian parity definition, and complete-cycle splice lemma.

## What the concrete theorem says

Choose cyclically consecutive rows `r,s`, with `NextRow r s`. In the left cylinder, supply a Hamiltonian cycle starting with the vertical edge from `(r,a−1)` to `(s,a−1)`; its remaining path is `p`. In the right cylinder, supply a Hamiltonian cycle starting with the oppositely traversed vertical edge from `(s,0)` to `(r,0)`; its remaining path is `q`.

Embed the left cylinder in columns `0,…,a−1` and the right cylinder in columns `a,…,a+b−1`. The constructed traversal is:

1. the row-`r` horizontal seam from the last left column to the first right column;
2. the translated remaining right path `q`;
3. the row-`s` horizontal seam back to the left cylinder;
4. the remaining left path `p`.

`spliceAt_isHamiltonianCycle` proves that this traversal is a Hamiltonian cycle of the entire length-`a+b` cylinder. `spliceAt_typeParity` separately proves that its combinatorial wrap-edge parity is the sum of the two original cycles' parities in `ZMod 2`.

## Fidelity checks

### Graph and indexing

`Vertex m L = Fin m × Fin L` is the complete labeled vertex set, without a quotient. The translation to manuscript indices is `(r,c) ↦ v_(r+1,c+1)`.

`NextRow r s` means `s.val = (r.val+1) % m`. Thus the row step includes `m−1 → 0`. The column relation uses ordinary natural-number equality `c+1=d`, so it introduces neither column wrap nor long edges. `Forward` has exactly these three alternatives:

| Alternative | Manuscript edge family |
| --- | --- |
| Same column and one positive cyclic row step | `V_(i,j)` |
| Same row and column increases by one | `H_(i,j)` |
| One positive cyclic row step and column increases by one | `D_(i,j)` |

The graph symmetrizes this relation. This permits reverse traversal of each undirected edge; it does not introduce the other diagonal slope. For vertices in distinct columns ordered from left to right, only the forward alternative with increasing column can apply. At `m=3`, the vertical graph is the ordinary three-cycle, and the same diagonal description remains valid. The `m=2` embedded multigraph convention is outside these files' domain, consistently with their explicit `m ≥ 3` assumption.

### Coordinate embeddings and coverage

I checked Lean's actual `Fin.castAdd` and `Fin.natAdd` definitions: the former preserves the value and enlarges its bound, while the latter adds `a` to the value. Therefore `leftVertex` and `rightVertex` are exactly the intended block inclusions.

Both inclusions are proved injective. The `forward_left_iff` and `forward_right_iff` theorems preserve and reflect the edge formulas within their images, although the packaged maps have graph-homomorphism type. `left_ne_right` proves the images disjoint, and `vertex_partition` proves that they exhaust the full joined vertex type. These are proved facts, not extra premises of the concrete Hamiltonian theorem. No topological embedding of these graphs into an annulus is constructed here.

### Deleted edges, seams, and full Hamiltonicity

The removed edges lie at the last left column and first right column at the same actual cyclic gap. `horizontal_seam` proves adjacency across columns `a−1` and `a` using `(a−1)+1=a`. `NextRow` implies `r ≠ s`, so the two seam rows are distinct. The orientations of `p`, `q`, the two initial deleted edges, and the seams fit the traversal exactly, including when `r=m−1,s=0`.

The pinned Mathlib definitions inspected were `SimpleGraph`, `Walk`, `Walk.support`, `Walk.edges`, `Walk.tail`, `Walk.IsPath`, `Walk.IsCycle`, `Walk.IsHamiltonian`, `Walk.IsHamiltonianCycle`, and the walk-mapping lemmas. In particular:

- `IsHamiltonian p` requires `p.support.count x = 1` for every vertex `x` of the ambient type.
- `IsHamiltonianCycle p` extends `p.IsCycle` and requires its tail to be Hamiltonian.
- `IsCycle` includes a nonempty edge-simple closed traversal and no repeated vertex after removal of the initial occurrence of its basepoint.

Consequently, the conclusion is a standard spanning simple cycle, not merely a closed walk, a 2-factor, or a cycle on a selected subset. The concrete proof obtains spanning remaining paths from the two input Hamiltonian-cycle tails, maps their cycle properties by injectivity, and derives ambient support disjointness and coverage from the block lemmas. It does not attempt to infer Hamiltonicity in the larger vertex set solely from an injective graph homomorphism.

The generic edge-list and edge-set theorems describe precisely deletion of the two designated edges and insertion of the two seams. The set-difference statement uses the input cycle property to exclude a second occurrence of either deleted edge. It therefore agrees with the manuscript's edge-set surgery for these cycle presentations.

### Combinatorial parity extension

`meridianWeight` maps the unordered endpoint pair to its unordered row pair and tests equality with `{m−1,0}`. On the reviewed graph with `m ≥ 3`, these are exactly the wrap vertical and wrap diagonal edges. All horizontal edges have weight zero. I checked the pinned `Sym2` definition as pairs modulo swapping and the `ZMod` definition and ring instance; the target is actual arithmetic modulo two.

The embeddings leave row pairs unchanged. The two removed vertical edges therefore have equal weight, and their sum vanishes in `ZMod 2`. The two inserted horizontal seams each have weight zero. `splice_meridian_balance` proves this concrete balance, discharging the premise that was left explicit in the generic additive-weight theorem.

`spliceAt_typeParity` holds even for arbitrary paths `p,q` of the stated endpoint types. This is appropriate: additive bookkeeping does not require Hamiltonicity. The separate Hamiltonian theorem supplies that property when the inputs are Hamiltonian cycles. No contractibility predicate is used or proved by the parity extension.

## Remaining obligations and exact scope

There is no necessary correction to the reviewed statements. The following bridges remain necessary before treating this work as a formal proof of the cylinder ratio theorem:

- **Input availability and presentation.** The current splice takes a common selected boundary gap as data and cycles already presented with that edge first. Existence of suitable cycles, selection or alignment of gaps, and rebasing/reversing an arbitrary cycle containing a selected edge are not established by these files.
- **Cycles as counted objects.** The manuscript counts undirected selected edge sets without traversal multiplicity. These files construct walks and record their edge sets; they do not yet formalize the counting type or its relation to Hamiltonian-cycle presentations.
- **Actual frontier states.** No definition or preservation theorem for frontier edge sets, pairings, assigned prefix parity, or actuality appears here. In particular, the manuscript's state-shift formula under splicing remains outside this verification.
- **Topology and exceptional width.** The equivalence between wrap-edge parity and annular contractibility is not formalized. Neither is the `m=2` multigraph calculation.
- **Enumeration and limits.** Witness families, the isolated two-column state, connectivity and period arguments for the actual-state transfer, counting identities, and the limiting ratio are not consequences already present in these sources.

These are transparent scope limits, not hidden hypotheses smuggled into the proved splice. The source comments largely state this scope accurately. Public descriptions should retain “given cycles containing the designated common boundary edges” and “combinatorial parity” until the corresponding additional bridges are proved.

## Verification evidence examined

I inspected `verification/graph_receipt.json`, `concrete_receipt.json`, `parity_receipt.json`, and their corresponding compiler logs. Each records exit code zero with warnings treated as errors and the source hashes above. The logged dependencies of the Hamiltonian and edge-set results are `[propext, Classical.choice, Quot.sound]`; the additive-weight and concrete parity results use `[propext, Quot.sound]`. The reviewed source files contain no `sorry`, `admit`, custom axiom declaration, or unsafe proof escape.

This audit independently checks mathematical statement fidelity and exact source identity. The compilation results in this paragraph are the inspected existing receipts, not a claim that this reviewer performed a fresh compiler run.
