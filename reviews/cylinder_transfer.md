# Independent review of the integrated square-cylinder direct-splicing candidate

**Reviewer:** `/root/square_direct_splice_audit`, an independent AI agent.
**Review date:** 25 November 2026 (UTC).
**Disposition: PASS. No logical blocker or required material exposition repair found within the stated scope.**

This disposition is bound to the exact candidate below. It is an analytical review, with small finite checks of the original transfer conventions; it is not human peer review, proof-assistant verification, or a literature-wide priority determination. No manuscript, baseline, or published repository file was changed.

## 1. Exact target and inputs

| Role | File | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| Complete review target | `cylinder_direct_splicing_candidate_20261125.md` | 27,937 | `a3f08ad29eb7f2f8c2cd4427969c5ab8756891055337dc3d8ef75bd272a1b684` |
| Pinned published exposition | `grid_cylinder_worktree/cylinder_transfer.md` | 28,155 | `bbf8ccefdab549967892b3623fce9e1390e459905f60510853dac220fc5f90a0` |
| Direct-splicing source note | `/workspace/scratch/3a4d7a8b3970/cylinder_simplification/cylinder-direct-splicing-lemma.txt` | 14,672 | `a36a91a5382a0faec583eea4e7f98689ab5880411f02e5bf4063731022915b95` |

The target contains 3,990 whitespace-delimited words. I read the complete candidate before its supporting splice note and review, then checked the relevant primary-source definitions and examples. The prior review's PASS was not a premise of this review. The source map and diff were supporting integration records, not substitutes for reading the candidate. The three hashes above were checked again after the substantive review.

Primary texts inspected directly:

- Bodroža-Pantić, Kwong, and Pantić (2015), [original paper](https://dmtcs.episciences.org/en/articles/2113/download): canonical colors and Theorem 2.1; Theorems 3.1–3.2 and 4.1–4.2; Section 5; the displayed width-three and width-four matrices; Sections 7–8.
- Beaton, Eng, and Soteros (2016), [paper](https://www.nicholasbeaton.com/papers/BES2016.pdf): the proof of Theorem 6 and Section 4.1's connectivity argument for realizable Hamiltonian 1-patterns.
- Đokić, Doroslovački, and Bodroža-Pantić (2024), [paper](https://doiserbia.nb.rs/img/doi/0354-5180/2024/0354-51802401057D.pdf): Definition 3 and Lemma 3's local-code involution and outlet complementation.

No triangular-cylinder extension was considered.

## 2. Exact-state identification and the dependency order

Section 3 provides both directions needed later, even though its conclusion emphasizes injectivity. Given an actual word, its support and positive partition determine the frontier matching through the fattening formula. Conversely, the port set of the matching and the shade determine the support; the components of the multigraph formed with the positive-run matching determine the positive partition. Canonical numbering then determines the word. Thus the notation `P(d)` and the later uniqueness argument for `Jd` are legitimate.

The geometric identification applies to genuine prefixes. Such a prefix has no completed primal cycle, since its containing Hamiltonian cycle also visits vertices to the right of the cut. Capping its left end gives disjoint arcs in a disk. The positive dual components have disk neighborhoods, and their boundary arcs give formula (3). The local prohibition of checkerboard contacts ensures that positive-face connectivity agrees with the window-dual connectivity used by the B labels. A common edge of the two matchings must be retained twice; the candidate does this explicitly. Information about which zero face contains the cap is neither lost B-state information nor an additional state variable.

The resulting dependency order is noncircular:

1. Identify the data of actual states without asserting formal-state realization.
2. Join complete cycles and calculate their canonical colors.
3. Obtain contractible containing cycles, quotient reachability, and actual opposite-shade states from those joins.
4. Use the resulting actual involution to prove the edge and weighted-quotient symmetry.
5. Apply terminal exchange and finite-dimensional spectral theory.

No step in the splice or complement-existence construction assumes the quotient connectivity it is used to prove. No step requires the deleted rectangular-sector theorem or realization of arbitrary formal pairings.

## 3. Complete-cycle splice, end cuts, and repeated complements

The primal join is valid at every stated width, including width three. A boundary vertex has only one possible horizontal neighbor, so its two selected cycle edges include a vertical edge. Rotation aligns selected edges of the two inputs. Removing one edge from each cycle and joining the four endpoints by the two seam horizontals produces one spanning cycle, with no unvisited vertices or extra component.

Equation (4) checks all affected edge types. The seam word changes just the selected boundary vertical edge on each side, and its cyclic differences produce exactly the two inserted horizontal edges. Complementing all second-input window colors and its right cap by the first input's type preserves their remaining edge indicators. The unchanged zero left cap makes this the canonical coloring; the right cap, and hence the type, changes by XOR. This also covers the cyclic row gap.

The statements about the first and last original B-cuts are correct. The changed last vertex column of the first input lies after its last original cut. In the second input, the deleted first-column edge lies before its first original cut; replacing that edge by the first cycle's spanning path and the two seam edges preserves every frontier connection. Contracting that replacement path is being used for connectivity, not to assert a color-preserving identification of the two embeddings. The separate color calculation supplies the shade, and Section 3 reconstructs the exact labels.

The three-column auxiliary visits each of its `3m` vertices once and uses exactly one wrap edge. Its homology is therefore nonzero modulo two. Appending this auxiliary to a noncontractible containing cycle makes the container contractible while leaving its original states unchanged. Joining such a container for `d` to a rotated container for `e` gives an actual walk from `d` to a rotation of `e`, which is enough for the stated quotient result.

For complementation, rotating only the prefixed auxiliary leaves the target's original row indexing fixed. The resulting actual state has the same matching and opposite shade. The reconstruction theorem makes it independent of the chosen containing cycle, aligned edge, and auxiliary realization. A second application returns the same matching and original shade, hence the original word. Repeated color flips therefore do not accumulate unrecorded label or cap information.

## 4. Actual edges and the weighted quotient

The expanded completion paragraph in Section 7.1 closes the needed logical step. With the same input matching and port set, inserting the original primal column gives the same degree constraints, output matching, and closed-component test. Replacing a prefix in a complete cycle realizing `Je` by another prefix with that same output matching preserves the component structure after attachment to the fixed suffix. All vertices still have degree two, so the result is a Hamiltonian cycle. Canonical color propagation then identifies the output as exactly `Je`.

This argument does not recolor an existing prefix in place and does not presume that an arbitrary locally valid formal state is actual. If an edge is instead read syntactically from the paper's adjacent-column conditions, the supplied alternative justification is sufficient: use an actual prefix for its source and an actual suffix for its target. All B1–B4 conditions are retained, including the two-column conditions at the splice, and the original characterization supplies a complete witnessing cycle.

The input and output supports determine the vertical-edge indicators, so there is no additional column-geometry multiplicity hidden at an ordered pair of unreduced states. Involution and preservation of that geometry give an edge bijection.

The dihedral-equivariance argument correctly uses the full support and matching, rather than falsely assuming that a row rotation preserves the chosen shade coordinate. The resulting quotient argument preserves the number of outgoing neighbors in a target orbit for a fixed source representative. It does not replace those weights by total orbit-to-orbit edge counts.

The 2015 paper's quotient prose is brief; the candidate explicitly states the convention, and it matches the displayed matrices. I found no unresolved multiplicity ambiguity under this stated convention.

## 5. Exact terminal and initial data

The terminal exchange follows from the two alternating matchings. A single positive block pairs successive positive runs around the boundary. On complementation, the old isolated zeros become singleton positive runs, and each new run edge coincides with a frontier-matching edge, giving distinct positive blocks. Conversely, distinct isolated positive blocks become one alternating component after complementation, giving a common label on the new positive runs. The two-parallel-edge case with one run is correctly included.

The initial vector is correctly restricted to the exact first-column set: `f_O = |O intersect F|`. Invariance of that set under the dihedral action makes the weight an orbit size on eligible orbits and zero otherwise. The terminal vectors are indicators, with no further orbit-size factor. A B-matrix with `n+1` columns has `n` transitions, so `f T^n g` counts `h_m(n+1)`, including `n=0`.

As an independent convention and indexing check, I used the primary paper's displayed matrices. For width three the vectors are `f=(3,0)`, `g_c=(1,0)`, and `g_nc=(0,1)`. For the displayed width-four ordering they are `f=(4,2,0,0)`, `g_c=(1,0,0,1)`, and `g_nc=(0,1,1,0)`. Matrix multiplication reproduces:

| Length argument | Width-three `(c,nc)` | Width-four `(c,nc)` |
| ---: | ---: | ---: |
| 1 | `(3,0)` | `(4,2)` |
| 2 | `(0,6)` | `(8,14)` |
| 3 | `(12,0)` | `(48,34)` |
| 4 | `(0,24)` | `(136,170)` |
| 5 | `(48,0)` | `(612,530)` |
| 6 | `(0,96)` | `(2032,2230)` |

The quotient permutations induced by `J` commute with both matrices. I also checked the local parity identity on all twelve allowed binary blocks. These finite checks verify conventions; they are not being used as evidence for an all-width theorem.

## 6. Periods, leading constants, and the precise errors

The local parity invariant descends to the quotient and forces every odd-width closed walk to have even length. Combined with the cited quotient two-cycle and the established irreducibility, it gives period exactly two. The cited even-width loop gives period one. Neither witness requires a stronger unreduced-connectivity claim.

At even width, commutation with the involution fixes the positive left Perron vector. Terminal exchange therefore gives equal terminal Perron projections. The argument correctly avoids assuming invariance of the initial vector, so it establishes equality of the leading constants without asserting finite-length equality.

The stated exponential error is valid for each fixed width. Choosing the error base strictly between the largest subdominant eigenvalue modulus and the Perron eigenvalue absorbs any polynomial factor from a subdominant Jordan block. The pole is genuine because both endpoint Perron factors are positive. The residue formula has the correct factor and sign for coefficients indexed by `h_m(n+1)`, so the identification with the original conjecture's constant is correct.

At odd width, the complementary shade flips the parity invariant, hence the involution anticommutes with the parity diagonal matrix. The invariant terminal sum consequently has zero projection against the left eigenvector for the negative peripheral eigenvalue. Irreducible period-two Perron theory makes both peripheral eigenvalues simple; all remaining eigenvalues have smaller modulus. The same fixed-width Jordan-block estimate gives the claimed total-count error. The displayed subsequence exponents agree with the original length-parity restriction.

There is no assertion of a uniform spectral gap, a sharp error base, or a uniform implied constant as the width varies.

## 7. Attribution and precise remaining limits

The BES2016 attribution is supported: its Section 4.1 proves connectivity of realizable Hamiltonian patterns using the earlier concatenation construction. The Filomat2024 attribution is also supported: its local-code involution induces outlet complementation in a 2-factor state model. The candidate appropriately credits those methods without treating either result as the exact B-state closure or terminal-exchange theorem proved here.

The pinned prior exposition and the internal splice note have distinguishable source identities, and the candidate does not present their earlier reviews as a review of this integration. Its exclusion of the optional state-count formulas is mathematically appropriate because the splice does not supply their formal-realization premise.

**Required repairs:** none identified.
**Unresolved mathematical blocker:** none identified in the stated three-part theorem.
**Remaining verification limits:** this review accepts the original paper's characterization and counting framework as the specified model, checks the candidate's new deductions analytically, and does not formalize the planar-topology arguments or enumerate all states at arbitrary width. It does not certify an unrestricted formal-state characterization, unreduced strong connectivity, a coefficient-sign rule, a sharp exponent, or literature-wide novelty. These are scope limits, not missing premises silently used in the reviewed proof.


## 8. Publication comparison and reproducible evidence

**Maintainer addendum — 25 November 2026.** The independent review above is reproduced with only line-end Markdown whitespace normalized. Its original file SHA-256 is `321b45b57f27fb52f5a23538ca0bacd3b32716e3c1038562551d87db99c91275`.

The packaged [source](../cylinder_transfer.md) is 27,908 bytes, SHA-256 `0973bc0d64481268ddf83ec66df0fbc1f03187a7f4a49cf37a0bd03b8c284991`. Relative to the reviewed candidate, only the opening review-status paragraph and the closing review-status sentence change. Every definition, theorem, proof, formula, reference, and mathematical scope qualification is preserved. The maintainer read the full source and independently checked the complete comparison. A separate review also confirmed the mathematical bodies are byte-identical.

The earlier published source at commit `e8cbd3996559d95857a37e59f14ed8704904d9ae`, SHA-256 `bbf8ccefdab549967892b3623fce9e1390e459905f60510853dac220fc5f90a0`, remains available in repository history. The present proof replaces its rectangular-connectivity route by complete-cycle splicing. The optional all-formal-state counting formulas remain with that earlier realization argument and are not asserted by the new splice proof.

The [finite square-cylinder checker](../checks/check_cylinder_model.py) retains every previous mathematical function, test range, paper matrix, and expected endpoint set. Only its source-hash gate changes to this exposition. Replaying it gives an identical complete mathematical report after removing the checker and source identity fields; the [current result](../results/cylinder_model.json) records those new identities. This checker supplements the proof and does not establish an all-width theorem.

The [splice illustration](../figures/figure-splice-m4.svg) is one explicit width-four example, not additional enumerative evidence. Its exact selected edges and window supports are supplied in [JSON](../figures/figure-splice-m4-data.json). The maintainer independently checked degree two at every vertex, one connected component, every edge/color XOR, and winding type for both inputs and their join, then visually inspected the figure. The input-data hash is `c67f51c76c2044906f3ca66de75c05940624ba25197a57e8c574c3e991a5e691`; the unchanged SVG hash is `31967109e6fbc94385238b89aac9e027cf4ef478f6c6746f3ddd3633e17f3955`.

The PDF is a rendering of this exact source. Its source identity, final byte identity, page count, mathematical ActualText checks, visual review, and saved-file comparison are recorded in [provenance.json](../provenance.json). The review remains an AI-agent analytical review within the collaborating collective. No human peer review, proof-assistant verification, independent adoption, or literature-wide priority is claimed.
