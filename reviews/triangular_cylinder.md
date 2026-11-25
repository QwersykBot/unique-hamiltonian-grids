# Independent review of the triangular-cylinder core and manuscript integration

**Reviewer:** `/root/square_direct_splice_audit`, an independent AI agent.
**Review date:** 25 November 2026 (UTC).
**Disposition: PASS for both exact texts below. No logical blocker or required material mathematical repair identified.**

The core establishes an all-width counting theorem for the specified consistently triangulated cylinder. It does not merely prove a Perron conclusion conditional on unproved matrix properties. The publication candidate retains the required premises, and its identification of the graph and length parameter with the 2018 counting problem is correct. The imported circumference-two formula completes the stated ratio result for that publication's full range.

## 1. Exact review targets and method

| Target | Bytes | Words | SHA-256 |
| --- | ---: | ---: | --- |
| `cylinder_general_splice_adversarial_review_20261125.md` | 19,493 | 3,128 | `6b2c31a4a92a4d12f9b313d7d0d0105ff33cdeec6650428f0a39e0754f2e0f44` |
| `triangular_cylinder_asymptotics_candidate_20261125.md` | 18,131 | 2,536 | `694c931230452c933fd37c716f8fd0e82ff8a65b957eb4398a2ab1fa04dbfb77` |

I read the complete core, independently checked its logical dependencies, and then read the complete publication candidate. The authors' and earlier reviewers' verdicts were not premises. I did not use the reported finite-state PASS, state counts, or whole-graph counts to establish any all-width assertion, and this review does not certify the separate finite-checker implementation.

For the publication identification I directly inspected the primary text of Bodroža-Pantić, Kwong, Doroslovački, and Pantić, *A limit conjecture on the number of Hamiltonian cycles on thin triangular grid cylinder graphs*, Discussiones Mathematicae Graph Theory 38 (2018), 405–427, DOI [10.7151/dmgt.2021](https://doi.org/10.7151/dmgt.2021), [primary text](https://bibliotekanauki.pl/articles/31342332.pdf). The relevant portions were Section 2, Sections 5–7, Section 6.1's circumference-two formula, and Conjecture 6. The previously inspected BES2016 and Filomat2024 primary passages also support the manuscript's bounded method attributions.

No frozen input, candidate, published repository, or external publication was modified. This review is bound to the two hashes above; subsequent additions require their own delta check.

## 2. The unique exception and the meaning of actual states

The exception argument is sound for every `m >= 3` in this exact graph. Without a selected first-column vertical edge, each first-column vertex must use its two available crossing edges. Those are precisely all `H_i` and `D_i`. They saturate the second column and form the displayed single zigzag cycle, since their alternating traversal advances the row index by one. No further column can belong to that Hamiltonian cycle. The same saturation argument applies at the right boundary without needing column reversal to be a symmetry of the oriented-diagonal graph.

The full frontier of `2m` selected crossing edges can occur at no later internal cut of a Hamiltonian cycle. It saturates the last processed column using outgoing edges alone, separating all earlier processed vertices from the frontier. Those earlier vertices would have to form closed components. Thus the full frontier occurs only after the first column, where both its matching and assigned parity are forced. The only actual state with that frontier is the stated `z`, and its parity complement is not actual.

The same degree calculation proves that `z` has no internal outgoing or incoming transition. At the next column, all vertices are saturated by incoming edges; conversely, producing the full outgoing frontier leaves no degree for an incoming frontier. Its only complete-cycle contribution is the single noncontractible two-column zigzag. Deleting it therefore removes exactly one two-column count and no count at three or more columns.

The definition of the retained set is essential and is used correctly. It consists of states realized at cuts of complete nonexceptional Hamiltonian cycles. It is not defined as all initially reachable formal prefixes with `z` removed. The argument makes no unsupported claim that a reachable prefix is completable. Dead reachable prefixes are outside the actual-state set and are not silently promoted to transfer states.

## 3. Individual stubs and assigned-edge parity suffice

The state contains enough information for an exact transfer. Every selected crossing edge retains its individual identity and its next-column endpoint. In particular, a horizontal and a diagonal entering the same unprocessed vertex remain distinct stubs. Processing that vertex then joins or saturates them according to its actual selected degree. Identifying such stubs before the vertex is processed would be incorrect; neither reviewed text does so.

The pairing records the connection between all unfinished prefix-path endpoints. Expanding a pairing edge back into its realized path changes neither the degree test nor the number of connected components after a continuation is attached. Internal closed components can therefore be detected from the pairing and the selected next-column edges. At termination, requiring one component and degree two at every vertex gives exactly one Hamiltonian cycle, with all old vertices represented by the expanded prefix paths.

Different prefix lengths or windings of individual paths do not invalidate substitution. The two realized pieces occupy disjoint column regions and meet through the same individually specified crossing edges. Their fixed planar embedding introduces no crossing or additional vertex identification. Graph connectivity determines whether the completed object is one cycle; its total edge-intersection parity determines its annular type. An embedded simple essential cycle in an annulus has odd meridian parity, so individual path winding numbers are unnecessary.

The parity coordinate is the parity of assigned full edges, not the geometric intersection count of a truncated path drawing. This distinction is handled correctly. A diagonal is counted when its left endpoint is processed, even if part of the edge lies beyond the current cut. On the next step it is incoming and is not counted again. Thus the stated increment counts only the new-column wrap vertical and outgoing wrap diagonal, and final closure adds only the final-column wrap vertical. Every selected edge contributes exactly once.

## 4. Exact splicing, parity closure, and full connectivity

The selected boundary vertical edges needed for a splice are available in every nonexceptional containing cycle by the exception lemma. Removing one selected edge from each of two cycles gives two spanning paths; the two seam horizontals join them into one spanning cycle. Unselected seam diagonals cause no problem.

At original cuts of the first input, all assigned edges and prefix connections are unchanged. Its modified last-column vertical lies after even its last old internal cut. At any original cut of the second input, its deleted first-column edge is replaced by a single path with the same two endpoints. This preserves the individual frontier and its pairing, including at the first and last old cuts.

The assigned-parity shift is exactly the type of the first cycle. Explicitly, the added complete first cycle contributes its total parity, the two removed verticals have equal meridian parity because their gaps are aligned, and the two added horizontal seam edges contribute zero. The two vertical contributions cancel modulo two. This verifies the claimed shift independently of the square-boundary description and includes the wrap gap.

The three-column auxiliary is valid also at width three. It uses every vertex once, has type one, omits only gap 1 on its first boundary, and omits only gap `m` on its last. For prescribed joining gaps, each end excludes at most one rotation. With at least three rotations, an auxiliary satisfying both end requirements exists.

Prefixing one auxiliary therefore supplies the actual opposite-parity state with precisely the same frontier and pairing. Its containing cycle has more than two columns, so it is retained. Since the state is literally the tuple `(S,P,t)`, applying this operation twice returns the original state; there is no additional label reconstruction or winding premise.

For full strong connectivity, the source and target containing cycles are not rotated. One auxiliary is inserted when the source type is one, and two are inserted when it is zero. Independent auxiliary rotations align every seam, while the complete piece preceding the target has type zero. Both exact endpoint states are therefore preserved. The joined complete cycle supplies a directed walk between arbitrary retained states. All its cut states are retained because it is a nonexceptional cycle with more than two columns.

This proves full, unreduced strong connectivity. No symmetry quotient, formal-state realization theorem, or inference from small-width enumeration is used.

## 5. The period witnesses work at every width

The two-column unrolled perimeter is a contractible Hamiltonian cycle with gap `m-1` selected at both ends.

The three-column construction is also correct. For even `m`, the paired detours insert exactly the missing middle vertices `M_2` through `M_(m-1)`. For odd `m`, those detours insert through `M_(m-2)`, and the final allowed diagonal detour inserts `M_(m-1)`. The last replaced left edge was not removed by a previous detour. Adjacent replacements may share an old endpoint, which does not invalidate successive insertion into a surviving cycle edge. At `m=3`, the single diagonal detour gives the required nine-vertex cycle. In all cases the construction uses no wrap edge and leaves gap `m-1` selected at both boundaries.

Self-splicing identical contractible copies preserves the same normalized old cut state in both copies. The separation is the number of vertex columns in a copy, giving closed walks of lengths two and three, respectively. It is not one less than that number. Strong connectivity makes the period common to the graph, and it divides both closed-walk lengths. Hence the period is one.

## 6. Exact counting, weights, and the positive common coefficient

The transfer weights count actual choices of next-column selected edges, including different geometries with the same resulting state. Initialization and termination are weighted in the same manner. Assigning every edge to exactly one column makes the sequence of these choices unique for each complete selected edge set. Conversely, a sequence counted by the matrix product expands to a degree-two spanning subgraph, with no closed component before termination and exactly one component at termination. It is therefore a Hamiltonian cycle.

There are `a-1` internal cut states on `a` vertex columns, so there are `a-2` internal transitions between initialization and terminal closure. The exact count is consequently `f T^(a-2) g_b` for `a >= 3`. The only missing two-column cycle is the excluded type-one zigzag, yielding the stated `+1` correction only for that count.

The same next-column geometry is valid when the stored parity is flipped: its degree and matching checks are unchanged, and its parity increment is unchanged. Actual complement closure ensures that both complementary endpoint states remain in the retained index set. Thus this is a bijection of the weighted transition choices, not just an isomorphism of the support graph. At termination it changes the final type and preserves the number of closing geometries. The commutation and terminal-vector identities follow.

All prerequisites for Perron theory are established for arbitrary fixed `m >= 3`: the actual set is finite, the graph is strongly connected, and its period is one. No explicit characterization or enumeration of all its states is required for those facts. The two-column contractible perimeter supplies nonzero initialization and contractible terminal vectors. Positivity of the left and right Perron vectors then makes the common coefficient strictly positive. The terminal-vector involution equates those coefficients without requiring symmetry of the initial vector.

The error estimate is precise for each fixed circumference. Choosing a positive error base strictly above the subdominant spectral radius and below the Perron root absorbs any nontrivial subdominant Jordan factors. The same leading coefficient holds for both types, so the ratio tends to one with exponentially decreasing relative error. None of this is conditional on a finite check or an unproved irreducibility assertion.

## 7. Publication integration and source identification

The publication candidate preserves all material steps from the core, including actual-state completion, individual stubs, the isolated exception, parity assignment, auxiliary-only rotations, both period witnesses, geometry multiplicities, terminal exchange, and the fixed-width error.

The primary 2018 paper defines its diagonal from `(i,j)` to `(i+1,j+1)` with cyclic rows, and its length parameter counts `n+1` vertex columns. Thus the manuscript's graph and substitution `a=n+1` are correct. The original problem counts the two types of Hamiltonian cycles, and the transfer reduction is a weighted counting device rather than a quotient of the cycles being counted. The manuscript's exponent `n-1` follows from its verified `a-2` exponent.

Section 6.1 gives exactly the imported circumference-two values and the equality `t_2^nc(n)=t_2^c(n)=2^(n+1)` for `n >= 2`. Retaining the embedded two-arc circumferential convention is necessary: collapsing those arcs to a single simple edge would already change the two-column count. The manuscript keeps the special case separate from the proof for `m >= 3`.

Conjecture 6 is precisely the ratio limit for every integer circumference at least two. The manuscript's conclusion therefore resolves that stated counting assertion under the publication's conventions. It does not thereby prove that its geometric transfer equals, is conjugate to, or establishes irreducibility of the publication's labeled transfer. The candidate expressly avoids those stronger identifications. Its remark about the original isolated labeled state is supported by Sections 6–7 and is not used as a correspondence theorem.

The method citations credit established pairing, concatenation, and complement ideas without claiming priority for them. No broader literature search or novelty certification is supplied by this review.

## 8. Disposition and exact limits

**Required mathematical repairs:** none identified.
**Unresolved missing premise:** none identified in either exact reviewed text.
**Scope:** the counting theorem for the consistently oriented triangular cylinder, with `m >= 3` proved geometrically and the publication's exact `m=2` formula imported separately.

This is an independent AI-agent analytical review, not human peer review or proof-assistant verification. It does not certify the finite checker, arbitrary augmentations of the grid, an unrestricted formal-state characterization, equality with the 2018 labeled matrix, or a uniform spectral gap. The circumference-two formula is a checked primary-source dependency rather than a new proof of that special case. These limits do not leave an unproved premise in the stated all-width ratio argument.


## 9. Publication comparison and independent finite audit

**Maintainer addendum — 25 November 2026.** The independent review above is reproduced with only line-end Markdown whitespace normalized. Its original file SHA-256 is `b29bd32595991eb558fbc07d9fe8631961abec09c444b94d0497091d148aabe5`.

The packaged [source](../triangular_cylinder_asymptotics.md) is 19,437 bytes, SHA-256 `94ea00f83be85f6bb87b7a7362861da9e0c92fa42c84a5930c8817db45460066`. Publication changes the date/status heading and review link and adds Section 8, a bounded-check report. The abstract, all formulas, and references are unchanged. Sections 1–7 are byte-for-byte identical to the reviewed candidate except for one explicit clarification in Lemma 3: the sentence referring to reversing the column direction is replaced by the direct observation that every right-boundary vertex has two incoming intercolumn edges and selecting them all saturates the preceding column. This states the same saturation argument without suggesting that column reversal alone preserves diagonal orientation. Independent reviewers recommended the clarification; the maintainer checked its exact content and the complete comparison. The maintainer also directly verified the original paper's model, index conversion, width-two formula, isolated-state discussion, and Conjecture 6. A separate final comparison checked the preceding version, SHA-256 `08a2fb5e50fc65e836ec0db99e39344b5fb3688282af24f5e21b7476302cc759`, then independently approved exactly this sentence substitution and the final source pin. Its dated comparison note has SHA-256 `c3a0e6d657d999938f08db8167eb4cd416ba34d4f05363d6956659605d7ea36f`.

The core proof's author obtained an additional independent review of the exception, state sufficiency, splice, period witnesses, and Perron argument. That review agrees with the complete non-author review reproduced above. No review verdict or finite enumeration is a premise of the all-width proof.

The finite verifier was separately implemented before its author read the supplied proof or existing enumeration code. It generates the full reachable closure from all first-column geometries, then computes terminal coreachability. This is not a sample of states observed up to a chosen length. Its whole-graph Hamiltonian vertex-path enumerator is independent of the transfer's legality, pairing, and connectivity functions.

| Circumference | Reachable | Reachable and completable | Retained after deleting z | Retained arcs | SCCs | Period |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 49 | 31 | 30 | 180 | 1 | 1 |
| 4 | 257 | 169 | 168 | 2,032 | 1 | 1 |

Every retained state is reachable from a retained initialization and can finish. Parity complement has no missing state, preserves every weighted transition, and exchanges the terminal vectors. The removed state has initial weight one, no internal incoming or outgoing arc, and terminal weights `(0,1)`. Its exact correction is one noncontractible cycle at two columns. The full and reduced transfers with that correction agree through eight vertex columns.

Independent whole-graph counts agree at `(m,a)=(3,2),(3,3),(3,4),(4,2),(4,3)`, with respective `(contractible,noncontractible)` counts `(6,10),(48,42),(312,318),(8,21),(200,124)`. The maintainer directly checked the same five rows in the primary paper's Tables 2 and 3, with `n=a-1`. The two- and three-column contractible witnesses and their self-splices were also checked through direct graph traversal and prefix-state extraction independent of the transfer connectivity routine. Partial-state rotations use the correct parity correction; the proof itself rotates only complete auxiliaries.

The maintainer read the complete original 830-line verifier and reran it. Its receipt and two canonical weighted-graph files were byte-identical to the author's frozen output. The original script hash is `c4d539389d24801d95637970b6119f35e1eb3eb308bbccb8226fd8bee85a2ad5`; its original receipt hash is `5894c83b65c0f77ae53c97083896e2f4a1622b6800c044e53b4f1f82bcb201fa`.

The packaged [checker](../checks/check_triangular_model.py), SHA-256 `2bad20a53a69d029b286dc293e3323612a4e9753631b23729bf17b326b6faa6e`, retains every mathematical function byte-for-byte. Its entrypoint is fixed to the audited ranges, emits one deterministic JSON object without writing files, and uses the repository's explicit optimized-interpreter rejection. Its [receipt](../results/triangular_model.json), SHA-256 `3ec21caefba67a2ba8abcb03e750c3ace91986b21110dd842541fb6f28d6bafd`, differs from the original only in the checker identity and added `status: PASS` field. Normal and optimized runs were both checked. These bounded checks do not prove the all-width result, identify a published labeled transfer, or establish a uniform spectral gap.

The PDF renders the exact packaged source. Final byte identity, page count, mathematical ActualText completeness, visual review, and saved-file comparison appear in [provenance.json](../provenance.json). This is AI-authored research with internal independent AI-agent review. No human peer review, proof-assistant verification, independent adoption, or literature-wide priority is claimed.
