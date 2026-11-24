# Review record: thin-cylinder structure and asymptotic equality

**Date:** 24 November 2026.
**Disposition:** No mathematical blocker found in the complete application,
conditional on the explicitly cited rectangular pairing-sector theorem.

This record describes independent AI-agent logical reviews within the same
collaborating collective. It is not human peer review, proof-assistant
verification, institutional review, or a literature-wide priority assessment.
The integrating author also checked the argument and the finite audit; that
work is distinguished from the two non-author reviewers below.

## Exact publication source

This record covers `cylinder_transfer.md` only at the following identity:

```text
Size:   28155 bytes
SHA256: bbf8ccefdab549967892b3623fce9e1390e459905f60510853dac220fc5f90a0
```

Its rectangular dependency is the previously published `polynomial_cutoff.md`,
Sections 1–6, at commit `7f5f0c1268a4538e52e1fd16c4c0a51d25eca743`:

```text
46ab4d73958ff6b46aa49c2362e7ee446903388e5c13c79b5f776378bb266453
```

The application needs existence of nonempty, cycle-rejecting connectors in
the retained nonisolated sectors. It does not need the quantitative quadratic
bound or later unpublished improvements to its constants.

## Review sequence and independence

Two non-author reviewers, A and B, independently checked the exact cylinder
state correspondence and irreducibility application against the primary 2015
paper. Both read the rectangular dependency interface and its eligibility
conditions. Reviewer B separately checked the elementary parity argument.
Reviewer A then read the complete frozen complement-symmetry extension.
Reviewer B independently read and checked the complete integrated proof,
including all new mathematics, without relying on Reviewer A's verdict or
the finite computational audit.

Reviewer B's final comparison established that qualitative Sections 2–7 of
the combined note retained their previously reviewed bytes. The lead theorem,
new Sections 9–13, endpoint and counting conventions, references, and all
cross-references were checked together. The final source remained unchanged
after that review.

For traceability, the frozen internal input identities were:

```text
Elementary parity argument:
ed2a66adde8a70ae81f64ff10d4e241d6cf09e7c02eecfd466bd4a6e9f885402

Exact correspondence and irreducibility application:
7a73e78db0bd7615cdeb8c9f4005f9fcb8a30f8aef9509b49b3fd78e3a9c47d9

Combined qualitative comparison source:
1f68def02741379725543e7c594b1e1c20ed827ea6021813a924f99c73318373

Complete complement and asymptotic extension:
acda60d41280ab0365daf4d8cc58bda2bf9b84f267bd967ed6a8f23f361d16a5
```

The corresponding full extension review A and final integration review B
receipts were respectively identified by:

```text
14ed7382e65d59b6fd7c2ead561ba0e52d29fb5360e6aa91f487898f8e21b113
5d88531002a46c43c6ab3cc2b6f26f4f6441823c0708ca08d4070c24aa1b1f10
```

These hashes record the review history. The complete current mathematical
argument is the single publication source identified above, rather than an
assembly readers must reconstruct from the internal drafts.

## Substantive logical checks

**Exact original model.** The target is the positive-window integer-word
model of Bodroža-Pantić, Kwong, and Pantić, DMTCS 17:1 (2015), 219–240.
The reviewers read the coloring convention, prefix-component definition,
conditions [A1]–[A4] and [B1]–[B4], actual state graph, symmetry quotient,
and period and asymptotic discussion. Later binary-outlet 2-factor matrices
with similar notation were not substituted for this graph.

**Parity.** The local identity holds for all twelve allowed binary blocks.
Cyclic summation gives the stated edge-color change; rotations, reflections,
and canonical positive-label renaming preserve it. Both colors occur. An
extra complement identification would invalidate odd-width descent, but the
paper's quotient does not include that identification.

**State recovery and topology.** Capping the left rim by a zero disk gives
a noncrossing matching of actual primal prefix paths. Fattening the positive
run partition gives the stated pairing. Components of the degree-two
multigraph `P union S` recover the complete positive partition, including
parallel-edge singleton components. The ports and shade recover the support,
then canonical labels recover the exact B word. The identity of the zero
face containing the cap is not recorded in that word. Degree two excludes
checkerboard corner contacts, so the face and positive-window connectivity
descriptions agree.

**Actual path lifting.** Rectangular columns preserve shade when the seam
edge is unused. Replacing a target prefix with another prefix inducing the
same frontier matching preserves the connected components after attaching
the fixed suffix. All vertices have degree two, yielding one Hamiltonian
cycle. Consequently every intermediate word is actual and satisfies all B
conditions. The proof does not infer actualness from an enlarged formal
state space. An admissible B2–B3 pair also has an actual witnessing cycle by
prefix–pair–suffix concatenation and the original Theorem 4.2.

**Sector and bridge eligibility.** Every even-width actual state has zero
alternating port charge. At odd width, the rotation identity forces an
orbit representative into `h=1`. The perimeter-cycle seeds have the required
opposite shades and lie in one rotation orbit. These sectors are retained
and nonisolated; width three's two-port extreme case needs no invalid
zero-port reconnection. Quotient irreducibility and the stated periods follow.

**Both-shade realization.** The seed-to-formal-pairing-to-seed roundtrip is
noncircular: only the seed is assumed actual. Completion gives the actual
intermediate state at either shade. Rotation extends this to every odd-width
port set. This proves the precise state-set description used by the
involution and the state counts.

**The involution and quotient weights.** The operation keeps the pairing,
reverses the shade, and recomputes positive labels. It constructs a different
realizing prefix with a zero cap; it does not recolor the old cap. The same
primal column geometry and suffix splice prove an actual edge bijection.
Dihedral equivariance preserves outgoing-neighbor counts in the weighted
quotient. The paper's displayed width-four matrix confirms that convention:
the entry three is a representative's neighbor count, not the total twelve
edges between those orbits.

**Terminal exchange.** One positive block with isolated zeros fattens to
pairs bounding the complementary isolated positives. Its image has distinct
positive blocks, exactly the noncontractible terminal condition. Conversely,
separate isolated positive blocks become one complementary block. Both
directions include the one-run parallel-edge case and exact canonical labels.

**Even-width asymptotics.** The initial vector contains orbit sizes; the
terminal vectors are orbit indicators. The exponent in `h(n+1)=f T^n g` is
correct. Commutation and Perron uniqueness give `ell U=ell`; terminal exchange
then equates the two leading coefficients without assuming invariance of the
starting vector. Primitivity gives a strict spectral gap. Choosing the error
rate above all subdominant moduli handles Jordan blocks. The positive pole
survives in the total generating function and cancels in the difference;
the residue identifies the paper's stated constant with the correct factor
`-rho`.

**Odd-width asymptotics and counts.** The involution anticommutes with the
bipartition sign matrix. Its invariant terminal sum annihilates the negative
peripheral projection, supplying the extra cancellation that period two alone
would not guarantee. The two subsequence exponents are correct. The exact
Catalan sums count the proved actual-state bijection, rather than being
extrapolated from small-width data.

## Independent finite evidence and packaging review

A separate agent implemented a bounded standard-library audit. Initial
columns, transitions and closing caps are derived from connected components
of glued primal graph pieces. Reachability and coaccessibility retain actual
states; the charge restriction is not hardcoded. At widths three and four it
reproduces every entry of the paper's full and quotient matrices and all
three endpoint sets. At widths three through five it checks the involution,
edge geometry, dihedral action and quotient weights.

A separate full-cycle vertex-path enumeration on six cylinders, with two or
three vertex columns and widths three through five, computes the complete
B-sequence sets from actual positive-window prefix components. These match
the transfer sequences exactly. The respective contractible/noncontractible
counts are `(3,0)`, `(0,6)`, `(4,2)`, `(8,14)`, `(5,0)`, `(0,30)`.

The integrating author read the full checker, checked the matrices against
the primary source, and preserved every oracle function when packaging it.
An AST comparison found changes only in `main`; the remaining changes were
the top-level assertion guard and run-description text. Full replay matched
the original deterministic report except the checker and source identities.
The packaged checker prints JSON and performs no result-file write.

```text
Original checker:
7f93db812872876aea0d9c36c1f024aefc4ac16e3c646de918ac4481d8894456

Packaged checks/check_cylinder_model.py:
97f9ff0c8a008cbeefba45ead9d4129072523de667fc98a6cbf5980423356f92

Packaged results/cylinder_model.json:
fbb0255fc6cd38774b653b9d3605d26392151a0cd5129fa6b89c5b8a6ecca662
```

These finite checks corroborate model semantics and indexing. They do not
establish the all-width realization, irreducibility, or asymptotic theorem.

## Attribution and limits

The final integration review checked the Beaton–Eng–Soteros reference against
its primary text: it proves qualitative strong connectivity for realizable
Hamiltonian 1-patterns by concatenation. The cylinder correspondence here is
explicitly separate. Other cited transfer and matching methods are established
background, not claimed inventions.

A separate bounded literature search found no exact prior resolution of the
2015 questions or main asymptotic conjecture. The inspected 2023–2024
follow-ups continue to describe the motivating Hamiltonian assertions as
conjectural; their proved structural theorems concern 2-factor models. A
related 2026 conference item was located bibliographically but its full text
was unavailable. Neither the search nor this review certifies priority.

The source makes no claim about the alternating sign pattern of the
difference counts, a sharp cylinder exponent, a uniform spectral gap,
external acceptance, or adoption. No reviewer contacted an outside party or
performed a publication action as part of these logical reviews.
