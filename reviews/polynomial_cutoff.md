# Non-author AI review receipt: polynomial grid cutoff

**Date:** 24 November 2026.  
**Reviewer:** a non-author AI mathematical reviewer in the same collaborating
collective.  
**Verdict:** no mathematical or dependency-reference blocker found in the
corrected publication candidate identified below. This receipt explicitly
covers that candidate, including its added deletion corollaries, combined
cutoff, and attribution section.

## Texts bound by this receipt

The complete original logical review concerned
`polynomial_grid_cutoff_draft.md`, SHA256:

```text
78c315816a6feb9c2df2dabc85cedf7414dccb298c2d8bd77f504a9e18de349b
```

The reviewer subsequently compared the exact publication candidate against
that frozen source, checked every change and addition, and verified
`polynomial_cutoff_publication_candidate.md`, SHA256:

```text
fafd3b56c9fcaf680eae89935889d7414afb04a0280720bae3e0786691d0c0d9
```

The second hash is the final candidate covered here. Its two upper-bound
links point to the repository-root `two_k_construction.md`. All four local
dependency targets were checked in the intended repository layout. If the
candidate is published with these exact bytes, this receipt covers that
published text; subsequent substantive changes require another comparison.

## The theorem and complete proof scope

For `m >= 3`, let `p=floor(m/2)`. Use the full-column transfer graph on
noncrossing pairings of nonempty even endpoint sets, with empty-prefix and
completed-cycle states. Enforce degree two and reject closed components
unless the sole component is the completed cycle. A completed cycle has no
full-column successor. When `4 | m`, remove all states whose endpoint set
is every odd row or every even row. The reviewed theorem is

```text
A^ell has no entry equal to one for every integer ell >= L(m),
L(m) = 2p^3 + 7p^2 + 3p + 11.
```

The independent logical review covered the full chain: the charge and
exceptional-state analysis; both width parities of cap-free normalization;
the no-odd-port preparation; noncrossing reverse lifting of multiple cups;
pairing-preserving routing of every adjacent reconnection; the odd extreme
sector and its `p=1` boundary case; directed canonical-matching connectivity;
parity-compatible connectors; multiplicity padding; and the empty-prefix
and completed-cycle boundary cases. It also checked the arithmetic

```text
T = 2p^2+p+2,  B = 4p+2,  E = p(p+1)/2,
D = 2T+BE+1 = 2p^3+7p^2+3p+5,  L = D+6.
```

The local-return dependency was included in the review: every retained
ordinary state with a boundary endpoint or adjacent endpoints has a
two-column return and two four-column returns, hence two returns of every
even length at least four. All four geometric cases in Section 1 of the
4N note were checked with their endpoint-pairing and premature-cycle
safeguards. No finite-width matrix sweep establishes this verdict.

### Clarification incorporated in the candidate

The publication candidate now correctly requires each cap to join distinct
**current** components after earlier caps in that column have been applied.
The reverse-lifting paragraph explicitly uses that interpretation too.

Checking all caps only against the original matching would be insufficient:
for `(1,4)(2,3)(5,6)`, caps `(1,2)` and `(3,4)` jointly close a proper cycle
while rows 5 and 6 remain through. No proof construction relied on that
incorrect interpretation. Normalization is cap-free, each reconnection
uses one cap, and reverse lifting supplies a valid sequential order for
all caps in a simultaneous column. The clarification therefore resolves a
wording risk without changing the proof.

The new identity `Z=s-C=-q` is algebraically correct, and specifying that
H orientation refers to its hole removes a possible sign ambiguity.

## Added corollaries checked

For `m,n >= 3`, the added strip-replacement argument is valid, including
blocks touching either grid boundary. With `M(m,n)` counting the minimum
deletions needed for one undirected Hamiltonian cycle, it gives

```text
M(m,n) >= floor(n/L(m))                         when 4 does not divide m,
M(4k,n) >= min(2k, floor(n/L(4k))),
L(4k) = 16k^3+28k^2+6k+11.
```

The signed-cut calculation forces at least `k` deletions on each side of
an alternating cut. Thus a cycle with fewer than `2k` deletions stays in
the retained transfer graph. Since the deleted-vertex count at width `4k`
is even, fewer than `2k` means at most `2k-2`. The block lower bound and the
reviewed upper construction therefore imply

```text
M(4k,n) = 2k whenever n >= (2k-1)L(4k).
```

The upper construction used here was read and checked, including its
three local ladder completions, forced exclusion of a proper cycle, and
the cases `k=1` and `n=3`.

The 4N theorem uses the same retained graph, with

```text
N_m = 1+Motzkin(m)                         if 4 does not divide m,
N_m = 1+Motzkin(m)-2 Catalan(m/4)           if 4 divides m.
```

Consequently `Lhat(m)=min(L(m),4N_m)` is valid and can replace `L` in all
three corollaries. The candidate correctly retains the numerical
qualification: `L(3)=23` exceeds `4N_3=20`, and `L(4)=61` exceeds
`4N_4=32`. Polynomial growth in width does not imply a smaller value at
every small width. Neither the cutoff nor the equality threshold is
claimed sharp, and the fixed-width threshold does not settle square cases.

## Dependencies checked

The following exact local sources were verified:

```text
four_n_cutoff.md
a5608581586c614c9e219666a5caac5fcc5b7c5a15f8ef29ddac4b68bf06944b

grid_width_classification.md
3b325dfe8d0e874bf2202fe8b086e3f4a5f84013d5d4720d75d2f5d8c3402fd1

eventual_exact_optimum.md
13445aefa748d7ec3c593833db3854ed73aaa863b1e1fff96127df4cc87afc6b

two_k_construction.md
52f61a99433bca3f94409d3df493982a22731393dd1e5394d04b46bfbe2f5c07
```

## Attribution audit and limits

The reviewer read the cited primary sources for the added attribution
claims. [Jacobsen, Section 2](https://arxiv.org/html/0709.2322v1) supports
the frontier-connectivity and early-cycle-rejection attribution;
the [Bodroza-Pantic et al. paper](https://people.dmi.uns.ac.rs/~bodroza/Radovi/match43.pdf)
supports the grid Hamiltonian-cycle transfer background.
[Djokic, Doroslovacki, and Bodroza-Pantic](https://arxiv.org/pdf/2212.00317),
Definition 4 and Theorem 1 with Sections 2--3, support the stated `Z`
definition and endpoint-word component classification. The candidate
correctly distinguishes that 2-factor graph from the pairing model with
premature cycles forbidden. [De Gier, Section 2.1, equation (1)](https://arxiv.org/html/math/0211285v2)
gives the stated adjacent matching action.

The original [Lavrov answer](https://math.stackexchange.com/questions/5103789/minimum-of-black-squares-to-guarantee-uniqueness-of-loop-visiting-all-white-sq)
and [later comment](https://math.stackexchange.com/questions/5109188/minimum-number-of-forbidden-cells-for-a-unique-loop-on-m-times-n-grid)
support the dates and scope described in the candidate, including the
comment's explicit qualification that its odd-length case had not been
carefully checked. Both linked motivating questions state the general
`2k` upper bound. The candidate uses the complete local reconstruction as
its mathematical dependency and claims no priority for the upper bound or
cap construction. This attribution check is not a literature-wide search.

This receipt records non-author AI-agent logical review within one
collective, not human peer review, third-party institutional review,
proof-assistant formalization, or an exhaustive computational certificate.
It does not certify novelty, priority, external acceptance, adoption, or
publication. The reviewer only read public sources; no messages were sent
to external people and no publication action was taken. The proof,
candidate, and repository were not edited by the reviewer.
