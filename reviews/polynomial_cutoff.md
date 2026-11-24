# Final non-author AI review receipt: polynomial grid cutoff

**Date:** 24 November 2026.

**Verdict:** no mathematical or dependency-reference blocker found. This
receipt covers the complete integrated proof, both polynomial cutoff
bounds, their minimum with the 4N bound, and all stated deletion corollaries.

## Publication identity

The proof covered by this receipt is to be published as
`polynomial_cutoff.md`, with exactly the following reviewed bytes:

```text
Size:   35468 bytes
SHA256: 46ab4d73958ff6b46aa49c2362e7ee446903388e5c13c79b5f776378bb266453
```

These are the bytes of the final source `polynomial_cutoff_final.md`.
The reviewer verified that its only differences from the reviewed
integrated candidate are the header and footer's accurate review-status
statements. No mathematical argument, formula, reference, or corollary
changed in that last step. The receipt covers a published
`polynomial_cutoff.md` only if it has this exact hash; it does not itself
certify that publication has occurred.

## Review history and method

The same non-author reviewer completed the original proof review, reviewed
the sequential-routing refinement independently, compared the integrated
text against both reviewed inputs, and finally checked the status-only
revision. The source identities are:

```text
Initial complete cubic draft:
78c315816a6feb9c2df2dabc85cedf7414dccb298c2d8bd77f504a9e18de349b

Reviewed cubic publication candidate, including corollaries:
fafd3b56c9fcaf680eae89935889d7414afb04a0280720bae3e0786691d0c0d9

Complete sequential-routing refinement:
b4decfc6a9b699cfde088cd30fba61ceec4535169f613afbafa6aa165bf38827

Integrated comparison candidate:
5bc027d51cbc104d332db1d75dbcded0ec889e7fcdbab7c7da1ae6a3b42d8c53
```

The integrated Sections 1--4 are byte-identical to the reviewed cubic
publication candidate. Its former Section 5 is retained as Section 5.1.
The new run-routing argument, connector minimum, padding, formulas,
cross-references, and corollaries were checked as one complete chain.
The refinement review did not rely on the author's child-agent audit.

This is logical proof review. No finite-width matrix sweep was performed.
Any accompanying code oracle or finite checks are supplemental and were
not the validation of the all-width theorem recorded here.

## Cutoff and proof coverage

For `m>=3`, put `p=floor(m/2)`. The matrix is the stated full-column
transfer on noncrossing pairings, with empty-prefix and completed-cycle
states and rejection of premature closed components. Alternating endpoint
states are removed exactly when `4 | m`. The reviewed conclusions are

```text
L_c(m) = 2p^3+7p^2+3p+11,
L_q(m) = 13p^2+11p+11,
L(m)   = min{L_c(m),L_q(m)},
A^ell has no entry equal to one for every integer ell >= L(m).
```

The review covered charge sectors and exceptional/isolated states;
cap-free normalization at both width parities; the odd no-odd-port
preparation; noncrossing reverse lifting, including simultaneous reversed
cups; all canonical adjacent reconnections; and preservation of nonempty
frontiers and valid current-component connections.

For the quadratic refinement, the FF, FHF, and FHH moves place the selected
F on exactly the next two endpoint ordinals. Recorded inverse swaps remain
through-only and valid after generators change the matching. Identity
skips retain the scheduled-position accounting. The conversion needs no
generator indexed `K-1`, so the odd bottom singleton requires no routing
across it. The recursive word has at most `p+1` nonempty runs and at most
`p(p+1)/2` scheduled positions. Consequently its column cost is at most
`J=9p(p+1)`. The direct-generator exceptional cases and `t=1` are covered.

With `T=2p^2+p+2`, `B=4p+2`, and `E=p(p+1)/2`, the checked accounting is

```text
D_c = 2T+BE+1 = 2p^3+7p^2+3p+5,
D_q = 2T+J+1  = 13p^2+11p+5,
D   = min{D_c,D_q},
L   = D+6.
```

Both connector constructions are available for every eligible endpoint
pair and required parity, so selecting the smaller bound is valid. The
local-return dependency gives two alternatives for every even padding
length at least four. At most two additional edges handle the empty-prefix
and completed-cycle states. Higher powers remain free of entries one by
nonnegative matrix multiplication.

The final text correctly requires caps to join distinct **current**
components. Its one-cap-per-column assertion is restricted to the new
matching-routing stage; reversed normalization may contain several caps,
handled by the reverse-lifting lemma. Both earlier wording concerns are
resolved in the text covered by this receipt.

## Corollaries and numerical qualifications

The strip-replacement argument preserves boundary states and the fixed
prefix/suffix connections, including blocks touching grid boundaries.
The signed-cut lemma excludes alternating states when fewer than `2k`
vertices are deleted at width `4k`. Together these give

```text
M(m,n) >= floor(n/L(m))                    when 4 does not divide m,
M(4k,n) >= min{2k, floor(n/L(4k))},
M(4k,n) = 2k when n >= (2k-1)L(4k).
```

The equality also uses evenness of the deletion count and the reviewed
upper construction, including its `k=1` and `n=3` cases. In particular the
standalone sufficient threshold

```text
n >= (2k-1)(52k^2+22k+11)
```

is valid. It is not claimed sharp and does not settle square dimensions.

The retained state count is `N_m=1+Motzkin(m)`, minus `2 Catalan(m/4)`
when `4 | m`. The same matrix therefore admits
`Lhat(m)=min{L_c(m),L_q(m),4N_m}`, which can replace `L` in these
corollaries. The comparison `L_c-L_q=2p(p-4)(p+1)` is correct. The text
also correctly notes that the polynomial minimum gives 23 at width three
and 61 at width four, whereas the corresponding 4N bounds are 20 and 32.

## Dependencies, attribution, and limits

The reviewed local dependency identities are:

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

The review included all four geometric cases of the 4N note's local-return
fact, the signed-cut calculation, and the upper construction's forced
ladder argument. All four relative dependency targets were verified in
the intended repository layout.

Attribution statements were checked against the cited primary papers and
original forum contributions: transfer-connectivity background, the
zero-word charge, the Temperley--Lieb action, and the prior upper-bound
construction and its stated scope. The added Kazazi citation accurately
describes complete-cycle reconfiguration and is explicitly related
context, not a dependency of the column-append proof. This was a targeted
source check, not a literature-wide novelty search.

The reviewer is a non-author AI agent within the same collaborating
collective. This receipt is not human peer review, proof-assistant
formalization, third-party institutional review, or an exhaustive
computational certificate. It establishes no priority, external
acceptance, adoption, or publication status. The conjectured sharp linear
cutoff remains unproved here. The reviewer sent no external messages,
took no publication action, and did not edit the proof or repository.
