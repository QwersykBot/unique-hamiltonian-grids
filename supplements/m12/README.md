# Certified finite result: M(12,12) = 6

The complete lower-bound certificate and an elementary six-deletion
uniqueness proof establish **M(12,12) = 6** for the ordinary square grid.
Verification uses Python's standard library and requires no Hamiltonian
search, cycle-counting procedure, or C++ compiler.

Here the grid has vertices `(r,c)`, `0 <= r,c < 12`, and edges between vertices
at Manhattan distance one. Deleting vertices means taking the induced graph
on the remaining vertices. `M(12,12)` is the minimum number of deletions that
leaves exactly one Hamiltonian cycle, counted as an **undirected edge set**.

Problem context is the [original square-grid question on Mathematics Stack
Exchange](https://math.stackexchange.com/questions/5103789/minimum-of-black-squares-to-guarantee-uniqueness-of-loop-visiting-all-white-sq)
and its [rectangular-grid extension](https://math.stackexchange.com/questions/5109188/minimum-number-of-forbidden-cells-for-a-unique-loop-on-m-times-n-grid).

This is a finite computational result with internal AI source review and an
independent certificate check. It is not a general lower-bound theorem,
formal-kernel proof, or human peer review. No priority claim is made.

## Verify the complete result

Requirements: **Python 3.10 or newer**. No external Python packages or network
access are needed. From the unpacked packet directory, run:

```sh
python3 verify.py
```

This single command:

1. Verifies all frozen payload hashes before loading the checker or counter.
2. Checks every lower-bound certificate record and complete D4 coverage.
3. Checks the saved six-deletion Hamiltonian-cycle witness directly.
4. Forces the upper construction's cycle using only degree constraints and
   exclusions of edges that would close a proper forced cycle, proving that
   it has **exactly one** Hamiltonian edge set.
5. Reports `equality_established: true` only if the complete lower bound and
   exact-one upper construction both succeed.

The unchanged certificate and checker passed a complete independent run in
**87.62 seconds** on Python 3.12.14. The actual result, counts, and hashes are
in `data/independent-check-report.json`. The small upper-construction check
adds little time; runtime depends on the machine.

For a quick portability check:

```sh
python3 verify.py --sample
```

This validates 1,193 selected records and the upper construction. It
explicitly reports `complete: false` and `equality_established: false` and
does **not** establish the lower bound. The portable wrappers were tested in
this sample mode; the already successful complete certificate check was not
repeated merely to package the same unchanged certificate and checker.

## Evidence and mathematical deduction

| Deletions | Canonical D4 classes | Proved zero cycles | Two explicit cycles |
|---:|---:|---:|---:|
| 0 | 1 | 0 | 1 |
| 2 | 666 | 70 | 596 |
| 4 | 818,316 | 215,993 | 602,323 |
| **Total** | **818,983** | **216,063** | **602,920** |

There are **1,205,840 explicit cycle witnesses** in the complete certificate.
The zero cases are proved by 213,882 degree contradictions and 2,181 forced
proper cycles. No zero label is accepted merely because a search found
nothing.

The grid has 72 vertices of each checkerboard color. A Hamiltonian cycle
alternates colors, so the deleted black and white populations must be equal.
Below six deletions, only balanced sets of sizes zero, two, and four can
therefore matter. The certificate covers all such sets modulo D4, and each
has zero or at least two cycles. This proves `M(12,12) >= 6`.

The upper construction is the `k=3` instance of **[Misha Lavrov's construction
in his answer of 25 October 2025](https://math.stackexchange.com/questions/5103789/minimum-of-black-squares-to-guarantee-uniqueness-of-loop-visiting-all-white-sq)**,
which establishes `M(4k,4k) <= 2k`, expressed after a quarter-turn. This packet
verifies that established construction. Its deleted zero-based coordinates are:

```text
(0,0), (4,0), (8,0), (1,10), (5,10), (9,10)
```

Equivalently, their row-major labels `12*r+c` are
`[0,48,96,22,70,118]`. The explicit witness is in
`data/upper12-witness.json`. Elementary forcing makes every retained degree
two and the resulting forced edge set is checked to be one spanning cycle.
Every possible Hamiltonian cycle must contain those forced edges, so the
cycle is unique. This gives `M(12,12) <= 6` and hence equality. The full
argument is in **`UPPER_PROOF.md`**. The actual upper-check report records
three propagation rounds, four proper-subtour edge exclusions, and all 138
cycle edges forced.

## What the certificate changes about trust

The lower-bound checker does **not** import or trust the producer's counting
program, pruning decisions, symmetry retries, or status labels. Each positive
record supplies two different edge sets. The checker verifies selected
degree two at every retained vertex, degree zero at deleted vertices, and a
single cycle spanning every retained vertex.

For each zero record, a separate neighbor-set implementation forces edges
that every Hamiltonian cycle would have to use. It accepts only a forced
degree contradiction or a forced proper cycle. It never branches, performs
a Hamiltonian search, or uses a timeout as evidence.

Every deletion set is checked for range, balance, canonicality, and
uniqueness. Independently derived Burnside totals are `1`, `666`, and
`818316`; reaching those totals with distinct valid canonical sets proves
complete coverage. Actual orbit weights are also checked. The detailed
soundness and coverage argument is in **`CHECKER_PROOF.md`**.

Thus verification of the lower bound relies on the small independent
checker and its runtime, not on the C++ search that produced the data.
Equality additionally relies on the elementary upper forcing rules and the
small wrapper joining the two results. This remains software verification
rather than formal-kernel verification.

The separately written exact frontier counter is retained as an optional
cross-check. It is not imported or executed by default:

```sh
python3 verify.py --frontier
```

Use `--sample --frontier` for the quick partial smoke test with that optional
upper count. It still makes no complete lower-bound or equality claim.

## Certificate format

`data/complete-m12-hc-certificate.jsonl.gz` is **9,559,221 bytes** and contains
a single header followed by one record per canonical class:

```json
{"format":"m12-hc-certificate-v1","n":12,"edge_order":"row-major-right-then-down"}
```

A zero record is `[D,0]`. A positive record is `[D,hex1,hex2]`, where `D` is
the sorted canonical deletion list. Each witness has 66 lowercase hexadecimal
digits selecting from the full grid's 264 edges. Visit vertices in row-major
order and list the right edge first, then the down edge, when present.
Bit zero selects the first edge; ordinary integer hexadecimal notation is
used, so that bit is at the right-hand end of the text.

All witnesses are expressed in the original canonical grid coordinates;
any producer rotation or reflection has already been inverted.

The compressed certificate's SHA-256 is:

```text
9ea69782a31f3ec4de132782f119fea882f095c9326d15b4f2e5b66a5849658d
```

## Regenerate the certificate

Regeneration is optional. It needs a **C++20 compiler** in addition to Python.
The original run used GCC 14.2.0 with:

```text
-O3 -DNDEBUG -std=c++20 -Wall -Wextra -Wpedantic
```

One command copies the frozen producer inputs into a fresh work directory,
compiles them, runs two producer shards, merges their certificates, and checks
the newly generated result and the upper construction:

```sh
python3 regenerate.py
```

The original production used approximately 434 CPU seconds and 218 seconds
maximum worker wall time; merging took 11 seconds, followed by the
independent check. Generated binaries and results go to a new directory under
`work/`; frozen inputs are never overwritten. Use `--workdir ./reruns` to
choose another location or `--cxx clang++` to choose another C++20 compiler.

```sh
python3 regenerate.py --sample
```

This shorter command exercises compilation and the same witness-serialization
path on the saved partial sample. Like `verify.py --sample`, it never asserts
complete coverage or equality.

## Contents, provenance, and license

- `src/check_certificate.py`: unchanged independent lower-bound checker.
- `src/root_transfer.py`: unchanged optional exact frontier cross-check.
- `CHECKER_PROOF.md`: checker soundness and coverage argument.
- `UPPER_PROOF.md`: elementary uniqueness proof for the six-deletion construction.
- `data/`: complete certificate, small smoke sample, actual independent-check
  report, producer summary, and six-deletion witness.
- `producer/`: unchanged source files and scripts needed to regenerate the
  certificate; verification does not execute them.
- `PROVENANCE.json` and `SHA256SUMS`: exact provenance and payload hashes.

The previous search-record edition is preserved separately and is not nested
in this packet. The complete certificate replaces the need to distribute its
classification CSV files. The complete-check report refers to the exact
unchanged certificate and checker included here; the new portable wrappers
are identified separately in provenance.

**Original source code and documentation in this packet are offered under
Creative Commons CC0 1.0 Universal**, matching the existing project's
dedication. See `LICENSE.txt` and
<https://creativecommons.org/publicdomain/zero/1.0/>. This dedication does not
change the rights or terms of third-party software or linked material.
