# Unique Hamiltonian cycles in fixed-width grids

This repository contains **AI-authored research drafts** on the vertex deletions
needed to leave a unique Hamiltonian cycle in a grid. The arguments have received
independent AI-agent review. They have not received human peer review or
proof-assistant verification.

The current argument gives a linear deletion lower bound at every width other
than two or a multiple of four, and an eventual exact value at widths divisible
by four. All four reviewed mathematical source files are preserved byte for byte.

## Results and scope

Let $M(m,n)$ be the minimum number of vertices deleted from an $m\times n$
grid so that the remaining **induced graph** has exactly one Hamiltonian cycle,
counted as an undirected edge set. Set

$$
N_m=1+\operatorname{Motzkin}_m
=1+\sum_{j=0}^{\lfloor m/2\rfloor}\binom{m}{2j}C_j,
\qquad C_j=\frac{1}{j+1}\binom{2j}{j}.
$$

For every fixed $m\geq3$ with $4\nmid m$ and every $n\geq3$, the
[geometric cutoff argument](four_n_cutoff.md) gives

$$
M(m,n)\geq\left\lfloor\frac{n}{4N_m}\right\rfloor.
$$

For $m=4k$, put $R_k=N_{4k}-2C_k$. The signed-cut argument and the
credited prior upper construction give, for $k\geq1$ and $n\geq3$,

$$
\min\!\left(2k,\left\lfloor\frac{n}{4R_k}\right\rfloor\right)
\leq M(4k,n)\leq2k,
$$

and, using bipartite parity,

$$
M(4k,n)=2k\qquad\text{whenever }n\geq4(2k-1)R_k.
$$

These are sufficient bounds, with no sharpness claim. The cutoff is linear in
the number of transfer states, which grows exponentially with width. Its proof
uses short return walks and a parity lift of the grid transfer graph; it does
not extrapolate from finite-width experiments.

The result addresses the missing unbounded direction of the
[MathOverflow boundedness question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and its
[MSE crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles).
The width-two case has $M(2,n)=0$. No literature-wide priority or external
acceptance is claimed.

## Read the argument

| Source | Role |
|---|---|
| [Geometric cutoff](four_n_cutoff.md) | The current $4N$ argument and its lower-bound and eventual-equality consequences. |
| [Original classification proof](grid_width_classification.md) | Geometric lemmas, transfer semantics, and the earlier general $2N^2$ walk bound. |
| [Signed-cut argument](eventual_exact_optimum.md) | Alternating cuts require at least $2k$ deletions. This unchanged source uses the earlier cutoff; the current threshold is stated above and in the geometric cutoff note. |
| [Prior upper construction](two_k_construction.md) | A self-contained reconstruction proving existence and uniqueness after exactly $2k$ deletions for all $k\geq1$, $n\geq3$. |

The [local path diagrams](figures/grid_scc_gadgets.svg) illustrate the geometric
replacements. The cutoff note retains its original archive reference
`two_k_exploration/two_k_construction.md`; that exact source is supplied here as
`two_k_construction.md`.

## Prior construction and methods

Misha Lavrov's
[25 October 2025 answer](https://math.stackexchange.com/questions/5103789/minimum-of-black-squares-to-guarantee-uniqueness-of-loop-visiting-all-white-sq)
gives the $2k$ cap and forced-zigzag construction for square grids of side $4k$.
Transposition followed by row reflection gives the square case of the deletion
pattern used here. His
[17 November 2025 comment](https://math.stackexchange.com/questions/5109188/minimum-number-of-forbidden-cells-for-a-unique-loop-on-m-times-n-grid)
extends the construction to even lengths and proposes reflection for odd
lengths, stating the all-length upper bound with the odd case not carefully
checked there. Our note is a **self-contained checked reconstruction of this
prior construction**, not a new construction or parity-extension idea. This
more precise attribution supplements the older frozen notes.

Earlier width-three work and Lavrov's width-five partial answer are also prior
work. Connectivity states and rejection of prematurely completed cycles are
established transfer methods; see Jacobsen,
[Exact enumeration of Hamiltonian circuits, walks, and chains in two and three dimensions](https://arxiv.org/html/0709.2322v1),
Section 2, and Bodroža-Pantić et al.,
[Enumeration of Hamiltonian Cycles in Some Grid Graphs](https://people.dmi.uns.ac.rs/~bodroza/Radovi/match43.pdf).
Adjacent reconnection of noncrossing matchings is also standard; see de Gier,
[Loops, matchings and alternating-sign matrices](https://arxiv.org/html/math/0211285v2),
Section 2.1, Equation (1). Đokić, Doroslovački, and Bodroža-Pantić's
[2-factor transfer-graph classification](https://arxiv.org/pdf/2212.00317)
uses odd/even imbalance, but its outlet-word states omit path pairings and
allow disjoint cycles, so it does not establish the Hamiltonian cutoff here.
These references supply background and attribution, not a proof of the present
cutoff or eventual-equality statements.

## Reproduce the supplied checks

Use Python **3.10 or later**; only the standard library is required. Local
validation used Python 3.12.14. The included GitHub Actions workflow runs the
same command with Python 3.12 on pushes and pull requests.

```sh
python verify.py
```

This verifies all file hashes and the four reviewed source identities, reruns
the three finite checks, compares their complete deterministic JSON output with
the pinned results, and checks optimized-interpreter rejection. Run without
`-O`, `-OO`, or `PYTHONOPTIMIZE`; assertion-dependent verification explicitly
rejects optimized execution.

| Check | What it verifies |
|---|---|
| [Geometry](checks/check_geometry.py) | The original local path families at heights 3 through 50 and the three mixed-interval cases. |
| [Directed graphs](checks/check_graph_lemma.py) | Both directions of the original $2N^2$ unique-walk criterion on all 19,767 directed multigraphs with one to three labeled vertices and edge multiplicities in `{0,1,2}`. |
| [Upper construction](checks/check_upper_construction.py) | Exact deletion counts and unique cycles in 24 constructions at widths 4, 8, 12, 16 and lengths 3 through 8; five controls with zero, one, or multiple cycles; all three local ladder completions. |

The upper check searches undirected edge subsets with degree propagation and
proper-subtour rejection. A separate vertex-path enumerator checks its five
controls. Neither uses a transfer matrix or SCC implementation.

Each checker can also run directly and prints JSON. Pinned outputs are in
[`results/`](results/). These finite checks supplement the written universal
arguments; a successful command does not mechanically prove the $4N$ cutoff,
the all-parameter construction, or the eventual equality.

## Provenance, license, and review

[provenance.json](provenance.json) records immutable source pins, the clarified
attribution, and the exact checker adaptations. The mathematical search logic
is preserved; execution guards and output normalization support reliable replay.
An earlier review also discussed a separate grid-transfer implementation; this
repository does not claim to reproduce that implementation-level review.

Original included prose, diagrams, and code are dedicated under
[CC0 1.0](LICENSE.txt). Referenced third-party papers and discussions retain
their own terms and are not reproduced here.

Mathematical objections and corrections are welcome as repository issues.
Please identify the relevant lemma and exact step or counterexample. For a
checker failure, include the Python version and command output.
