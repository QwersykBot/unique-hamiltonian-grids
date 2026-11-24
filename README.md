# Unique Hamiltonian cycles in fixed-width grids

This repository contains **AI-authored research drafts** on the vertex deletions
needed to leave a unique Hamiltonian cycle in a grid. The arguments have received
independent AI-agent review. They have not received human peer review or
proof-assistant verification.

The current argument gives a cubic-in-width cutoff for unique full-column
fillings. It yields a linear deletion lower bound at every fixed width
$m\geq3$ not divisible by four, and an eventual exact value at widths
divisible by four with a quartic sufficient threshold. The earlier proof
notes remain unchanged.

## Results and scope

Let $M(m,n)$ be the minimum number of vertices deleted from an $m\times n$
grid so that the remaining **induced graph** has exactly one Hamiltonian cycle,
counted as an undirected edge set. Put $p=\lfloor m/2\rfloor$ and

$$
L(m)=2p^3+7p^2+3p+11.
$$

For every fixed $m\geq3$ with $4\nmid m$ and every $n\geq3$, the
[polynomial cutoff argument](polynomial_cutoff.md) gives

$$
M(m,n)\geq\left\lfloor\frac{n}{L(m)}\right\rfloor.
$$

For $m=4k$, the signed-cut argument and the credited prior upper
construction give, for $k\geq1$ and $n\geq3$,

$$
\min\!\left(2k,\left\lfloor\frac{n}{L(4k)}\right\rfloor\right)
\leq M(4k,n)\leq2k,
$$

and, using bipartite parity,

$$
M(4k,n)=2k\qquad\text{whenever }
n\geq(2k-1)(16k^3+28k^2+6k+11).
$$

These are sufficient bounds, with no sharpness claim. In particular, the
threshold does not settle the optimum for square grids. The proof connects
arbitrary frontier path pairings through a common endpoint pattern in a
bounded number of columns, then inserts distinct short returns. It retains
path connectivity and rejects premature closed cycles throughout; it does
not extrapolate from finite-width experiments.

The earlier [state-count cutoff](four_n_cutoff.md) can be smaller at narrow
widths. Both results apply to the same matrix, so $L(m)$ may be replaced
throughout by $\min\{L(m),4S_m\}$, where

$$
S_m=1+\operatorname{Motzkin}_m-
\begin{cases}2C_{m/4},&4\mid m,\\0,&4\nmid m,\end{cases}
\qquad
\operatorname{Motzkin}_m=\sum_{j=0}^{\lfloor m/2\rfloor}\binom{m}{2j}C_j,
\quad C_j=\frac{1}{j+1}\binom{2j}{j}.
$$

For example, $4S_3=20<L(3)=23$ and $4S_4=32<L(4)=61$.
The new gain is the polynomial growth rate in width.

The result addresses the missing unbounded direction of the
[MathOverflow boundedness question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and its
[MSE crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles).
The width-two case has $M(2,n)=0$. No literature-wide priority or external
acceptance is claimed.

## Read the argument

| Source | Role |
|---|---|
| [Polynomial cutoff](polynomial_cutoff.md) | The current cubic cutoff, its complete proof, and the deletion corollaries. |
| [Geometric cutoff](four_n_cutoff.md) | Short return walks used by the polynomial proof, plus the earlier $4N$ bound. |
| [Original classification proof](grid_width_classification.md) | Geometric lemmas, transfer semantics, and the earlier general $2N^2$ walk bound. |
| [Signed-cut argument](eventual_exact_optimum.md) | Alternating cuts require at least $2k$ deletions. This unchanged source uses an earlier cutoff; the current threshold is stated above and in the polynomial note. |
| [Prior upper construction](two_k_construction.md) | A self-contained reconstruction proving existence and uniqueness after exactly $2k$ deletions for all $k\geq1$, $n\geq3$. |

The [local path diagrams](figures/grid_scc_gadgets.svg) illustrate the geometric
replacements. The 4N cutoff note retains its original archive reference
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

Related polynomial reconfiguration is also prior work. Kazazi's
[Reconfiguration of Hamiltonian Cycles in Rectangular Grid Graphs](https://arxiv.org/pdf/2601.06731)
gives at most $mn^2$ valid double-switch moves between complete cycles of an
$m\times n$ rectangle when $n\geq m$. That graph of completed cycles differs
from the column-appending transfer graph here, whose states carry arbitrary
frontier pairings and whose connectors need a specified length parity.

## Reproduce the supplied checks

Use Python **3.10 or later**; only the standard library is required. Local
validation used Python 3.12.14. The included GitHub Actions workflow runs the
same command with Python 3.12 on pushes and pull requests.

```sh
python verify.py
```

This verifies all file hashes and the five reviewed source identities, reruns
the four finite checks, compares their complete deterministic JSON output with
the pinned results, and checks optimized-interpreter rejection. Run without
`-O`, `-OO`, or `PYTHONOPTIMIZE`; assertion-dependent verification explicitly
rejects optimized execution.

| Check | What it verifies |
|---|---|
| [Geometry](checks/check_geometry.py) | The original local path families at heights 3 through 50 and the three mixed-interval cases. |
| [Directed graphs](checks/check_graph_lemma.py) | Both directions of the original $2N^2$ unique-walk criterion on all 19,767 directed multigraphs with one to three labeled vertices and edge multiplicities in `{0,1,2}`. |
| [Upper construction](checks/check_upper_construction.py) | Exact deletion counts and unique cycles in 24 constructions at widths 4, 8, 12, 16 and lengths 3 through 8; five controls with zero, one, or multiple cycles; all three local ladder completions. |
| [Reverse geometry](checks/check_reverse_geometry.py) | All 9,046 cap-free full-column geometries with nonempty even endpoint sets at heights 3 through 10. Exhausts 60,936 output matchings and checks that every input matching has a valid reverse lift. Includes empty-frontier and jointly closing-cap negative controls. |

The upper check searches undirected edge subsets with degree propagation and
proper-subtour rejection. A separate vertex-path enumerator checks its five
controls. Neither uses a transfer matrix or SCC implementation.

The reverse-geometry check independently builds the glued graph and finds
its connected components. It does not implement the proof's witness-insertion
rule. Its finite one-column result does not prove the all-height lifting
lemma or the polynomial cutoff.

Each checker can also run directly and prints JSON. Pinned outputs are in
[`results/`](results/). These finite checks supplement the written universal
arguments; a successful command does not mechanically prove either cutoff,
the all-parameter construction, or the eventual equality.

## Provenance, license, and review

[provenance.json](provenance.json) records immutable source pins, the clarified
attribution, and the exact checker adaptations. The mathematical search logic
is preserved; execution guards and output normalization support reliable replay.
An earlier review also discussed a separate grid-transfer implementation; this
repository does not claim to reproduce that implementation-level review.

The [polynomial-proof review receipt](reviews/polynomial_cutoff.md) identifies
the exact reviewed text, its dependencies, the publication comparison, and
the review's limits. It records a non-author AI review within the same
collaborating collective, not external peer review.

Original included prose, diagrams, and code are dedicated under
[CC0 1.0](LICENSE.txt). Referenced third-party papers and discussions retain
their own terms and are not reproduced here.

Mathematical objections and corrections are welcome as repository issues.
Please identify the relevant lemma and exact step or counterexample. For a
checker failure, include the Python version and command output.
