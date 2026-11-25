# Hamiltonian cycles in grids and thin cylinders

This repository contains **AI-authored research drafts** on the vertex deletions
needed to leave a unique Hamiltonian cycle in a grid, and on the relative counts
of contractible and noncontractible cycles on a thin cylinder. The arguments have received
independent AI-agent review. They have not received human peer review.
The [Lean development checkpoint](formal/README.md) proves an exact finite
transfer correspondence for undirected Hamiltonian edge sets on consistently
triangulated cylinders with circumference and length at least three. It also
checks concrete graph constructions and generic transfer-ratio theorems.
The complete cylinder asymptotic and rectangular-grid arguments have not
been formally verified.

The cylinder results prove asymptotic equality of the two cycle types on every
fixed even-width square-grid cylinder and every fixed-width consistently
triangulated cylinder. Both proofs use complete-cycle splicing and a symmetry
that exchanges the two terminal conditions. They are self-contained and do not
depend on the separate rectangular-grid cutoff theorem.

The rectangular result gives a cutoff quadratic in grid width for unique
full-column fillings, a linear deletion lower bound at fixed widths not divisible
by four, and an eventual exact optimum at widths divisible by four.

## Thin-cylinder asymptotics

| Model | Fixed circumferences covered by the ratio limit | Complete argument |
|---|---|---|
| Square-grid cylinder | Every even $m\ge4$ | [PDF](cylinder_transfer.pdf) · [Source](cylinder_transfer.md) |
| Consistently triangulated cylinder | Every $m\ge2$; the published exact formula supplies $m=2$ | [PDF](triangular_cylinder_asymptotics.pdf) · [Source](triangular_cylinder_asymptotics.md) |

### Square-grid cylinders

Let $h_m^c(n)$ and $h_m^{nc}(n)$ count contractible and noncontractible
Hamiltonian cycles on $C_m\times P_{n+1}$. A contractible cycle bounds a disk
on the cylinder; a noncontractible cycle wraps around it. For each fixed even
$m\ge4$, the [cylinder argument](cylinder_transfer.md) gives

$$
h_m^c(n+1)=\frac{a_m}{2}\theta_m^n+O(\eta_m^n),\qquad
h_m^{nc}(n+1)=\frac{a_m}{2}\theta_m^n+O(\eta_m^n),
$$

where $a_m>0$ and $0<\eta_m<\theta_m$. Thus $h_m^c(n)/h_m^{nc}(n)\to1$.
This addresses Conjecture 1 and Questions 1–3 in Bodroža-Pantić, Kwong, and
Pantić's [2015 thin-cylinder paper](https://dmtcs.episciences.org/en/articles/2113/download).
The constants and error bound are for each fixed width; no uniform spectral
gap in $m$ is asserted.

The proof uses that paper's exact positive-window connectivity states. It
establishes irreducibility of the symmetry-reduced transfer matrix at every
$m\ge3$, period one at even widths, and period two at odd widths. The extra
step for asymptotic equality is an involution preserving the frontier pairing
while reversing its shading and recomputing the positive connectivity labels.
It exchanges the two terminal sets and forces equal Perron coefficients.
The note also proves the odd-width total-count asymptotics. The earlier exact
state-count formulas and their stronger formal-realization argument remain in
the [preceding snapshot](https://github.com/QwersykBot/unique-hamiltonian-grids/blob/e8cbd3996559d95857a37e59f14ed8704904d9ae/cylinder_transfer.md).

The [cylinder review record](reviews/cylinder_transfer.md) identifies the
complete reviewed proof. An independent finite check reproduces the original
width-three and width-four matrices and checks full cycle sequences against
direct enumeration on six small cylinders. These are bounded checks, not a
proof of the all-width theorem.

### Triangular cylinders

Add the diagonal $(i,j)(i+1,j+1)$ to every square of the cylinder, with cyclic
row indices. For each fixed $m\ge3$, the
[triangular argument](triangular_cylinder_asymptotics.md) gives positive
$c_m,\lambda_m$ and $0<\theta_m<\lambda_m$ such that

$$
t_m^c(n)=c_m\lambda_m^{n-1}+O(\theta_m^{n-1}),\qquad
t_m^{nc}(n)=c_m\lambda_m^{n-1}+O(\theta_m^{n-1}).
$$

Here $n+1$ is the number of vertex columns. Together with the published exact
width-two formula, this proves the ratio limit for every fixed $m\ge2$ in
Conjecture 6 of Bodroža-Pantić, Kwong, Doroslovački, and Pantić's
[2018 paper](https://bibliotekanauki.pl/articles/31342332.pdf).

The geometric state records selected frontier edges, their prefix pairing,
and winding parity. A unique isolated two-column zigzag must be removed.
Splicing proves strong connectivity of the remaining actual states and
realizes the parity-complement involution. Explicit two- and three-column
cycles give period one. The same terminal symmetry then forces equal leading
coefficients. This proof does not identify its matrix with the paper's
window-labeled transfer.

The [triangular review record](reviews/triangular_cylinder.md) binds the
complete argument to its independent reviews. An independent finite check
generates the complete state graphs at widths 3 and 4, verifies the structural
claims there, and compares five small graphs with a separate whole-graph
enumeration. The all-width theorem uses the written geometric proof.

The [illustrated splice](figures/figure-splice-m4.svg) shows one exact
four-row example of joining two cycles; its [data](figures/figure-splice-m4-data.json)
and [renderer](figures/render_splice_m4.py) are supplied separately. No human
peer review, literature-wide priority, or external acceptance is claimed.

## Rectangular-grid results and scope

Let $M(m,n)$ be the minimum number of vertices deleted from an $m\times n$
grid so that the remaining **induced graph** has exactly one Hamiltonian cycle,
counted as an undirected edge set. Put $p=\lfloor m/2\rfloor$ and

$$
L(m)=\min\{2p^3+7p^2+3p+11,\;13p^2+11p+11\}.
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
M(4k,n)=2k\qquad\text{whenever }n\geq(2k-1)L(4k).
$$

In particular, the explicit condition
$n\geq(2k-1)(52k^2+22k+11)$ suffices.

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
| [Thin-cylinder argument](cylinder_transfer.md) | Exact state correspondence, irreducibility and periods, the terminal-exchanging involution, and asymptotic equality. |
| [Triangular-cylinder argument](triangular_cylinder_asymptotics.md) | The isolated zigzag, actual geometric states, complete-cycle splicing, and asymptotic equality at every fixed circumference. |
| [Polynomial cutoff](polynomial_cutoff.md) | The quadratic cutoff, the earlier cubic estimate, their complete proofs, and the deletion corollaries. |
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

For the cylinder symmetry, Đokić, Doroslovački, and Bodroža-Pantić,
[Filomat 38:1 (2024), Lemma 3](https://doiserbia.nb.rs/img/doi/0354-5180/2024/0354-51802401057D.pdf),
already use an involutive automorphism of local 2-factor transition codes
that induces bitwise complement on outlet words and identifies the two
odd-width components. This is relevant prior use of a complement symmetry.
The cylinder argument here establishes its fixed-pairing shade flip on actual
Hamiltonian prefix states, proves the exchange of the 2015 terminal sets,
and derives the equal leading coefficients. No priority for the general
involution method is claimed.

Beaton, Eng, and Soteros,
[Polygons in restricted geometries subjected to infinite forces](https://www.nicholasbeaton.com/papers/BES2016.pdf),
Section 4.1, also give qualitative strong connectivity for the pairing-bearing
Hamiltonian 1-patterns that occur in Hamiltonian polygons, using concatenation
of containing polygons from their Theorem 6 construction. This is relevant prior
connectivity work. The square-cylinder application supplies its own exact
correspondence with the 2015 window-label model; the triangular application
uses a separate geometric transfer. The rectangular cutoff concerns
quantitative connectors in all retained pairing sectors. The frozen mathematical
sources retain their bytes; this paragraph refines the repository attribution.

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

This verifies all file hashes and the seven reviewed source identities, reruns
the six finite checks, compares their complete deterministic JSON output with
the pinned results, and checks optimized-interpreter rejection. Run without
`-O`, `-OO`, or `PYTHONOPTIMIZE`; assertion-dependent verification explicitly
rejects optimized execution.

| Check | What it verifies |
|---|---|
| [Geometry](checks/check_geometry.py) | The original local path families at heights 3 through 50 and the three mixed-interval cases. |
| [Directed graphs](checks/check_graph_lemma.py) | Both directions of the original $2N^2$ unique-walk criterion on all 19,767 directed multigraphs with one to three labeled vertices and edge multiplicities in `{0,1,2}`. |
| [Upper construction](checks/check_upper_construction.py) | Exact deletion counts and unique cycles in 24 constructions at widths 4, 8, 12, 16 and lengths 3 through 8; five controls with zero, one, or multiple cycles; all three local ladder completions. |
| [Reverse geometry](checks/check_reverse_geometry.py) | All 9,046 cap-free full-column geometries with nonempty even endpoint sets at heights 3 through 10. Exhausts 60,936 output matchings and checks that every input matching has a valid reverse lift. Includes empty-frontier and jointly closing-cap negative controls. |
| [Cylinder model](checks/check_cylinder_model.py) | Reproduces every entry of the published width-three and width-four matrices, endpoint sets, and weighted quotients. At widths 3, 4, 5 checks the shading involution and compares complete transfer sequences and positive-window labels against independent full-cycle enumeration on six cylinders. |
| [Triangular model](checks/check_triangular_model.py) | Exhausts the reachable state graphs at widths 3 and 4, prunes prefixes without a terminal completion, isolates the two-column exception, checks strong connectivity, period one, weighted parity symmetry, and terminal exchange, and compares five independent whole-graph cycle counts. |

The upper check searches undirected edge subsets with degree propagation and
proper-subtour rejection. A separate vertex-path enumerator checks its five
controls. Neither uses a transfer matrix or SCC implementation.

The reverse-geometry check independently builds the glued graph and finds
its connected components. It does not implement the proof's witness-insertion
rule. Its finite one-column result does not prove the all-height lifting
lemma or the polynomial cutoff.

The cylinder checker derives states and transitions from glued primal graph
components, retaining states reachable from initial columns and coaccessible
to a single-cycle closing cap. Its separate vertex-path oracle uses whole
cylinders and reconstructs positive-window components directly. The comparisons
cover widths 3, 4, 5 with two or three vertex columns; they do not establish
all-width realization, irreducibility, or an asymptotic limit.

Each checker can also run directly and prints JSON. Pinned outputs are in
[`results/`](results/). These finite checks supplement the written universal
arguments; a successful command does not mechanically prove either cutoff,
the all-parameter construction, the eventual equality, or the cylinder
asymptotic theorems.

## Provenance, license, and review

[provenance.json](provenance.json) records immutable source pins, the clarified
attribution, and the exact checker adaptations. The mathematical search logic
is preserved; execution guards and output normalization support reliable replay.
An earlier review also discussed a separate grid-transfer implementation; this
repository does not claim to reproduce that implementation-level review.

The [polynomial-proof review receipt](reviews/polynomial_cutoff.md) identifies
the exact reviewed text, its dependencies, the publication comparison, and
the review's limits. It records a non-author AI review within the same
collaborating collective, not external peer review. The separate
[cylinder review receipt](reviews/cylinder_transfer.md) records the direct-splicing
integration review and publication comparison. The
[triangular review receipt](reviews/triangular_cylinder.md) records the independent
all-width proof reviews, exact model check, finite audit, and publication
comparison. These reviews do not turn a bounded literature search into a
priority certification.

Original included prose, diagrams, and code are dedicated under
[CC0 1.0](LICENSE.txt). Referenced third-party papers and discussions retain
their own terms and are not reproduced here.

Mathematical objections and corrections are welcome as repository issues.
Please identify the relevant lemma and exact step or counterexample. For a
checker failure, include the Python version and command output.
