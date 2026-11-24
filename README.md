# Linear deletion lower bounds in grid graphs

This repository contains an **AI-authored research draft** giving a linear lower
bound for the number of vertex deletions needed to leave a unique Hamiltonian
cycle in a grid graph. The proof has received independent AI-agent review. It has
not received human peer review or proof-assistant verification.

Read the [complete proof](grid_width_classification.md). The
[local path diagrams](figures/grid_scc_gadgets.svg) illustrate its geometric
replacements. The reviewed proof is preserved byte for byte.

## Result and scope

Let $M(m,n)$ be the minimum number of vertices deleted from an $m\times n$
grid so that its remaining **induced graph** has exactly one Hamiltonian cycle,
counted as an undirected edge set. For every fixed $m\geq3$ with $4\nmid m$,
and every $n\geq3$, the draft proves

$$
M(m,n)\geq\left\lfloor\frac{n}{2N_m^2}\right\rfloor,
\qquad
N_m=1+\sum_{j=0}^{\lfloor m/2\rfloor}\binom{m}{2j}C_j
=\operatorname{Motzkin}_m+1,
$$

where $C_j=\binom{2j}{j}/(j+1)$ is a Catalan number. The constant is
deliberately loose; the conclusion is divergence at every such fixed width.

The proof combines an elementary bound on unique walks in directed multigraphs,
a classification of deterministic components in the full-column grid transfer
graph, and a replacement argument that preserves the fixed exterior of a strip.
Its arbitrary-width conclusion rests on the written argument.

This supplies the unbounded direction requested in the
[MathOverflow question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and its
[Mathematics Stack Exchange crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles).
Those questions state the bounded constructions at width two and widths
divisible by four. This repository does not reconstruct those constructions.
The earlier width-three work and Misha Lavrov's width-five answer are prior work.
No literature-wide priority, sharp constant, exact optimum, or external
acceptance is claimed.

## Reproduce the supplied checks

Use Python 3.9 or later; only the standard library is required. The initial
snapshot was checked with Python 3.12.14. GitHub Actions runs the same command
with Python 3.12 on every push and pull request.

```sh
python verify.py
```

The command verifies file hashes and the exact reviewed proof, reruns both
independent finite checks, compares their complete deterministic output with the
pinned results, and checks that each verification entry point rejects Python's
`-O` mode. Run without `-O`, `-OO`, or `PYTHONOPTIMIZE`: the finite checks use
assertions, and optimized execution is explicitly rejected.

| Check | What it verifies |
|---|---|
| [Geometry](checks/check_geometry.py) | Adjacency, coverage, disjointness, endpoint identity, distinct edge sets, and the shared-edge invariant for the displayed path families at heights 3 through 50 and the three mixed-interval cases. |
| [Directed graphs](checks/check_graph_lemma.py) | Both directions of the unique-walk criterion on all 19,767 directed multigraphs with one to three labeled vertices and edge multiplicities in `{0,1,2}`. |
| [Integrity and execution](verify.py) | The manifest, proof identity, pinned outputs, and optimized-interpreter rejection. |

The individual checks print JSON and leave the repository unchanged:

```sh
python checks/check_geometry.py
python checks/check_graph_lemma.py
```

The [geometry result](results/geometry.json) and
[graph result](results/graph_lemma.json) are finite evidence. A successful run
does not mechanically verify the universal theorem; its justification is the
written proof, including the all-height induction and fixed-exterior argument.

## Provenance and attribution

[provenance.json](provenance.json) identifies the original reviewed archives,
the unchanged proof and diagram, and the exact adaptations to the independent
checkers. The adaptations preserve their mathematical checks, add an early
optimized-mode rejection, and make output deterministic and read-only.

An earlier review companion mentions a separate `grid_transfer.py`. That source
is absent from the two archives used here. No such implementation is included,
and this repository does not claim to reproduce that implementation-level
review. The supplied finite checks need no grid-transfer implementation.

Transfer-based enumeration of grid Hamiltonian cycles is established background;
see Bodroža-Pantić et al.,
[Enumeration of Hamiltonian Cycles in Some Grid Graphs](https://people.dmi.uns.ac.rs/~bodroza/Radovi/match43.pdf).
The proof distinguishes its arbitrary-width argument from the prior partial
results linked above. Referenced third-party papers and discussions are not
included in this repository.

Original prose, diagrams, code, and review material are dedicated under
[CC0 1.0](LICENSE.txt).

## Review

Mathematical objections and corrections are welcome as repository issues.
Please identify the relevant lemma and the exact step or counterexample.
For a checker failure, include the Python version and command output.
