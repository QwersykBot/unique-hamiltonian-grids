# Why the certificate checker proves the lower bound

This document explains the acceptance conditions in `check_certificate.py`.
The checker uses Python's standard library and imports no search program.
A successful **complete** check proves `M(12,12) >= 6`. The separate
six-deletion upper construction is needed to conclude equality.

## Positive records: two explicit cycles

The full 12 by 12 grid has 144 vertices and 264 edges. The checker independently
constructs its edges by visiting vertices in row-major order and listing the
right edge, then the down edge, when present. A witness is a 66-digit
hexadecimal integer whose set bits select edges from that list. Extra bits,
malformed encodings, and identical witness integers are rejected.

For each witness, every deleted vertex must have selected degree zero and every
retained vertex selected degree two. Consequently the selected graph is a
disjoint union of cycles on the retained vertices. Starting at one retained
vertex, the checker follows the selected edge other than the edge just used.
It requires every retained vertex to occur exactly once before returning to
the starting vertex. This rules out a union of smaller cycles. Two different
accepted integers therefore specify two distinct Hamiltonian cycles, counted
as undirected edge sets rather than oriented traversals.

## Zero records: necessary obstructions only

The zero check maintains two undirected graphs, `forced` and `available`.
Initially no edge is forced, and every edge between retained vertices is
available. Any possible Hamiltonian cycle must contain all forced edges and
use only available edges.

The following operations preserve that invariant:

- If a vertex has exactly two available incident edges, both are forced.
- If a vertex has exactly two forced incident edges, all its other incident
  edges are removed from the available graph.

The checker updates both endpoints whenever an edge changes. It accepts a
zero record only after deriving one of these contradictions:

1. A retained vertex has fewer than two available incident edges or more than
   two forced incident edges.
2. A proper connected component of the forced graph has degree two at every
   vertex. Such a component is already a cycle and cannot connect to the
   remaining retained vertices in a Hamiltonian cycle.

If neither contradiction is obtained, the zero record is rejected. There is
no branching, Hamiltonian search, time budget, or assumption that failure to
find a cycle proves nonexistence. Propagation terminates because edges can
only become forced or unavailable, and the grid has finitely many edges.

## Complete coverage

The original grid has 72 vertices of each checkerboard color. A Hamiltonian
cycle alternates the two colors, so a permissible deletion set must delete
equally many vertices of each color. Below six deletions, only balanced sets
of sizes zero, two, and four need examination.

The checker explicitly computes the eight dihedral images of every recorded
deletion set. It requires the set to be the lexicographically smallest image,
checks its actual orbit size, and rejects duplicate canonical sets, including
duplicates spread across input files.

Burnside's lemma gives the number of balanced-set orbits. The necessary fixed
set counts have direct derivations:

| Symmetry type | Number of symmetries | Fixed balanced two-sets | Fixed balanced four-sets |
|---|---:|---:|---:|
| Identity | 1 | `72^2 = 5184` | `C(72,2)^2 = 6533136` |
| Quarter turn | 2 | `0` | `36` |
| Half turn | 1 | `0` | `36^2 = 1296` |
| Diagonal reflection | 2 | `0` | `36 * (30 + C(12,2)) = 3456` |
| Axial reflection | 2 | `72` | `C(72,2) = 2556` |

A quarter turn has 36 vertex orbits of size four, each with two vertices of
each color. A half turn has 36 monochromatic pairs of each color. A diagonal
reflection fixes 12 vertices of one color and has 30 two-vertex orbits of
that color and 36 of the other color. An axial reflection has 72 mixed-color
pairs. These observations give every entry in the table.

Dividing each weighted sum by eight gives:

- Zero deletions: one orbit, containing the empty set.
- Two deletions: `(5184 + 2*72)/8 = 666` orbits.
- Four deletions:
  `(6533136 + 2*36 + 1296 + 2*3456 + 2*2556)/8 = 818316` orbits.

Every accepted deletion set is a valid canonical representative, and no two
are equal. Reaching these respective orbit counts therefore proves that
every orbit is represented. The checker additionally requires the sum of
actual orbit sizes to equal the raw balanced-set totals `1`, `5184`, and
`6533136`. All grid symmetries preserve the number of Hamiltonian cycles.

Thus a complete accepted certificate proves that every relevant deletion
set below size six has either no Hamiltonian cycle or at least two. This is
exactly the lower bound `M(12,12) >= 6`.

## Scope of acceptance

Run the checker without `--partial` to require complete coverage. Partial
mode checks the supplied records but explicitly makes no complete-coverage
or lower-bound claim.

The certificate makes the lower bound independently checkable without
trusting the producer's search, pruning, symmetry retries, or recorded
status labels. Acceptance still relies on the checker implementation and
its execution; this is not a theorem-prover formalization or a formal-kernel
verification claim.
