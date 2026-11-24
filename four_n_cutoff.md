# A 4N cutoff for the full-column grid transfer

Mathematical proof note, 24 November 2026. This is a separate refinement of
the frozen classification proof. The complete argument has received a
separately reasoned logical review by a collaborating AI agent, who also
discussed intermediate arguments and proposed the parity corollary. That
review covered the geometric return cases and the parity-lift first-return
argument; no mathematical blocker was identified. This is not blind or
third-party review, human peer review, or proof-assistant formalization;
novelty and external acceptance have not been established. In particular,
this note does not prove the much stronger exploratory conjecture that the
sharp cutoff is floor(m/2)+2. Earlier proof snapshots remain unchanged.

## Statement and source dependency

Fix m >= 3. Use the full-column transfer matrix on noncrossing frontier
pairings, together with the empty-prefix and completed-cycle states. Reject
every closed component unless it is the sole component and is one completed
cycle. A completed cycle has no full-column successor. When 4 divides m,
delete all states whose endpoint set consists of every odd row or every even
row. Let A denote the resulting nonnegative integer matrix and N its number
of states. Then

    A^(4N) has no entry equal to one.

The same conclusion holds at every larger power. The state count is

    N = 1 + Motzkin(m)                         if 4 does not divide m,
    N = 1 + Motzkin(m) - 2 Catalan(m/4)       if 4 divides m.

The convention is Motzkin(m) = sum_j binom(m,2j) Catalan(j), including the
empty pairing, and Catalan(j) = binom(2j,j)/(j+1).

The geometric ingredients are Lemmas 2, 4, 5, 6, and 7 of the unchanged source
grid_width_classification.md, SHA256
3b325dfe8d0e874bf2202fe8b086e3f4a5f84013d5d4720d75d2f5d8c3402fd1.
The proof below does not use that source's general 2N^2 graph lemma or its
classification of all cyclic strongly connected components. It uses the
directly established forcing of the alternating endpoint states, which makes
the deleted set closed under full-column transitions.

## 1. Good states and short return walks

Call an ordinary state good when its endpoint set touches row 1 or row m,
or contains two adjacent rows. Call every other retained state bad; this
includes the empty-prefix and completed-cycle states.

For every good state P,

    (A^2)_(P,P) >= 1,        (A^4)_(P,P) >= 2.               (1)

Here and below walks distinguish their selected column edges, including
parallel transition edges if there are any.

To prove (1), use the reversible through-path partition from Lemma 2 of the
source. It partitions all rows into intervals, each containing one input
endpoint at one of its ends. Using all vertical edges of each interval sends
that endpoint to the opposite end; the same intervals reverse the transition.
Thus P has a two-column return. The following cases produce two four-column
returns.

* If an interval has height at least three, the source's Lemma 4 supplies two
  different Hamiltonian paths in its height-by-four rectangle, each joining
  the same designated input and output. Repeat the original through paths
  elsewhere. Both fillings preserve each individual boundary endpoint.

* If interval heights are at most two and both heights occur, choose two
  neighboring intervals of different heights. Their three-row union has
  endpoint pattern 110, 101, or 011. Lemma 5 supplies two four-column path
  covers preserving the individual endpoints in each case. Repeat the
  original through paths elsewhere.

* If every interval has height one, every row is an endpoint. Since m >= 3,
  the even number m is at least four. A noncrossing perfect matching contains
  an adjacent matched pair i,i+1. Choose an endpoint immediately next to this
  pair, on either available side; it has a different partner. The two-column
  reconnection between that endpoint and the nearer endpoint of the matched
  pair joins two different components, then creates a new adjacent pair.
  Follow it by the two-column reconnection at i,i+1. This restores the
  original matching. Both caps join different components and therefore
  create no closed loop. The resulting four-column return is different from
  four straight-through self-loops. These are the reconnection operations
  defined and justified in Lemma 6 of the source.

* If every interval has height two, write P -> Q -> P for the reversible
  return. Unless all endpoints have the same orientation in their two-row
  intervals, some adjacent intervals have pattern 1001 in P or in Q.
  Repartition those four rows as 1+3 (or 3+1), leaving other intervals
  unchanged. This gives an additional reversible neighbor, different from
  the original neighbor. If the pattern is in P, two different two-column
  returns give different four-column returns. If it occurs only in Q,
  denote Q's additional neighbor by R, with R != P. The walks

      P -> Q -> P -> Q -> P,
      P -> Q -> R -> Q -> P

  are distinct four-column returns. This explicitly handles the local
  pattern 0110 at P, which need not itself admit a 1+3 partition.

  Finally, uniform orientation means all odd rows or all even rows are
  endpoints. Their number m/2 must be even, so 4 divides m. These states
  were deleted.

Every return constructed above remains in the retained graph. An alternating
endpoint state has exactly one full-column successor, namely its opposite
alternating state with the same transported matching. Thus a walk that enters
the deleted set can never return to a retained state.

Combining a four-column return with copies of a two-column return shows that
every good P has at least two returns of each even length at least four.

## 2. The bad subgraph and its two-cycles

The directed subgraph induced by bad states is acyclic. Indeed, an ordinary
bad state has only isolated interior endpoints. Lemma 2 of the source shows
that every valid full-column transition increases their number by at least
two. This increase prevents a cycle consisting entirely of ordinary bad
states. The empty-prefix state has no incoming full-column edge, and the
completed-cycle state has no outgoing full-column edge, so neither lies on
a directed cycle.

There is one additional short-return observation. Suppose a bad state P
belongs to a two-column return P -> Q -> P. Then Q is good: otherwise both
steps would strictly increase the endpoint count. Choose a reversible
through-path neighbor R of Q. Necessarily R != P. If R were P, reversing
that same through partition would give a through partition at the bad state
P, contradicting the strict endpoint-count increase at every transition
from P. Therefore

    P -> Q -> P -> Q -> P,
    P -> Q -> R -> Q -> P

are distinct four-column returns at P. In particular,

    P bad and (A^2)_(P,P) > 0 implies (A^4)_(P,P) >= 2.    (2)

As above, these return walks cannot enter the deleted alternating set.

## 3. The parity-lift counting argument

Lift the graph to pairs (state, parity), with every transition changing
parity. An original walk with a fixed initial parity has a unique lifted
walk. There are 2N lifted vertices. We claim that a walk unique for its
endpoints and length visits each lifted vertex at most twice.

For a good lifted vertex, three visits give a return segment between the
first and third visits of even length at least four. By (1), there are at
least two returns of that same length. Replacing this segment contradicts
uniqueness.

For a bad lifted vertex, suppose there are at least three visits, and take
three consecutive visits. The two segments between them are first-return
loops C and D at that lifted vertex.

If C and D are different edge words, swapping their order gives a different
walk with the same endpoints and length. Distinct first-return words cannot
commute: the successive returns to their base vertex uniquely delimit each
word. Thus uniqueness requires C = D.

Let ell be their common length in original columns. It is positive and even.
If ell = 2, the two repeated loops form a four-column return at a bad state
having a two-column return. By (2) this segment has an alternative.

If ell >= 4, the loop contains an interior good state, since the bad induced
subgraph is acyclic. Its two corresponding occurrences in the repeated
loops have the same parity and are ell columns apart. By (1), the intervening
segment can again be replaced by a different return of the same length.

All cases contradict uniqueness. Therefore each of the 2N lifted vertices
appears at most twice. A unique walk consequently has at most 4N vertices,
and hence at most 4N-1 edges. No walk of length 4N is unique. This proves
the stated matrix conclusion.

Once a nonnegative integer matrix power has only entries zero or at least
two, right multiplication by A cannot create an entry one: each product
summand is zero or at least two. The conclusion therefore holds at all
larger powers as well.

## Consequences and limits

For m >= 3 not divisible by four, the fixed-prefix and fixed-suffix strip
replacement argument in the frozen source gives the improved bound

    M(m,n) >= floor(n / (4(1 + Motzkin(m)))).

This uses the complete original transfer graph. It preserves the same
endpoint pairing and excludes premature closed components, so a distinct
strip filling yields a different global Hamiltonian cycle.

For m = 4k, put R = N_m - 2 Catalan(k), where N_m = 1 + Motzkin(m).
The retained matrix statement is unconditional. To apply it to a grid with
fewer than 2k deleted vertices, use the signed cut argument from the unchanged
source eventual_exact_optimum.md, SHA256
13445aefa748d7ec3c593833db3854ed73aaa863b1e1fff96127df4cc87afc6b.
An alternating cut forces at least k deleted vertices on each side, so a
Hamiltonian cycle in a grid with fewer than 2k deletions encounters no removed
state. Each block of 4R full columns is therefore forbidden in such a grid.
Consequently, for n >= 3,

    M(4k,n) >= min(2k, floor(n / (4R))).

Bipartite parity gives a slightly sharper threshold for eventual equality:

    M(4k,n) = 2k whenever n >= 4(2k-1)R.                   (3)

Indeed, a Hamiltonian cycle uses an even number of vertices. The original
4k-by-n grid has an even number of vertices, so its number d of deleted
vertices must also be even. If d < 2k, then d <= 2k-2. But the stated threshold
provides 2k-1 disjoint blocks of 4R columns. Every block must contain a deleted
vertex, requiring d >= 2k-1, a contradiction. This proves the lower bound 2k.

The matching upper bound M(4k,n) <= 2k for every n >= 3 is the explicitly
reconstructed construction in two_k_exploration/two_k_construction.md,
SHA256 52f61a99433bca3f94409d3df493982a22731393dd1e5394d04b46bfbe2f5c07.
That source credits the previously stated 2k upper bound in the motivating
question. Equality (3) depends on this upper construction as well as the
signed-cut argument; the matrix estimate alone is not an upper bound.

The bound is linear in the number of transfer states, which grows
exponentially with m. It is not a linear-in-width bound, and it does not
explain why the exploratory sharp exponents at widths 3 through 12 equal
floor(m/2)+2. No finite-width matrix experiment is needed for the 4N proof.
