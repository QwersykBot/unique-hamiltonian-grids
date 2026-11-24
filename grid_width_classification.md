# Linear lower bounds for every nonexceptional grid width

**Review-ready proof draft, 24 November 2026.** The complete argument has been
independently challenged by two other AI agents, with an additional independent
review of the endpoint-count and reconnection lemmas. No mathematical blocker
was identified. This is not human peer review or proof-assistant formalization;
literature-wide priority and external acceptance have not been established.
This file is separate from every earlier frozen exact-width certificate.

For fixed m >= 3 not divisible by four, and every n >= 3, the proposed theorem
is the explicit linear lower bound

    M(m,n) >= floor(n / (2 N_m^2)),
    N_m = 1 + sum_{j=0}^{floor(m/2)} binom(m,2j) Catalan(j).

Here M(m,n) is the minimum number of vertices deleted from the m-by-n grid
so that its remaining induced graph has exactly one Hamiltonian cycle, counted
as an undirected edge set. The number N_m is the m-th Motzkin number plus one:
the sum counts all noncrossing partial pairings, including the empty one, and
the extra state records a completed cycle. Here Catalan(j) = binom(2j,j)/(j+1).
The numerical bound is deliberately
loose; its purpose is to prove divergence for every nonexceptional width.

The motivating [MathOverflow question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and [Mathematics Stack Exchange crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles)
already state the bounded constructions M(2,n)=0 and M(4k,n)<=2k for n>=3.
The result below supplies the complementary unbounded direction. Together,
these statements give the bounded-width classification in that question.
Misha Lavrov's existing answer treats width five, and the earlier width-three
argument is also prior work. A live primary-API check on 24 November 2026 found
no MathOverflow answer and only that partial width-five answer on the crosspost;
this limited check is not a literature-wide priority claim.

## Proposed result

Fix a width m >= 2. Let T be the full-column transfer matrix on noncrossing
frontier pairings, with the empty-prefix and completed-cycle states included.
An edge counts one possible selection of vertical edges in a fully retained
column, with horizontal edges determined by degree two. Reject every closed
component unless it is the sole component and is a single completed cycle;
in particular, reject two or more closed cycles. The completed-cycle state
has no successor on a fully retained column. A cyclic strongly connected component
(SCC) is called deterministic here if its internal multigraph is a directed
cycle with every edge of multiplicity one.

Proposed classification:

* At m = 2 there is the deterministic singleton consisting of the full pairing.
* At m = 4k there are precisely Catalan(k) deterministic two-cycles. Their
  endpoint sets alternate between the odd and even row positions, with each
  noncrossing matching transported between these two sets.
* There are no other deterministic cyclic SCCs.

Together with Lemma 1 below, this proves that M(m,n) is unbounded for every
m other than 2 and a multiple of 4. The bounded construction at the exceptional
widths is already present in the motivating question and is not the focus here.

Rows in this note are numbered 1,...,m. Every ordinary frontier state has an
even number of endpoints. Individual paths represented by the pairing may
extend arbitrarily far into the already processed prefix.

## Lemma 1: an elementary eventual-multiplicity criterion

Let A be the adjacency matrix of an N-vertex finite directed multigraph. If
none of its cyclic SCCs is deterministic, A^(2N^2) has no entry equal to one.
Conversely, a deterministic cyclic SCC supplies an entry equal to one at
arbitrarily large powers of A.

Proof within one branching SCC of h vertices: suppose a walk of length at
least 2h^2 were unique for its endpoints and length. Some vertex x occurs at
least 2h+1 times. Its successive first-return loops must all be the same edge
word P: otherwise swap two adjacent unequal first-return loops. Such words
cannot commute, since their first return to x is their final vertex.

The word P is a simple cycle. If another vertex y occurs twice in P, then P^2
contains different first-return loops at y: one passes through x, whereas an
internal one does not. Swapping unequal adjacent loops again contradicts
uniqueness.

Because the SCC is not merely that simple cycle with multiplicity-one edges,
there is an edge off P whose source lies on P. Follow P from x to that edge,
take it, and return to x by a shortest path inside the SCC. This yields a
different first-return word Q of length q <= 2h-1. The original walk contains
at least 2h repetitions of P, hence contains P^q. Replace this by Q^|P|. The
length is unchanged. The edge words P^q and Q^|P| are different: distinct
first-return words at x cannot share a positive power, because the positions
of successive returns to x uniquely delimit each copy. This is another
contradiction to uniqueness.

For the whole graph, a walk visits SCCs in condensation-DAG order. An internal
segment in a branching SCC of h vertices has length at most 2h^2-1 if the
whole walk is unique. Acyclic singleton segments have length zero. Adding
the at most one-between-components crossing edges gives total length less
than 2N^2. Thus no length-2N^2 walk is unique. Larger powers cannot acquire
an entry one by multiplying a matrix whose entries are zero or at least two.

For the converse, a walk from a vertex of a deterministic SCC back to itself
cannot leave that SCC. At every positive multiple of the cycle length, exactly
one such walk exists.

This characterizes eventual absence of matrix entries one. It does not by
itself make a deterministic pairing SCC a uniquely Hamiltonian construction:
the complete count-vector automaton is needed for that stronger inference.

## Lemma 2: reversible through-path transitions

Partition the entire row path into intervals, each containing exactly one
incoming endpoint at one of its ends. Use every vertical edge within each
interval. The opposite end is its outgoing endpoint. A singleton interval has
its incoming and outgoing endpoint at the same row. This is a valid transition
consisting only of through paths. It preserves the order of the individual
endpoints and their pairing. The same intervals give the reverse transition.

Such a partition exists if the incoming endpoint set touches either boundary,
or if two incoming endpoints are adjacent:

* If the first endpoint is row 1, take intervals starting at each endpoint and
  ending just before the next, with the last interval ending at m.
* If the last endpoint is row m, use the reflected construction.
* If adjacent endpoints occur in the interior, end intervals at their input
  endpoint up to the first of that adjacent pair, then start intervals at their
  input endpoint from the second onward. Adjacency makes the two portions meet.

If none of these conditions holds, let k be the number of incoming endpoints.
They are isolated interior positions, splitting the other rows into k+1
nonempty zero-runs. In any valid column choice an incoming endpoint has at
most one incident vertical edge, so at most k endpoint-to-zero-run attachments
are possible. Write z_j for the number of zero-runs with j attachments. Then

    z_0 + z_1 + z_2 = k+1,      z_1 + 2z_2 <= k,

so z_0 >= z_2+1. Each unattached zero-run contains at least one cup component
(a vertical path with two outgoing ends). A cap component (a vertical path
with two incoming ends) uses a doubly attached zero-run. Thus cups >= caps+1.
Isolated incoming vertices are straight through components and do not change
the endpoint count. Consequently

    outgoing endpoints = k + 2(cups-caps) >= k+2.

This argument applies to every valid transition, not just one proposed choice
of vertical edges. Rejection of closed loops cannot invalidate the inequality
for the transitions that remain.

## Corollary 3: deterministic SCCs have one or two states

The empty-prefix state has no incoming full-column transition, and the
completed-cycle state has no outgoing full-column transition. Neither is
in a cyclic SCC. Choose an ordinary state P with the largest endpoint count
in a cyclic SCC. If the
condition for a through-path partition failed, every outgoing transition would
increase that count; this contradicts the existence of an outgoing transition
inside the SCC. Therefore P has a reversible through-path transition P <-> Q.
Both states belong to the SCC. A deterministic directed cycle containing this
reversible edge has length one or two.

In either case, (T^4)_(P,P) = 1: a walk leaving this SCC cannot return to it.
The next local constructions will contradict this equality in all but the
exceptional cases.

## Lemma 4: a through interval of height at least three creates multiplicity

For every h >= 3, an h-by-4 rectangle has at least two Hamiltonian paths from
its top-left to its top-right vertex. Reflect vertically for bottom endpoints.
At each of the two base heights, one path is the vertical column zigzag.
Alternative base paths are:

    h=3:
    (1,1),(2,1),(3,1),(3,2),(3,3),(3,4),
    (2,4),(2,3),(2,2),(1,2),(1,3),(1,4).

    h=4:
    (1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(3,4),
    (2,4),(2,3),(3,3),(3,2),(2,2),(1,2),(1,3),(1,4).

Each is distinct from its column zigzag, and both paths in either pair contain
the bottom edge joining columns 1 and 2. Add two rows by replacing this edge
with the path through the new two-row strip

    top1,bottom1,bottom2,bottom3,bottom4,top4,top3,top2.

Connect its first and last vertices to the respective endpoints of the removed
edge. This includes all eight new vertices, preserves the two original path
endpoints, and leaves a common bottom edge at columns 1 and 2 for induction.
The inductively extended paths remain distinct because their previous
differences occur outside the common edge. They need not remain column
zigzags; only distinctness, endpoint preservation, and the common bottom
edge are needed by the induction.

Apply this construction to any height-h interval of the reversible partition
for P <-> Q. In all other intervals, repeat the original through transition
four times. The resulting two fillings of the complete four-column strip
both carry every individual input endpoint to the same row at the right cut.
They therefore preserve P, regardless of how its endpoints are paired outside
the strip. Each individual gadget path runs from its designated input to its
designated output, so no component closes prematurely. Different fillings
give different undirected edge sets, giving (T^4)_(P,P) >= 2.

Hence a deterministic SCC's reversible partition has interval lengths at
most two.

## Lemma 5: intervals of lengths one and two cannot be mixed

If both lengths occur, choose adjacent intervals of different lengths. Their
three-row union has two incoming endpoints, in pattern 110, 101, or 011.

For 110, two distinct four-column path covers preserve both individual
endpoint rows. The first is a straight path along row 1 together with the
column zigzag in rows 2 and 3. The second consists of these disjoint paths:

    (1,1),(1,2),(2,2),(2,3),(1,3),(1,4);
    (2,1),(3,1),(3,2),(3,3),(3,4),(2,4).

They cover all twelve vertices. Pattern 011 follows by vertical reflection.
For 101, use the two different reversible partitions 1+2 and 2+1, repeating
each for four columns. They give distinct path covers returning each input
endpoint to itself.

In all cases repeat the original through paths outside these three rows.
Again (T^4)_(P,P) >= 2. Thus every interval has length one, or every interval
has length two.

## Lemma 6: the all-singleton case is deterministic only at width two

All intervals being singletons means every row is an incoming endpoint, so m
is even. A full-column through self-loop exists at each noncrossing perfect
matching of these endpoints.

All these perfect matchings communicate in the full-column graph. For adjacent
positions i,i+1 that are not paired to each other, use their vertical edge as
a cap in one column, leaving every other endpoint straight. This joins two
different paths, so it does not close a cycle. In the next column, use the same
vertical edge as a new cup; every other endpoint is again straight. The result
is the standard adjacent reconnection e_i: i and i+1 become a pair, and their
former partners become a pair. Both columns are completely retained.

From any matching, applying e_1,e_3,..., skipping already paired positions,
reaches the adjacent-pair matching. Previously fixed pairs are unaffected.

Conversely, from the adjacent-pair matching, to build a desired outer pair
(1,2j), apply e_2,e_4,...,e_(2j-2). The inside is now the adjacent matching on
positions 2,...,2j-1, and the outside remains adjacent. Recursively build the
desired matching inside and outside. This reaches every noncrossing matching.

At m >= 4 there are at least two such matchings in the same SCC, each with a
self-loop, so that SCC is not deterministic. At m=2 the lone full pairing has
a self-loop; its other possible full-column transition closes the cycle and
cannot return. This is the asserted deterministic singleton.

## Lemma 7: the all-length-two case forces uniform alternation

The partition is now (1,2),(3,4),...,(m-1,m), with one incoming endpoint in each
pair. If the chosen endpoint orientation changes between two consecutive
pairs, their four-row pattern is 1001 in either P or Q. On that pattern an
alternative reversible partition into intervals of lengths 1 and 3 gives an
additional neighbor, different from both P and Q. This contradicts a
deterministic SCC with at most two states.

Thus the input endpoints are all odd rows or all even rows. Their number m/2
must be even, so 4 divides m.

Conversely, these alternating patterns are forced. For an even-height full
column, multiply the vertex-degree equations by alternating row signs. The
vertical contributions cancel, yielding C_out = -C_in, where C is the number
of odd-row endpoints minus the number of even-row endpoints. An alternating
input set has the extreme value +/-m/2. The only possible output set therefore
consists of every position of the opposite parity. The degree equations then
force the vertical perfect matching (1,2),(3,4),.... The endpoint pairing is
transported without any join or creation, and the next column returns it.

Every noncrossing perfect matching of the m/2 alternating endpoints gives
one deterministic two-cycle. There are Catalan(m/4) such matchings. No other
deterministic cyclic SCC remains after the preceding lemmas.

## Consequence for the grid-deletion question

At a width other than 2 or a multiple of 4, Lemma 1 supplies a finite L with
no entry one in T^L; the explicit safe choice is L = 2N^2 for N frontier
states. A uniquely Hamiltonian induced grid cannot contain L consecutive
fully retained columns: the actual Hamiltonian cycle supplies a path through
that strip, and multiplicity at least two with the same boundary pairing
would yield a second global Hamiltonian cycle. To see this precisely, keep
the original prefix and suffix edge sets fixed and replace only the strip
edges. The same boundary pairing preserves all connections to the fixed
prefix and suffix; the transfer rules exclude premature closed components.
Consequently the replacement still gives one spanning cycle. A different
strip filling changes an undirected edge set, rather than merely changing
the starting point or traversal direction of the same cycle.
Every disjoint block of L
columns therefore contains a deleted vertex:

    M(m,n) >= floor(n/L).

This is a deliberately loose bound sufficient for unboundedness. It does not
replace the much sharper, separately frozen exact formulas at widths 5,6,7.

## Provenance and review scope

The abstract graph lemma, local paths, maximum-endpoint argument, directed
Catalan reachability, and complete implication chain received independent
AI-agent logical review. The statement is a mathematical proof by finite-state
and local geometric arguments, not an extrapolation from a finite-width
numerical sweep. The earlier exact formulas at widths five, six, and seven
are separate results with their own independently checked certificates.

Column-frontier counting is standard; see
[Bodroza-Pantic et al., Enumeration of Hamiltonian Cycles in Some Grid Graphs](https://people.dmi.uns.ac.rs/~bodroza/Radovi/match43.pdf).
No connectivity theorem about 2-factor transfer graphs is used here: such
graphs permit multiple cycles and forget the pair-connectivity information
needed in this argument.

This proof has not undergone human peer review or proof-assistant
formalization. No external acceptance or adoption has been observed, and no
literature-wide priority claim is made. It has not been submitted to the
forums, whose policies restrict AI-generated mathematical content. Original
prose and any accompanying original code are offered under CC0 1.0.
