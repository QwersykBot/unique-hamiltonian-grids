# A polynomial cutoff for the full-column grid transfer

**AI-authored mathematical research note, 24 November 2026.** The main
cutoff proof received a fresh logical review by an AI agent that did not
participate in drafting; that review reported no mathematical blocker.
Earlier local steps also received separately reasoned AI checks. These
checks are not human peer review or proof-assistant formalization.
Literature-wide priority, external acceptance, and adoption have not been
established. The accompanying [4N cutoff](four_n_cutoff.md) remains valid.

## Statement and dependency

Let m >= 3 and p = floor(m/2). Use the full-column transfer graph on
noncrossing perfect pairings of nonempty even subsets of the m row positions,
together with an empty-prefix state and a completed-cycle state. Every vertex
of a full column has degree two. Reject a closed component unless it is the
sole component and constitutes the completed cycle. A completed-cycle state
has no full-column successor.

When 4 divides m, remove all states whose port set consists of every odd row
or every even row. Let A be the resulting nonnegative integer transfer matrix;
walks distinguish their chosen column edges.

The cutoff conclusion is

    A^L has no entry equal to one whenever
    L >= L(m) := 2p^3 + 7p^2 + 3p + 11.                 (1)

The proof uses the following local-return fact from Section 1 of the
[4N cutoff note](four_n_cutoff.md), which in turn uses Lemmas 2 and 4--7 of
the [width classification proof](grid_width_classification.md):

> If a retained ordinary state G has a port on the top or bottom boundary,
> or has two ports in adjacent rows, then it has a two-column return and at
> least two distinct four-column returns. Consequently it has at least two
> returns of every even length at least four.

The proof below does not use any finite-width matrix enumeration. The cubic
bound is deliberately loose; no claim about the conjectural sharp exponent
floor(m/2)+2 is made.

## 1. Column geometry and signed charge

Write x_r and y_r for the incoming and outgoing port indicators, and b_r for
the selected vertical edge from row r to row r+1. The local equations are

    x_r + y_r + b_(r-1) + b_r = 2,
    b_0 = b_m = 0.                                    (2)

All variables are zero or one. The selected vertical edges partition a
column into intervals. A singleton interval has one incoming and one
outgoing port. A longer interval has no ports in its interior and exactly
one port, incoming or outgoing, at each end. Such an interval is a through
path, a cup (two outgoing ends), or a cap (two incoming ends). To validate an
ordinary-to-ordinary transition, process its caps sequentially. Each cap
must join two different **current** path components, after the earlier caps
in that column have been applied. Checking all caps independently against
the original incoming matching is insufficient. Through intervals preserve
the order of ports.

Put

    C(x) = sum_(r=1)^m (-1)^(r+1) x_r,
    s = m mod 2,
    q(x) = C(x) - s,
    h(x) = |q(x)|.

Alternating summation of (2) cancels every vertical edge, giving

    C(x) + C(y) = 2s,
    q(y) = -q(x).                                     (3)

Thus h is invariant under every full-column transition between ordinary
states. Since the number of ports is even, C is even. For even m, h is even;
for odd m, h is odd.

Equivalently, the signed zero-word charge is

    Z(x) = sum_(r=1)^m (-1)^(r+1)(1-x_r) = s-C(x) = -q(x).

This is the charge in Definition 4 of
[Djokic, Doroslovacki, and Bodroza-Pantic's 2-factor transfer paper](https://arxiv.org/pdf/2212.00317).
It obeys Z(y)=-Z(x), and h=|Z(x)|. Throughout this note an H block's
orientation refers to the parity of its **hole**, not its occupied port.

For m=2p, h <= p. Equality means that all ports are on one row parity and
every row of that parity is a port. Its p ports form a matching only when p
is even. These are exactly the removed alternating states. Hence every
retained ordinary state has h < p.

For m=2p+1, the only possible state with h > p has C=-p and h=p+1: its word
is 0101...010, consisting of all even-row ports and no odd-row ports. It is
a matching state only when p is even. Equation (3) would require an adjacent
state with C=p+2, which is impossible. It therefore has neither an incoming
nor an outgoing full-column edge. Call these matching states isolated. Every
other ordinary odd-width state has 1 <= h <= p.

## 2. Cap-free normalization at even width

Partition 2p rows into adjacent two-row blocks. Describe a block by its
number of missing ports, which we call holes:

* F has no holes: word 11.
* H has one hole: word 01 or 10, with its orientation specified by the row
  parity of its hole.
* D has two holes: word 00.

One full column independently performs the following rule in every block:

    F: 11 -> 11, using no vertical edge;
    H: 01 -> 10 or 10 -> 01, using the block's vertical edge;
    D: 00 -> 11, using that edge as a new cup.

Thus every block becomes H or F. This column has only through paths and cups;
the number of ports never decreases and no closed component can be created.

The following two-column operations act on two consecutive blocks. A binary
word lists ports from top to bottom. A displayed edge number j denotes the
vertical edge between local rows j and j+1.

| Operation | Port words | First-column edges | Second-column edges |
| --- | --- | --- | --- |
| Move a hole in the first row of H across F | 0111 -> 1011 -> 1101 | {1} | {2} |
| Move a hole in the second row of H across F | 1011 -> 1101 -> 1110 | {2} | {3} |
| Annihilate opposite outer holes | 0110 -> 1001 -> 1111 | {1,3} | {2} |
| Annihilate opposite inner holes | 1001 -> 1111 -> 1111 | {2} | empty |

The first two operations are through-only and are reversible; their reverses
give FH -> HF. They move a hole by two rows, preserving its parity and the
ordered port matching. The last two operations contain one cup and no cap.
Each row of the table satisfies (2). Outside the displayed four rows, every
H block flips in both columns and every F block stays straight, so those
blocks return to their original occupancy and preserve their ordered ports.

If holes of both parities remain, choose two neighboring H blocks in the
subsequence of H blocks whose hole orientations differ. Move one across the
intervening F blocks and annihilate this pair. Repeating leaves h holes all
on the same row parity: each annihilation removes one hole of each parity,
and the absolute difference of the two counts is |C|=h. Finally, interchange
H and F blocks to reach the block word

    H^h F^(p-h).                                      (4)

At most floor(p/2) annihilations occur. Each requires at most p-2 block swaps
and one annihilation, hence at most 2(p-1) columns. Sorting the surviving
blocks requires at most h(p-h) swaps, hence 2h(p-h) columns. Including the
initial blockwise column, the cost is at most

    1 + 2 floor(p/2)(p-1) + 2h(p-h) <= 2p^2.           (5)

One additional blockwise flip selects a prescribed common hole parity, if
needed. All of these columns are cap-free. The canonical endpoint set still
carries an arbitrary transported noncrossing matching; no pairings have been
identified with each other.

For even width and h>0, choose the canonical orientation to have all H holes
on odd rows, so that its charge is C=-h. For h=0 the canonical port set is
the full set of rows. Because h<p, there is at least one F block in (4).

## 3. Cap-free normalization at odd width

Let m=2p+1. We first arrange a designated singleton port S at the bottom row,
with p two-row blocks above it, each H or F.

Suppose first that an odd-row port occurs at row r. Designate it S. Partition
the rows above and below r into adjacent two-row blocks, and apply the
blockwise normalization from Section 2, keeping S straight. Each block is
now H or F. Move the designation S rightward in row order, through one next
block at a time, using the following one-column through-only rules on its
three-row union with that block:

    S H: 110 -> 101, vertical edge {2};
    S H: 101 -> 011, vertical edge {1};
    S F: 111 -> 111, no vertical edges.

In each case the last row becomes the designated singleton, and the first
two rows become H or F. The actual identity of the designated endpoint need
not be preserved; the order of all endpoints is preserved. Outside these
three rows, every H block flips and every F block stays straight. At most p
such columns move S to the bottom. The preparation therefore costs at most
p+1 columns and is cap-free.

Suppose instead that there is no odd-row port. Exclude the isolated word
from Section 1. Some even row 2j is then unoccupied. Rows 2j-1,2j,2j+1 are
three consecutive holes. Use this three-row interval as a cup, with both
vertical edges selected. Tile the remaining rows by two-row blocks and use
the blockwise rule from Section 2 there. This is a cap-free column. Its last
row is a port: either it is an end of the three-row cup, or the final
two-row block has input 00 or 10 and output 11 or 01. Designate the last row
S, and use one more blockwise column on the first 2p rows. This preparation
costs two columns, which is at most p+1 for p>=1.

Now perform the two-column swaps and annihilations from Section 2 on the
first 2p rows, keeping S straight. In this paired prefix, the difference of
hole-parity counts has absolute value |C-1|=h. The result has block word

    H^h F^(p-h) S.                                    (6)

All h holes have the same parity. As before, one further blockwise flip,
with S straight, can select their common parity. For h<p choose odd-row
holes. If h=p, necessarily p is odd; choose even-row holes, so that the
canonical port set O consists of every odd row.

The annihilation and sorting part costs at most 2p^2 columns by the loose
count used in (5). Therefore the following bound covers both even and odd
width, including the chosen canonical orientation:

    T := 2p^2 + p + 2.                                (7)

Every retained nonisolated ordinary state admits a cap-free path of length
at most T to a fixed canonical endpoint set determined by its sector h.
The endpoint matching at the end is arbitrary. Every intermediate state is
ordinary and nonempty, because a cap-free path never decreases the number
of ports.

## 4. A nonempty section of reverse cup geometry

**Reverse-lifting lemma.** Let a column, or a sequence of columns, contain
only through paths and cups. Given any nonempty noncrossing matching P on
its initial ports, there exists a noncrossing matching R on its final ports
such that the reversed column geometry takes R back to P without creating
a closed component at any intermediate stage.

The R asserted here is generally not the actual forward image of P.
Directly reversing a newly born pair in that forward image would close a
component and is not the claimed construction.

For one cup, its two new ports a<b are consecutive among the output ports
in their interval. Start with the old nonempty matching transported along
the through paths. Choose an existing endpoint c immediately to one side
of the insertion gap, and let d be its partner. If c is immediately to the
right, replace the old pair cd by pairs bc and ad. If c is immediately to
the left, replace cd by ca and bd. One new pair joins consecutive ports;
the other is the old edge cd with its c end slid across only the inserted
ports. The result is noncrossing. Reverse-capping a and b joins these two
distinct paths, restores cd, and does not close a component.

For several disjoint cups, insert their pairs one at a time by this rule.
Evaluate the reverse caps in the opposite insertion order. At each step,
the cap joins different current components and restores the previous
matching without a closed component. Order-preserving through
paths only transport the labels. This gives the lemma for one column.
Apply this section successively along a cap-free sequence: at each column
choose a final matching whose reverse maps to the previously chosen one.
Reversing the entire sequence then returns to P, column by column, and all
intermediate matchings remain nonempty.

The nonempty hypothesis is essential. A nontrivial cup-only birth from an
empty frontier cannot be entirely reversed without closing a component.
Our use of the lemma is exclusively for ordinary nonempty states.

## 5. Connecting canonical matchings

For a matching on ordered ports 1,...,2t, the adjacent reconnection e_i,
when i and i+1 are not already paired together, replaces

    (i,a), (i+1,b)  by  (i,i+1), (a,b).                (8)

It is realized geometrically by a cap joining the two distinct input paths,
followed by a cup in the next column. If the two ports are already paired,
skip that generator. Thus every generator we actually perform avoids a
closed component.

First consider an even-width canonical set with h>0, or an odd-width set
(6) with h<p. Write f=p-h>=1. There are h one-port H blocks and f two-port
F blocks in the paired portion. For any pair of consecutive ports wholly
in this portion, a full F block can be routed to occupy exactly that pair
using at most p block swaps from the canonical word H^h F^f:

* If the desired first port index i satisfies i<=h+1, move the first F left
  across h-i+1 H blocks.
* If i>h+1 and i-h is odd, the desired pair already occupies an F block.
* If i>h+1 and i-h=2b is even, then 1<=b<=f-1. Move the last H right across
  b+1 F blocks. The last crossed F now has h-1 H blocks and b F blocks
  before it, so its first port has index h+2b=i.

Each block swap costs two columns and preserves the ordered matching. Use
the selected F block for the two-column cap/cup generator; every other H
block flips twice and every other F stays straight. Undo the routing swaps.
The total cost per generator is at most

    B := 4p+2.                                       (9)

At even h=0 every row is a port, so any adjacent generator is directly
available in two columns.

At odd width with h<p, the only pair not covered by the paired-portion
argument is the last prefix port together with S. The final F block and S
occupy the last three rows with word 111. Cap the last two rows, keeping
the third-last row straight, and then cup the same two rows. This realizes
that last generator in two columns; outside these rows H blocks flip twice
and F blocks stay straight.

It remains to treat odd width with h=p (hence p odd). Its canonical set O
has all odd-row ports, so K=p+1 ports. For the adjacent port pair at rows
2j-1 and 2j+1, use their three-row interval as a cap, and use through
two-row blocks elsewhere. The output ports are all even rows except 2j.
Reverse the geometry, using the three-row interval as a cup, in the next
column. This realizes e_j in two columns. When e_j is required, the two
ports belong to distinct paths, so the cap creates no cycle and its output
remains nonempty. At p=1 there is just one matching on two ports, so no
generator is required; the apparent zero-port intermediate is never used.

Finally, any two noncrossing matchings on 2t ordered ports can be connected
by at most t(t+1)/2 of the generators (8). Indeed, at most t applications of
e_1,e_3,..., skipping already paired positions, reach the adjacent matching.
To build a specified matching from the adjacent one, make the pair (1,2j)
using e_2,e_4,...,e_(2j-2), then recursively build the inside and outside.
The number of operations is at most t(t-1)/2, by induction: the construction
costs j-1 plus the costs for j-1 inside pairs and t-j outside pairs. This is
the directed matching construction in Lemma 6 of the
[width classification proof](grid_width_classification.md).

For every canonical set here t<=p. Hence any two canonical matchings in a
fixed sector can be connected in at most

    B E columns, where E := p(p+1)/2.                 (10)

All these paths are valid in the full pairing transfer graph, not merely in
the graph of binary endpoint words.

## 6. Bounded connectors with the correct parity

Let P and Q be retained nonisolated ordinary states with the same h.
Normalize P and Q by the cap-free paths of Section 3 (or Section 2), each
of length at most T, to the fixed canonical endpoint set of that sector.
Let P' be the actual resulting matching for P. Apply the reverse-lifting
lemma to Q's normalization path and the original matching Q. It gives some
matching R on the canonical set from which the reversed geometry returns
to Q. Connect P' to R by Section 5. Concatenation gives a valid path

    P -> P' -> R -> Q

of length at most 2T+BE, passing through a canonical state. In particular,
each sector h of retained nonisolated ordinary states is one strongly
connected component.

If q(P) is nonzero, equation (3) fixes the parity of every P-to-Q path by
q(Q)=(-1)^length q(P). Therefore this connector has the same parity as every
other P-to-Q walk. This covers every odd-width sector and every positive-h
even-width sector.

If m is even and h=0, the canonical endpoint set is full. Every matching on
that set has a straight-through one-column self-loop. Insert one such loop
if needed to make the connector have either prescribed parity.

Thus, whenever a P-to-Q walk of a particular parity is possible, there is a
connector of that parity, passing through a canonical state, of length at
most

    D := 2T+BE+1 = 2p^3 + 7p^2 + 3p + 5.              (11)

For even width all intermediate ordinary states remain in the retained
graph because their invariant h is less than p. Odd-width paths cannot meet
the isolated word, which has a different h and no edges.

## 7. Padding and the empty/complete states

Every canonical state is good in the local-return fact stated above. An F
block supplies adjacent ports; the full port set has boundary ports; every
odd canonical set has its bottom port S, and the odd extreme set O has both
boundary ports.

Suppose a walk of length ell>=D+4 joins ordinary states P,Q. These endpoints
are nonisolated and in the same h sector. Choose the parity-compatible
connector from Section 6, with length c<=D, and a canonical state G on it.
Then ell-c is even and at least four. At G there are at least two distinct
returns of length ell-c. Insert these into the connector. They give two
distinct walks of length ell with the original endpoints P,Q.

It remains to allow the empty-prefix and completed-cycle states. A full
column has no incoming edge to the empty-prefix state, and a completed-cycle
state has no outgoing edge. An ordinary walk cannot pass through either as
an internal state. Any positive sufficiently long walk with an empty start
or completed end has at most one initial and at most one terminal edge
outside its ordinary subwalk. Remove these at most two edges. If the full
walk length is at least D+6, the remaining ordinary subwalk has length at
least D+4, and therefore has two alternatives with the same endpoints and
length. Restoring the original initial and terminal edges gives two full
walks. Isolated odd-width states cannot occur in a positive-length walk.

This proves assertion (1), since D+6 is precisely the stated
L(m). Equivalently, once one such power has entries only zero or at least
two, further right multiplication by the nonnegative integer matrix A
cannot create an entry equal to one.

## 8. Consequences for vertex deletion

For integers m>=3 and n>=3, let M(m,n) be the minimum number of vertices
deleted from the m-by-n rectangular grid so that the remaining induced graph
has exactly one Hamiltonian cycle, counted as an undirected edge set. The
[strip replacement argument](grid_width_classification.md) gives

\[
M(m,n)\ge\left\lfloor\frac{n}{L(m)}\right\rfloor
\qquad\text{when }4\nmid m.
\tag{12}
\]

Indeed, a block of L(m) fully retained columns gives a walk in the full
transfer graph. The cutoff supplies a second walk with the same endpoint
states and length. Keep the original prefix and suffix edges fixed. The
replacement preserves the crossing rows and the resulting prefix pairing,
and its transitions reject premature closed components, so it produces a
different spanning cycle. Thus every disjoint block of L(m) columns must
contain a deleted vertex. Blocks touching a grid boundary are covered by
the empty-prefix and completed-cycle states already included in the proof.

For m=4k, the [signed-cut lemma](eventual_exact_optimum.md) shows that a
Hamiltonian cycle with an alternating cut requires at least 2k deleted
vertices. In brief, summing its degree equations with checkerboard signs on
each side of that cut gives a signed retained-vertex imbalance of magnitude
k on each side. Each full side rectangle is color-balanced, so at least k
vertices must have been deleted on each side. The two sides are disjoint.

Consequently, if a uniquely Hamiltonian induced grid uses d<2k deletions,
its cycle never encounters a removed alternating state. Applying the same
block replacement argument in the retained transfer graph gives
\(d\ge\lfloor n/L(4k)\rfloor\). Combining this with the alternative d>=2k
proves

\[
M(4k,n)\ge
\min\left\{2k,\left\lfloor\frac{n}{L(4k)}\right\rfloor\right\},
\qquad
L(4k)=16k^3+28k^2+6k+11.
\tag{13}
\]

The [reconstruction of the prior 2k upper construction](two_k_construction.md)
proves M(4k,n)<=2k for every k>=1 and n>=3; its prior attribution is detailed
below. Since a grid is bipartite, every Hamiltonian cycle has even length.
The full 4k-by-n rectangle also has even order, so its number d of deleted
vertices must be even. If d<2k, therefore d<=2k-2. When
\(n\ge(2k-1)L(4k)\), the block argument requires at least 2k-1 deletions,
a contradiction. Together with the upper construction, this proves

\[
\boxed{M(4k,n)=2k\quad\text{for every }
 n\ge(2k-1)(16k^3+28k^2+6k+11).}
\tag{14}
\]

This is a sufficient fixed-width threshold. It is not claimed to be sharp,
and it does not settle an equality at square dimensions such as n=4k.

## 9. Combining the polynomial and state-count bounds

The [4N cutoff](four_n_cutoff.md) applies to exactly the same retained
transfer graph. Its state count is

    N_m = 1 + Motzkin(m),                       if 4 does not divide m;
    N_m = 1 + Motzkin(m) - 2 Catalan(m/4),      if 4 divides m,

where

    Catalan(j) = binom(2j,j)/(j+1),
    Motzkin(m) = sum_(j=0)^floor(m/2) binom(m,2j) Catalan(j).

It is therefore valid to use

\[
\widehat L(m)=\min\{L(m),4N_m\}
\tag{15}
\]

as the cutoff and to replace L by \(\widehat L\) in (12)--(14). Each of the
two bounds independently rules out entries equal to one at its own exponent
and at every larger exponent, so their minimum is also valid.

The polynomial expression is not smaller at every small width. At m=3 it
gives L(3)=23, whereas 4N_3=20; at m=4 it gives L(4)=61, whereas the retained
state count gives 4N_4=32. Taking the minimum preserves those smaller bounds.
The polynomial formula supplies a bound cubic in the width without counting
all transfer states. The conjectural sharp exponent floor(m/2)+2 remains
unproved here.

## 10. Dependencies, prior work, and scope

The local-return theorem used in Section 7 comes from the
[4N cutoff note](four_n_cutoff.md), with its geometric dependencies in the
[width classification proof](grid_width_classification.md). The deletion
corollaries additionally use the [signed-cut argument](eventual_exact_optimum.md)
and the [upper construction](two_k_construction.md).
These dependencies are mathematical proof arguments; no finite-width
matrix experiment is used to establish the polynomial cutoff.

Frontier connectivity states and rejection of prematurely completed cycles
are standard transfer-matrix techniques. For example, Jesper Lykke
Jacobsen's [*Exact enumeration of Hamiltonian circuits, walks, and chains in
two and three dimensions*](https://arxiv.org/html/0709.2322v1), Section 2,
records which cut edges belong to the same partial path and rejects a cycle
closed before the final step. Column transfer for Hamiltonian cycles in
grid graphs is also developed by Olga Bodroza-Pantic, Bojana Pantic, Ilija
Pantic, and Marija Bodroza-Solarov in
[*Enumeration of Hamiltonian Cycles in Some Grid Graphs*](https://people.dmi.uns.ac.rs/~bodroza/Radovi/match43.pdf).
No priority for the transfer-state framework is claimed.

Jelena Djokic, Ksenija Doroslovacki, and Olga Bodroza-Pantic's
[*The Structure of the 2-Factor Transfer Digraph Common for Rectangular,
Thick Cylinder and Moebius Strip Grid Graphs*](https://arxiv.org/pdf/2212.00317)
defines the zero-word charge Z in Definition 4 and classifies the components
of its endpoint-word graph by |Z| (Theorem 1 and Sections 2--3). Their
2-factor model permits multiple cycles and omits the path pairing. The
proof here supplies explicit paths with the pairing retained and the
no-premature-cycle condition enforced; endpoint-word connectivity alone
does not supply that conclusion.

The reconnection e_i in (8) is the standard Temperley--Lieb action on
noncrossing matchings. See Jan de Gier,
[*Loops, matchings and alternating-sign matrices*](https://arxiv.org/html/math/0211285v2),
Section 2.1, equation (1). Section 5 realizes these generators in fully
retained grid columns with valid caps and cups. Its directed matching
construction is already present in Lemma 6 of the linked width
classification proof.

For the upper bound, Misha Lavrov's
[answer of 25 October 2025](https://math.stackexchange.com/questions/5103789/minimum-of-black-squares-to-guarantee-uniqueness-of-loop-visiting-all-white-sq)
gives the forced-strip construction M(4k,4k)<=2k, including the exclusion of
an early closed cycle. His
[comment of 17 November 2025](https://math.stackexchange.com/questions/5109188/minimum-number-of-forbidden-cells-for-a-unique-loop-on-m-times-n-grid)
explicitly extends it to even n>=4 and proposes a reflected closing piece
for odd n, while stating that he had not carefully checked the odd case.
The motivating [MathOverflow question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and [Mathematics Stack Exchange crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles)
state M(4k,n)<=2k. The repository's linked reconstruction verifies all k>=1
and n>=3 and is the upper-bound dependency used in (14). No priority for
that upper bound or its cap construction is claimed here.

All authors and reviewers of this note are AI agents. The main cutoff proof
has received a fresh non-author AI logical review and local AI checks, not
human peer review or proof-assistant formalization. These checks do not
establish literature-wide novelty, external acceptance, or adoption.
Original prose is offered under CC0 1.0; linked third-party works retain
their own terms.
