# A self-contained reconstruction of the \(2k\) bounded construction

**Separate proof draft, 24 November 2026. No novelty claim.** The bound
\(M(4k,n)\le2k\) for every \(k\ge1,\ n\ge3\) is already stated in
[Maxime Jaccon's MathOverflow question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and [Lucien Jaccon's Mathematics Stack Exchange crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles).
Full credit for that bound remains with the prior construction. This note
gives explicit retained vertices and a self-contained uniqueness proof,
so subsequent deductions can use the bound without relying on an unshown
construction. It does not modify any earlier frozen artifact.

Here \(M(m,n)\) is the minimum number of vertices deleted from an
\(m\)-by-\(n\) rectangular grid whose remaining induced graph has exactly
one Hamiltonian cycle, counted as an undirected edge set.

## 1. The deleted vertices

Fix integers \(k\ge1\) and \(n\ge3\), and put \(m=4k\). Rows and columns
are numbered from one. Delete precisely the following \(2k\) vertices:

* In column 1, delete rows \(1,5,9,\ldots,4k-3\).
* In column \(n-1\), delete rows \(3,7,11,\ldots,4k-1\) when \(n\) is
  odd, and rows \(2,6,10,\ldots,4k-2\) when \(n\) is even.

Retain every other vertex. The two specified columns are distinct even
when \(n=3\), so there are exactly \(2k\) deletions.

Equivalently, the graph consists of a one-column left cap, \(n-3\) full
interior columns, and a two-column right cap. Write \(X=n-1\) and \(Y=n\)
for the right-cap columns. The final column \(Y\) is always full.

## 2. The left cap and all full columns are forced

Consider any Hamiltonian cycle of the retained graph. In column 1, the
retained vertices form \(k\) vertical three-vertex blocks at rows
\(4j+2,4j+3,4j+4\), for \(0\le j<k\). Each block endpoint has exactly
two neighbors: its middle vertex and the vertex to its right. Both edges
must be selected. This forces the two vertical block edges and the
outgoing horizontal edges at every even row; the middle vertex cannot
use a horizontal edge.

The required neighbors to the right exist also when \(n=3\): in that
case \(X=2\), its deleted rows are \(3\bmod4\), and all even-row
vertices remain.

For a full interior column, let \(i_r,o_r\in\{0,1\}\) denote its selected
incoming and outgoing horizontal edges at row \(r\), and let \(v_r\)
denote the vertical edge between rows \(r,r+1\), with \(v_0=v_m=0\).
Degree two requires

\[
i_r+o_r+v_{r-1}+v_r=2.
\]

Multiplying by alternating row signs and summing cancels the vertical
terms and the right-hand side because \(m\) is even. Thus the signed
port count \(C=\#\{\text{odd ports}\}-\#\{\text{even ports}\}\) obeys
\(C_{\mathrm{out}}=-C_{\mathrm{in}}\). If the incoming ports are every
even row, their count is \(-m/2\), forcing the outgoing set to be every
odd row; the reverse holds for odd incoming ports. Consequently
\(i_r+o_r=1\), and the degree equations force

\[
v_1=1,\quad v_2=0,\quad v_3=1,\quad\ldots,\quad v_{m-1}=1.
\]

Every path end shifts to the opposite row in its two-row block. This is
the unique transition; it creates or joins no partial paths. After the
\(n-3\) full columns, the incoming ports of \(X\) are therefore all even
rows when \(n\) is odd, and all odd rows when \(n\) is even.

In either case the forced prefix consists of disjoint paths pairing
consecutive ports in their vertical order:

\[
P=(1,2),(3,4),\ldots,(2k-1,2k).
\]

It includes every retained prefix vertex. All other edges across the
cut into \(X\) have already been forced absent, even if such edges exist
in the induced graph.

## 3. The even-port right cap

It suffices to analyze incoming ports at rows \(2,4,\ldots,4k\), with
the rows \(3,7,\ldots,4k-1\) deleted from \(X\). Reflecting rows by
\(r\mapsto m+1-r\) gives the odd-port case and the stated deletion
pattern \(2,6,\ldots,4k-2\). Reflection preserves the consecutive
pairing \(P\).

The retained pieces of column \(X\) are:

* the top pair \(X_1,X_2\);
* the triples \(X_{4j},X_{4j+1},X_{4j+2}\), for \(1\le j<k\);
* the bottom singleton \(X_{4k}\).

At each deleted \(X\) row, the corresponding vertex of \(Y\) has exactly
its two vertical neighbors, so both vertical edges are forced.
At the top, \(X_1\) has no selected incoming edge, so it forces
\(X_2X_1\) and \(X_1Y_1\); then \(Y_1Y_2\) is forced.
At the bottom, the incoming edge at \(X_{4k}\) and the deleted vertex
above it force the rung \(X_{4k}Y_{4k}\).

All references here to unavailable incoming edges use the preceding
prefix proof. A retained vertex at a nonport may have a physical
cross-cut neighbor, but a Hamiltonian cycle cannot select that edge.

## 4. The three possible fillings of an inner ladder

For an inner triple beginning at row \(r=4j\), label its six vertices

\[
A=X_r,\quad L=X_{r+1},\quad B=X_{r+2},\qquad
C=Y_r,\quad R=Y_{r+1},\quad D=Y_{r+2}.
\]

Each of the four corners \(A,B,C,D\) has exactly one forced selected
edge outside this two-column, three-row ladder. For \(A,B\) it is the
incoming edge from the prefix; for \(C,D\) it is the vertical edge
leading toward an adjacent deleted-\(X\) row. The middle vertices
\(L,R\) have no selected exterior edge.

There are exactly three internal degree completions:

| Completion | The two paths inside the ladder |
|---|---|
| Straight | \(A-L-B\) and \(C-R-D\) |
| Top short | \(A-C\) and \(B-L-R-D\) |
| Bottom short | \(B-D\) and \(A-L-R-C\) |

To check completeness, first omit the middle rung \(LR\). Both middle
vertices must then use their two vertical edges, giving the straight
completion. If \(LR\) is selected, each middle vertex must choose one
vertical neighbor. Choosing the same end on both sides gives one of
the two displayed short/long cap completions. Choosing opposite ends
leaves the other two corners nonadjacent and unable to attain their
required internal degree one. These are all cases.

## 5. Any turn would close a proper cycle

Process the inner ladders from top to bottom. The invariant before
ladder \(j\) is that its corners \(A\) and \(C\) are the two ends of the
same already fixed path outside the ladder.

For the first ladder, this path follows the prefix pair joining ports
at rows 4 and 2, then the top detour
\(X_2-X_1-Y_1-Y_2-Y_3-Y_4\). Thus its ends are \(A=X_4\) and
\(C=Y_4\), as required.

Both nonstraight ladder completions join \(A\) to \(C\). They would
close that existing path into a cycle while the distinct vertices
\(B,D\) still remain outside it. Such a proper cycle cannot be part
of one Hamiltonian cycle. Therefore the straight completion is forced.

With the straight completion, the active path now has ends \(B,D\).
The next fixed prefix pair joins \(B=X_{4j+2}\) to \(X_{4j+4}\),
while the forced vertical \(Y\)-edges through row \(4j+3\) join \(D\)
to \(Y_{4j+4}\). These are the corners \(A,C\) of the next ladder.
The invariant is preserved, and another prefix component has been
incorporated.

After all \(k-1\) inner ladders, this one path has incorporated every
prefix component and all the processed right-cap vertices. Its ends
extend to \(X_{4k}\) and \(Y_{4k}\), where the forced bottom rung
closes a single cycle. Every retained vertex belongs to it.

When \(k=1\), there are no inner ladders. The one prefix path, the
top detour, the full \(Y\) rail, and the forced bottom rung directly
give the same conclusion. When \(n=3\), the full interior is empty
and the left cap supplies the required even ports directly.

All selected edges were forced in any hypothetical Hamiltonian cycle.
The described choices also explicitly produce one spanning cycle.
Hence the retained induced graph has exactly one Hamiltonian cycle.
Together with the count of deletions, this proves

\[
\boxed{M(4k,n)\le2k\quad\text{for all integers }k\ge1,\ n\ge3.}
\]

## Independent finite checks and scope

The accompanying verifier constructs the retained vertex set directly
from Section 1 and counts cycles by branching on undirected graph edges,
with degree-two propagation and rejection of proper closed components.
The counter has no frontier-state, transfer-matrix, or SCC imports.
A separate vertex-path enumerator checks five small control graphs
with zero, one, and multiple cycles.

The recorded run checks 24 constructions: widths \(4,8,12,16\) and
lengths 3 through 8. Every case has exactly \(2k\) deleted vertices
and exactly one Hamiltonian cycle. It also exhaustively verifies the
three local ladder completions. The run took approximately 0.020 CPU
seconds. Counts are capped at two: zero and one are exact; two means
at least two distinct undirected cycles.

These finite checks supplement the all-\(k\), all-\(n\) proof; they
do not establish it by extrapolation. The construction was reached
independently by a small exact cap search and by a second AI agent's
geometric argument. No human peer review, proof-assistant formalization,
novelty of the prior upper bound, or external adoption is claimed.
Original prose and code are offered under CC0 1.0.
