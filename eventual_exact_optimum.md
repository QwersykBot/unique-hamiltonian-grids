# Eventual exact optimum at widths divisible by four

**Reviewed corollary, 24 November 2026.** This note derives a further
consequence of the full-column SCC classification and its elementary walk
bound. The final equality uses the accompanying self-contained reconstruction
of the previously stated upper bound, credited explicitly below. Earlier
frozen proofs and archives remain unchanged.

Let \(M(m,n)\) be the minimum number of vertices deleted from an \(m\)-by-\(n\)
grid so that the remaining induced graph has exactly one Hamiltonian cycle,
counted as an undirected edge set. Fix an integer \(k\ge1\), put \(m=4k\), and
write

\[
N_m=1+\sum_{j=0}^{\lfloor m/2\rfloor}\binom{m}{2j}
          \frac{1}{j+1}\binom{2j}{j},
\qquad L=2N_m^2.
\]

Then, for every \(n\ge3\),

\[
M(4k,n)\ \ge\ \min\left\{2k,\left\lfloor\frac nL\right\rfloor\right\}.
\tag{1}
\]

Consequently, using the accompanying reconstruction of the previously stated
construction \(M(4k,n)\le2k\),

\[
\boxed{M(4k,n)=2k\quad\text{for every }n\ge 2kL=4kN_{4k}^{\,2}.}
\tag{2}
\]

## 1. An alternating cut costs at least \(2k\) deletions

Consider any Hamiltonian cycle \(H\) in a retained induced subgraph. An
internal cut between columns \(t\) and \(t+1\) is called alternating when
the selected crossing edges occur at every odd row or at every even row,
and at no other rows. There are exactly \(2k\) such edges.

Give each grid vertex its checkerboard sign
\(\sigma(r,c)=(-1)^{r+c}\). Let \(R\) be the retained vertices in columns
1 through \(t\), and let \(D_R\) be the deleted vertices in that same
prefix rectangle. Summing the degree-two equations over \(R\) with these
signs gives

\[
2\sum_{v\in R}\sigma(v)
 = \sum_{\substack{e\in H\\ e\text{ crosses the cut}}}
      \sigma(\text{prefix endpoint of }e).
\tag{3}
\]

Every selected edge internal to the prefix cancels in the signed sum. At an
alternating cut all \(2k\) prefix endpoints have the same checkerboard sign,
so the right-hand side is \(+2k\) or \(-2k\). The full prefix rectangle is
color-balanced because its height is even. Hence

\[
\left|\sum_{v\in D_R}\sigma(v)\right|
 =\left|\sum_{v\in R}\sigma(v)\right|=k,
\]

which forces at least \(k\) deletions in the prefix. Applying the same
argument to the suffix forces at least \(k\) deletions there. These vertex
sets are disjoint, so any Hamiltonian cycle with an alternating cut requires
at least \(2k\) deletions in total. This assertion does not require uniqueness.
The two exterior cuts have no crossing edges and are not alternating.

## 2. Restricting the transfer graph does not create a new exception

Use the full-column transfer graph \(T\) from the frozen classification
proof: its states are noncrossing frontier pairings, together with the
empty-prefix and completed-cycle states. It has \(N_m\) states. The
classification proves that at width \(4k\) its deterministic cyclic SCCs
are exactly the two-cycles on alternating endpoint sets. Every alternating
state belongs to one of these SCCs.

Remove all alternating states, and call the resulting induced directed
multigraph \(T^\circ\). This removes a union of whole SCCs. It therefore
does not split any remaining SCC: a path connecting two vertices of one
SCC cannot leave that SCC and later return. All remaining SCCs and their
internal edges are unchanged. In particular, \(T^\circ\) has no
deterministic cyclic SCC.

This whole-SCC observation is essential. Removing an arbitrary set of
vertices from a branching directed graph could create a deterministic
cyclic SCC; that inference would not be valid here without the exact
classification of the removed states.

Lemma 1 of the frozen proof states that a directed multigraph with \(S\)
vertices and no deterministic cyclic SCC has no adjacency-matrix entry
equal to one at any power at least \(2S^2\). Since \(T^\circ\) has at most
\(N_m\) states, it has no unique length-\(L\) walk with specified endpoints.

## 3. A full block would contradict uniqueness

Suppose a retained induced grid has exactly one Hamiltonian cycle and uses
\(d<2k\) deletions. Section 1 shows that its cycle has no alternating cut.
If \(L\) consecutive columns were fully retained, processing these columns
would give a length-\(L\) walk entirely in \(T^\circ\), including its two
endpoint states.

Fix the cycle edges outside this block. Another transfer walk of the same
length and with the same endpoint states gives a different filling of the
block, with the same crossing rows and the same final prefix pairing.
The transfer rules reject premature closed components. Thus attaching the
fixed suffix again gives one spanning cycle, with a different undirected
edge set. The actual block walk would therefore have to be unique,
contradicting Section 2.

This argument also covers a block touching either end of the grid: its
endpoint can be the empty-prefix or completed-cycle state. Both states
are retained in \(T^\circ\) and neither belongs to a cyclic SCC.

Every disjoint block of \(L\) columns must consequently contain a deleted
vertex. Therefore

\[
d\ge\left\lfloor\frac nL\right\rfloor
\quad\text{whenever }d<2k.
\]

Together with the alternative \(d\ge2k\), this proves (1). If
\(n\ge2kL\), it excludes every \(d<2k\). The independently reconstructed prior upper bound then yields (2).

## Dependencies, credit, and scope

The graph classification and explicit \(2N_m^2\) walk bound are taken from
grid_width_classification.md, frozen source SHA256
3b325dfe8d0e874bf2202fe8b086e3f4a5f84013d5d4720d75d2f5d8c3402fd1.
The lower bound depends on those proved lemmas and does not alter them.

The stronger bounded construction \(M(4k,n)\le2k\) is already stated in
[Maxime Jaccon's MathOverflow question](https://mathoverflow.net/questions/516913/a-boundedness-question-for-unique-hamiltonian-cycles)
and [Lucien Jaccon's Mathematics Stack Exchange crosspost](https://math.stackexchange.com/questions/5154584/a-boundedness-question-for-unique-hamiltonian-cycles).
No priority for that bound is claimed here. The accompanying
[two-column-cap construction](two_k_construction.md) now reconstructs it
explicitly, with an all-\(k\), all-\(n\) uniqueness proof. Its frozen source
is two_k_construction.md, SHA256
52f61a99433bca3f94409d3df493982a22731393dd1e5394d04b46bfbe2f5c07.
Together with the classified transfer graph, this makes the exact equality
in (2) self-contained within the accompanying mathematical sources. The
earlier \(6k\) reconstruction remains unchanged as a historical artifact.

The threshold is deliberately coarse. No sharpness or literature-wide
priority claim is made. The reasoning has received an independent AI-agent
challenge, not human peer review or proof-assistant formalization.
Original prose is offered under CC0 1.0.
