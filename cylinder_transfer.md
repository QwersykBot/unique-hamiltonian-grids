# Asymptotic equality and transfer structure for thin-cylinder Hamiltonian cycles

**AI-authored research draft — 25 November 2026.**
This direct-splicing exposition has received independent AI-agent review.
The [review record](reviews/cylinder_transfer.md) identifies the exact candidate
and publication comparison. No human peer review, proof-assistant verification,
or literature-wide priority is asserted.

## 1. Exact model, statement, and proof route

Use the model of Bodroža-Pantić, Kwong, and Pantić [1] for Hamiltonian cycles
on the thin cylinder $C_m\times P_{n+1}$. In its Section 5, printed p. 228,
a vertex of $D_m$ is a possible integer column word of the positive-window
connectivity matrix $B$. Zero denotes a zero window; positive labels record
connectivity through the processed prefix. The graph $D_m^*$ identifies row
rotations and reflections, with positive labels recanonicalized. Its weighted
adjacency matrix is $T_m^*$. This reduction does not identify complementary
support words. Throughout, a possible column means one occurring in a
matrix of an actual Hamiltonian cycle.

Write $h_m^c(n)$ and $h_m^{nc}(n)$ for the numbers of contractible and
noncontractible Hamiltonian cycles on $C_m\times P_{n+1}$, as in [1]. The
superscripts distinguish a cycle that bounds a disk on the cylinder from
one that wraps around it. Set $h_m=h_m^c+h_m^{nc}$.

**Theorem.** The following statements hold for the exact model in [1].

- For every $m\ge3$, $D_m^*$ is strongly connected and $T_m^*$ is
  irreducible. At odd widths, both $D_m$ and $D_m^*$ are bipartite. The
  period of $T_m^*$ is one at even widths and two at odd widths.
- For every fixed even $m\ge4$, there are constants $a_m>0$,
  $\theta_m>0$, and $0<\eta_m<\theta_m$ such that, as $n\to\infty$,

  $$
  h_m^c(n+1)=\frac{a_m}{2}\theta_m^n+O(\eta_m^n),\qquad
  h_m^{nc}(n+1)=\frac{a_m}{2}\theta_m^n+O(\eta_m^n).
  $$

  In particular $h_m^c(n)\sim h_m^{nc}(n)$. The constants
  $a_m,\theta_m$ agree with those defined in Conjecture 1 of [1].
- For every fixed odd $m\ge3$, the total count has
  $h_m(n+1)=a_m\theta_m^n+O(\eta_m^n)$ with positive $a_m$ and
  $0<\eta_m<\theta_m$. Its two cycle types occur on the opposite
  length parities specified in [1].

The first two statements address Questions 1–3 and Conjecture 1 stated in
Section 8, printed p. 238 of [1]. The proof of asymptotic equality uses an
additional involution exchanging the two terminal sets; connectivity alone
does not supply equality of the leading constants. No finite-length equality
of the two counts is asserted.

The proof works with actual complete cycles and their window states.
Section 3 recovers an actual state from its frontier pairing and shade.
Sections 4–5 splice complete cycles to prove quotient connectivity and
existence of every actual state's opposite shade. Sections 7–10 establish
the weighted symmetry, terminal exchange, and asymptotics. This replaces the
rectangular-connectivity route of the pinned published exposition [4].
No charge-sector theorem or arbitrary formal-pairing realization is used.

## 2. A local parity invariant

For a state $d=(d_1,\ldots,d_m)$, put $a_i=\mathbf1_{\{d_i>0\}}$ and use
cyclic indices. Define

$$
\varepsilon(d)=\sum_{i=1}^m a_i a_{i+1}\pmod2.
$$

Let \(d\to e\) be any transition, and let \(a\) and \(b\) be its two binary
support words. By [B2], these supports satisfy Theorem 3.1 [A2] of [1]. Thus,
for each cyclic row index \(i\), the ordered block

\[
(u,v,w,z)=(a_i,a_{i+1},b_i,b_{i+1})
\]

is neither constant nor checkerboard: the excluded tuples are
\(0000,1111,0110,1001\). Every allowed block therefore has one positive
corner, three positive corners, or two adjacent positive corners.

In each allowed case the following identity holds in \(\mathbb F_2\):

\[
uv+wz+uw+vz=1+u+v+w+z.                 \tag{1}
\]

Indeed, the left side counts the positive-positive sides of the square modulo
two. With one or three positive corners this count is respectively zero or
two, and the right side is zero. With two adjacent positive corners the count
is one, and the right side is one.

Sum (1) over \(i=1,\ldots,m\). The products \(a_i b_i\) occur twice on the
left, while each \(a_i\) and \(b_i\) occurs twice on the right. Hence

\[
\boxed{\varepsilon(d)+\varepsilon(e)=m\pmod 2.}       \tag{2}
\]

For odd \(m\), every directed edge joins opposite values of
\(\varepsilon\), proving bipartiteness of \(D_m\).

A cyclic rotation merely permutes the adjacent products defining
\(\varepsilon\). Reflection reverses their cyclic order and interchanges the
two factors in each product. Both operations preserve the sum. Renaming the
positive connectivity labels also preserves it, since it leaves the support
unchanged. Thus each symmetry class used in \(D_m^*\) has a well-defined
value of \(\varepsilon\), and every quotient edge still joins opposite
values. Edge multiplicities do not affect this conclusion.

Both values occur: the states represented in [1, Section 7] by
$2^{m-1}0$ and $0^{m-1}2$ have respective values one and zero when $m$ is odd.

Finally, a walk of length \(r\) changes \(\varepsilon\) by \(r\bmod2\).
Accordingly, no power of \(T_m^*\) can have all entries positive: for even
\(r\), entries between opposite classes vanish; for odd \(r\), entries
within a class vanish. This proves nonprimitivity at odd widths.


## 3. A pairing and a shading bit determine the exact B-state

Use a cut through a column of windows, crossing the horizontal primal edges
between two successive vertex columns. The prefix consists of all primal
vertices strictly to the left of that cut, with the crossing edges retained
as frontier stubs. Every prefix vertex is fully processed. The dual windows
on the cut are the column represented by \(d\); their positive connectivity
is the connectivity through the dual prefix, including positive runs along
the cut.

For this genuine prefix state, let \(a_i=\mathbf1_{\{d_i>0\}}\), with
cyclic indices. Both colors occur. The primal frontier ports are exactly

\[
x_i=a_{i-1}\oplus a_i,\qquad a_0=a_m.
\]

There are a positive even number of ports. Because the cut comes from a
Hamiltonian cycle and crosses edges, the processed primal components are
paths, not completed cycles. They pair the ports in a noncrossing matching
\(P\). Record also the shading bit \(c=a_m\). Filling the left end of the
cylinder with a zero-colored disk places this picture in a disk without
changing any primal path connection. The zero color is the paper's exterior
color in the contractible case and its left-side color in the noncontractible
case.

Here is the precise relation to the positive-component labels. List the
positive cyclic runs as intervals \(I_j\), with start and end ports
\((s_j,t_j)\) in circular order. Their positive-tree components form a
noncrossing partition \(\pi\). For a block with runs
\(j_1,\ldots,j_k\) in circular order, its boundary contributes the pairs

\[
\{t_{j_1},s_{j_2}\},\ldots,
\{t_{j_{k-1}},s_{j_k}\},\{t_{j_k},s_{j_1}\}.       \tag{3}
\]

These are precisely the corresponding primal prefix paths: they are the
parts of the boundary of the positive tree's disk neighborhood lying away
from the frontier. Formula (3) is the fattening map.

For fixed support, this map is injective. Add the auxiliary boundary matching
\(S=\{\{s_j,t_j\}:j\}\). The components of the degree-two multigraph
\(P\cup S\) recover exactly the blocks of \(\pi\); a singleton block
gives two parallel edges, which causes no difficulty. Moreover, \(x\) and
\(c\) recover the support recursively by
\(a_0=c\), \(a_i=a_{i-1}\oplus x_i\). The paper's canonical numbering of
positive components then recovers the exact integer word \(d\).

The same conclusion follows from the disk faces: the noncrossing primal
paths determine which boundary intervals lie in the same complementary
face, and $c$ fixes their colors. Which zero face contains the filled cap
can depend on the embedding, but that information is not part of the $B$
word. At each processed primal vertex, degree two gives exactly two local
color changes; positive corners cannot touch in a checkerboard pattern.
Thus positive face connectivity agrees with positive-window dual
connectivity, including at boundary contacts.

Thus equal \((P,c)\) means equal \(B\)-states, not just equal support or
equal component counts. There is no need below to assert that every formal
shaded pairing occurs as an actual cylinder state.

## 4. Splicing complete cycles with exact canonical colors

### 4.1 Geometry and color convention

Write $G(m,a)=C_m\times P_a$, with $m\ge3$ and $a\ge2$. Rows $i$ are
cyclic and vertex columns are $j=1,\ldots,a$. Window $w_{i,j}$ lies between
rows $i,i+1$ and vertex columns $j,j+1$. A vertical edge at gap $i$
joins rows $i,i+1$ in one vertex column; a horizontal edge joins successive
columns in one row.

For a Hamiltonian cycle $H$, let $A_{i,j}\in\{0,1\}$ be its canonical
window support. The left cap has color zero; the right cap has color
$\tau(H)$, where $\tau=0$ for a contractible cycle and $\tau=1$ for a
noncontractible cycle. An edge is selected exactly when its adjacent face
colors differ [1, Section 2 and the proof of Theorem 3.2]. Fixing the left
cap fixes these colors uniquely, because the face-adjacency graph is
connected and crossing each edge prescribes whether its color changes.

### 4.2 The primal join

Take cycles $H_1$ on $G(m,a)$ and $H_2$ on $G(m,b)$. Each vertex in a
boundary column has at most one horizontal neighbor and degree two in the
cycle, so every boundary column contains a selected vertical edge. Choose
one in the last column of $H_1$ and one in the first column of $H_2$.
Rotate either input to align them at a common row gap $r$.

Place the vertex columns consecutively. Delete the two chosen vertical
edges and insert the two seam horizontals at rows $r,r+1$. Deleting one
edge from each cycle leaves two disjoint spanning paths; the two new edges
join their endpoints into one cycle. Every vertex retains degree two and
is visited. The result is a Hamiltonian cycle on $G(m,a+b)$. At $r=m$,
row $r+1$ means row 1 and the same construction uses the cyclic seam square.

### 4.3 The canonical colors of the join

Put $\beta=\tau(H_1)$ and $\gamma=\tau(H_2)$, extending original supports
to their caps by

$$
A^1_{i,0}=0,\quad A^1_{i,a}=\beta,\qquad
A^2_{i,0}=0,\quad A^2_{i,b}=\gamma.
$$

The selected aligned edges give
$A^1_{r,a-1}=1\oplus\beta$ and $A^2_{r,1}=1$.
Define the joined colors by

$$
\begin{aligned}
A'_{i,j}&=A^1_{i,j} &&(1\le j\le a-1),\\
A'_{i,a}&=S_i=\beta\oplus\mathbf1_{\{i=r\}},\\
A'_{i,a+k}&=\beta\oplus A^2_{i,k} &&(1\le k\le b-1),
\end{aligned}                                      \tag{4}
$$

with left cap zero and right cap $\beta\oplus\gamma$.

At the last vertex column of $H_1$, the vertical-edge indicator changes
from $A^1_{i,a-1}\oplus\beta$ to $A^1_{i,a-1}\oplus S_i$.
They differ only at $i=r$, deleting precisely its selected edge. At the
first column of $H_2$, the new indicator is

$$
S_i\oplus(\beta\oplus A^2_{i,1})
=A^2_{i,1}\oplus\mathbf1_{\{i=r\}},
$$

again deleting precisely the chosen edge. A seam horizontal at row $i$
has indicator $S_{i-1}\oplus S_i$, which equals one exactly at
$i=r,r+1$, including the cyclic case $r=m$.

All internal edges of $H_1$ are unchanged. Adjacent faces of $H_2$ are
both changed by $\beta$, so their edge indicators are unchanged. Its right
boundary is preserved because both the adjacent window and cap change by
$\beta$; the left boundary of $H_1$ is unchanged. Thus (4) gives exactly
the joined cycle's edges and zero left cap. Uniqueness makes it the
canonical coloring, and the joined type is $\beta\oplus\gamma$.

### 4.4 All original cuts, including the end cuts

At every original $B$-cut of $H_1$, the processed primal and window prefix
is unchanged. Its altered last-column vertical edge lies after even its
last original cut. All original colors are unchanged, so every exact
$H_1$ state, including its connectivity labels, is preserved.

At every original $B$-cut of $H_2$, its deleted first-column edge lies
strictly before the cut. That edge has been replaced by the path consisting
of $H_1$ minus its deleted edge and the two seam horizontals. Contracting
this replacement path restores the original $H_2$ prefix. Thus all frontier
ports and their matching $P$ are unchanged, while (4) changes every support
entry by $\beta$. The shade changes from $c$ to $c\oplus\beta$.
Section 3 determines the exact resulting state.

This includes the first and last $B$-columns of both inputs. If an input
was rotated for alignment, its preserved states mean the rotated states
with labels recanonicalized. When $\beta=1$, positive labels must be
reconstructed from $P$ and the new positive runs; numerical labels are
not carried over. All resulting states are actual because the join is a
complete Hamiltonian cycle.

## 5. Quotient connectivity and an actual complement for every state

### 5.1 An auxiliary noncontractible cycle

For every $m\ge3$, the following cyclic ordering is a Hamiltonian cycle
on three vertex columns:

$$
\begin{gathered}
(1,1),(m,1),(m-1,1),\ldots,(2,1),\\
(2,2),(3,2),\ldots,(m,2),\\
(m,3),(m-1,3),\ldots,(1,3),\\
(1,2),\quad\text{then back to }(1,1).
\end{gathered}
$$

The segments visit all vertices of column 1, rows $2,\ldots,m$ of
column 2, all of column 3, and finally the remaining vertex $(1,2)$.
Consecutive vertices are adjacent. The only row-wrap edge is
$(1,1)(m,1)$, so the cycle has nonzero annular homology modulo two and is
noncontractible. The ordering and verification apply also at $m=3$.

### 5.2 Contractible containing cycles and quotient reachability

Every actual state $d$ has a contractible containing cycle. Choose a cycle
$H$ containing it. If $H$ is noncontractible, append the auxiliary cycle,
rotating only the auxiliary for edge alignment. The joined type is
$1\oplus1=0$, while Section 4.4 preserves every original state of $H$,
including the exact $d$.

For actual states $d,e$, choose a contractible containing cycle for $d$
and any containing cycle for $e$. Join them in this order, rotating the
second input for edge alignment. The first cycle's states are preserved.
Its type is zero, so the second cycle's states are preserved apart from
that row rotation and label recanonicalization. The joined $B$-column
sequence therefore gives a directed walk from $d$ to $\sigma(e)$ for some
row rotation $\sigma$. In $D_m^*$ this is a walk from $[d]$ to $[e]$.
Interchange $d,e$ to obtain the reverse direction. Thus $D_m^*$ is strongly
connected and its nonnegative adjacency matrix $T_m^*$ is irreducible for
every $m\ge3$.

### 5.3 Actual shade complementation

Fix an actual state $e$ and a containing cycle $H_e$ at its original row
indices. Prefix the noncontractible auxiliary, rotating only that auxiliary
to align its right-boundary edge with a selected left edge of $H_e$.
Section 4.4 produces, at the original cut of $e$, an actual state with the
same matching $P(e)$ and opposite shade. Define it as $Je$. Section 3
gives uniqueness. Applying the construction again gives the unique actual
state with data $(P(e),c(e))$, namely $e$, so $J^2=I$.

This proves complement closure of the actual state set. It does not require
or prove realization of arbitrary formal shaded pairings.

## 6. Period and scope

For an irreducible nonnegative matrix, the period is the greatest common
divisor of the lengths of its directed closed walks. At even width, the
self-loop exhibited in [1, Section 7, printed p. 237] makes this period one.
At odd width, Section 2 makes every closed-walk length even, while the
two-cycle exhibited in the same source makes their greatest common divisor
at most two. The period is therefore exactly two.

These structural conclusions concern the exact symmetry-reduced matrix in
[1]. They do not assert strong connectivity of the unreduced graph or of
every enlarged formal state space. We next prove the extra symmetry needed
for the asymptotic statement.

## 7. A shading involution preserving the weighted transfer

For an actual state $d$, define $Jd$ by

$$
P(Jd)=P(d),\qquad c(Jd)=1-c(d).
$$

Section 5.3 supplies existence; Section 3 supplies uniqueness. Thus $J^2$ is
the identity. The reconstructed support of $Jd$ is $1-a$, since the port
differences are unchanged and the starting shade is reversed.

The positive connectivity labels are recomputed from the same $P$ and the
new positive-run matching $S$, using the components of $P\cup S$. They
are not retained from $d$. Nor is an existing prefix recolored in place:
the prefix realizing $Jd$ may have a different length and embedding, and
its own left cap is still zero. The construction in Section 5.3 is what
makes this operation legitimate in the actual state graph.

### 7.1 Preservation of actual edges

Take an actual edge $d\to e$ and a witnessing primal column. Its input
and output matchings are $P=P(d)$ and $Q=P(e)$; let $z_i$ indicate its
selected vertical edges, including the wrap edge. If $a,b$ are its old
and new supports, edge reconstruction gives $b_i=a_i\oplus z_i$.
Apply the same column to a genuine prefix realizing $Jd$. The input
matching is still $P$, so current-component connectivity and rejection of
closed components have
exactly the same outcome. The output matching is $Q$.

Append a genuine suffix for $Je$. To check the completion, collapse each
prefix path in a cycle realizing $Je$ to an edge between its frontier
ports. The replacement prefix has the same matching $Q$, so the fixed
suffix produces the same single component. Every replacement vertex is
visited and has degree two; the completed cycle is Hamiltonian. Its zero
left cap and unchanged starting prefix fix the colors. Across the inserted
column they satisfy

$$
(1-a_i)\oplus z_i=1-(a_i\oplus z_i).
$$

The resulting output has matching $Q$ and shade $1-c(e)$, and hence is
exactly $Je$. Thus $Jd\to Je$ is an actual edge. Applying $J$ again
recovers the original geometry, giving a bijection on edges. In the
unreduced paper graph the two supports already determine all $z_i$;
there is no hidden choice of geometry for a fixed ordered pair of states.

If the paper's edge definition is read directly as an admissible pair
satisfying [B2]–[B3], the witnessing-cycle formulation is equivalent:
concatenate a genuine prefix for $d$, the admissible pair, and a genuine
suffix for $e$. The resulting matrix satisfies [B1]–[B4], and Theorem 4.2
of [1] supplies the witnessing cycle.

### 7.2 Descent with multiplicities

The involution commutes with rotations and reflections. On full state
data, it complements the support and keeps the matching. A dihedral
symmetry permutes the support and the corresponding ports; this commutes
with complementation. Canonical reconstruction gives the same integer
word in either order. This argument does not assume that a rotation
preserves the single shade coordinate.

For symmetry orbits $O,O'$, the quotient entry is the number of outgoing
edges from a fixed representative $d\in O$ to states in $O'$. Symmetry
makes it independent of the chosen representative. This is the row-neighbor
weight convention used by the displayed matrices in [1]; it is not the
total number of edges between the two orbits.

The edge bijection sends those neighbors to the neighbors of $Jd$ in
$JO'$. Therefore $J$ induces an involution on quotient states preserving
all quotient weights. If $U$ is its permutation matrix and $T=T_m^*$,

$$
UT=TU,\qquad U^2=I.
$$

## 8. The involution exchanges the exact terminal sets

Let $L_c,L_{nc}$ be the last-column sets specified in [B4] of [1]. For
$d\in L_c$, zero windows are isolated and all positive windows have one
common label. Write its positive runs in cyclic order as $R_1,\ldots,R_b$,
with endpoint ports $(s_j,t_j)$. The single positive block and the
fattening formula (3) give

$$
P=\{\{t_j,s_{j+1}\}:1\le j\le b\},
$$

with indices cyclic. Each complemented positive run is one of the old
isolated zeros, with endpoints $(t_j,s_{j+1})$. Its auxiliary run edge
therefore coincides with a $P$ edge. The multigraph $P\cup S$ consists of
separate two-edge components: each new positive window is a distinct
positive block. The new word has isolated positives with distinct canonical
labels, precisely the condition for $L_{nc}$.

Conversely, for $d\in L_{nc}$ the positive windows are isolated and their
blocks are distinct. Hence

$$
P=\{\{s_j,t_j\}:1\le j\le b\}.
$$

The complemented positive runs are the old zero gaps; their auxiliary
edges join $t_j$ to $s_{j+1}$. Together with $P$ these form one alternating
component. The new positive runs therefore have one common label, and the
new zeros are isolated. This is the condition for $L_c$.

For $b=1$ the component has two parallel edges. Both conclusions still
hold. It follows that $J(L_c)=L_{nc}$ and $J(L_{nc})=L_c$, both before
and after the symmetry quotient.

## 9. Even widths: equal leading constants and an exponential error

At any width, let $\mathcal F$ be the exact first-column set [B1] of [1]. For each quotient orbit $O$, set $f_O=|O\cap\mathcal F|$.
Dihedral invariance of $\mathcal F$ makes this the orbit size on eligible
initial orbits and zero elsewhere. Let $g_c,g_{nc}$ be column indicators
of the two terminal orbit sets. The exact walk enumeration of [1] is

$$
h_m^c(n+1)=fT^n g_c,\qquad
h_m^{nc}(n+1)=fT^n g_{nc},\qquad n\ge0.
$$

Now fix even $m\ge4$. Sections 5.2 and 6 make $T$ primitive. Let
$\rho>0$ be its Perron
eigenvalue, with positive right and left vectors $r,\ell$, normalized by

$$
Tr=\rho r,\qquad \ell T=\rho\ell,\qquad \ell r=1.
$$

Since $U$ commutes with $T$, the vector $\ell U$ is another positive
left Perron vector. Uniqueness gives $\ell U=\alpha\ell$ with
$\alpha>0$; applying $U$ twice gives $\alpha^2=1$, hence
$\ell U=\ell$. Section 8 gives $Ug_c=g_{nc}$, so

$$
\ell g_c=\ell U g_c=\ell g_{nc}.
$$

No invariance of the starting vector $f$ is needed. In particular this
argument does not imply equality of the finite counts.

Define $a_m=(fr)\ell(g_c+g_{nc})>0$. The strict Perron spectral gap gives
some $0<\eta_m<\rho$ for which

$$
h_m^c(n+1)=\frac{a_m}{2}\rho^n+O(\eta_m^n),\qquad
h_m^{nc}(n+1)=\frac{a_m}{2}\rho^n+O(\eta_m^n).
$$

One may choose $\eta_m$ strictly above every subdominant eigenvalue
modulus and strictly below $\rho$; this absorbs polynomial factors from
possible subdominant Jordan blocks. The constants are for each fixed
width; no uniform spectral gap in $m$ is asserted.

Let $H_m^c,H_m^{nc}$ be the generating functions with coefficients
$h_m^c(n+1),h_m^{nc}(n+1)$, and put
$H_m=H_m^c+H_m^{nc}$, $K_m=H_m^c-H_m^{nc}$. The Perron projection is
positive for the terminal sum and zero for the terminal difference. Thus
$H_m$ has a genuine simple pole at $\rho^{-1}$, while $K_m$ has radius
of convergence strictly greater than $\rho^{-1}$. This is the strict
radius comparison in Question 3 of [1].

Write the reduced proper rational part of $H_m$ as $p_m(x)/q_m(x)$.
Its simple-pole coefficient is

$$
a_m=-\rho\,\frac{p_m(\rho^{-1})}{q'_m(\rho^{-1})}.
$$

Therefore $\rho=\theta_m$ and $a_m$ is exactly the constant in
Conjecture 1 of [1]. This proves its stated asymptotic equivalence.

## 10. Odd widths: cancellation of the negative peripheral eigenvalue

At odd width, let $E$ be diagonal with entries
$(-1)^{\varepsilon(d)}$ on quotient states. Section 2 gives $ETE=-T$.
Complementation changes the invariant by

$$
\varepsilon(Jd)=\varepsilon(d)+m\pmod2,
$$

so $UE=-EU$. Irreducibility and period two give peripheral eigenvalues
$\rho$ and $-\rho$, with right/left eigenvectors $r,\ell$ and
$Er,\ell E$, respectively. Again $\ell r=1$ and $\ell U=\ell$.
The terminal sum $g=g_c+g_{nc}$ satisfies $Ug=g$. Consequently

$$
\ell Eg=\ell U E U g=-\ell Eg=0.
$$

The negative peripheral contribution therefore vanishes in $fT^ng$.
For some $0<\eta_m<\rho$,

$$
h_m(n+1)=a_m\rho^n+O(\eta_m^n),\qquad a_m=(fr)\ell g>0.
$$

The parity restriction in Theorem 2.1 of [1] states that, at odd width,
$h_m(n)=h_m^{nc}(n)$ for even $n$ and $h_m(n)=h_m^c(n)$ for odd $n$.
It follows that

$$
h_m^{nc}(2n)\sim a_m\rho^{2n-1},\qquad
h_m^c(2n+1)\sim a_m\rho^{2n}.
$$

Period two alone would not give cancellation for arbitrary endpoint
vectors. Here the endpoint-exchanging involution supplies that extra step.

## 11. Sources, attribution, and scope

1. O. Bodroža-Pantić, H. Kwong, M. Pantić (2015),
   [A Conjecture on the Number of Hamiltonian Cycles on Thin Grid Cylinder Graphs](https://dmtcs.episciences.org/en/articles/2113/download),
   *DMTCS* **17:1**, 219–240,
   DOI [10.46298/dmtcs.2113](https://doi.org/10.46298/dmtcs.2113).
   Relevant parts: Section 2 and Theorem 3.2, canonical colors and edge
   reconstruction; Sections 4–5, [B1]–[B4], actual states, and quotient;
   Section 7, period witnesses; Section 8, the questions and conjecture.
2. N. R. Beaton, J. W. Eng, C. E. Soteros (2016),
   [Polygons in restricted geometries subjected to infinite forces](https://www.nicholasbeaton.com/papers/BES2016.pdf),
   Section 4.1 and the construction in the proof of Theorem 6.
3. J. Đokić, K. Doroslovački, O. Bodroža-Pantić (2024),
   [The structure of the 2-factor transfer digraph common for thin cylinder, torus and Klein bottle grid graphs](https://doiserbia.nb.rs/img/doi/0354-5180/2024/0354-51802401057D.pdf),
   *Filomat* **38:1**, 57–65, Definition 3 and Lemma 3, especially pp. 64–65.
4. [Asymptotic equality and transfer structure for thin-cylinder Hamiltonian cycles](https://github.com/QwersykBot/unique-hamiltonian-grids/blob/e8cbd3996559d95857a37e59f14ed8704904d9ae/cylinder_transfer.md),
   published AI-authored snapshot at commit
   `e8cbd3996559d95857a37e59f14ed8704904d9ae`, 28,155 bytes, SHA-256
   `bbf8ccefdab549967892b3623fce9e1390e459905f60510853dac220fc5f90a0`.
   This is exposition provenance; the arguments used here are included above.
5. *Direct cycle splicing for the exact thin-cylinder transfer*, internal
   AI-authored proof note, 24 November 2026, `cylinder-direct-splicing-lemma.txt`,
   14,672 bytes, SHA-256
   `a36a91a5382a0faec583eea4e7f98689ab5880411f02e5bf4063731022915b95`.
   Sections 4–5 above integrate its direct construction and color calculation.

Concatenation-based connectivity is established work. Beaton, Eng, and
Soteros [2, Section 4.1] join polygons containing two realizable Hamiltonian
1-patterns in either order, using their Theorem 6 construction, to prove
strong connectivity. The present application supplies the canonical-color
and exact-state checks for the particular window-label model of [1].

Complement methods also appear explicitly in [3, Lemma 3]: the involution
$a\leftrightarrow f$, $b\leftrightarrow e$, $c\leftrightarrow d$ preserves
their local transfer rules and induces outlet-word complementation,
identifying the two odd-width components. Their binary outlet-word graph
represents 2-factors, which may have several cycles. It is a different state
model. Actual $B$-state complement closure, terminal exchange, and the exact
weighted quotient are established separately in Sections 3–8 here.

The splice proves the main theorem without classifying all formal pairings.
The optional exact state-count formulas in [4, Section 13.2] retain their
separate formal-realization argument and are omitted here. The published
manuscript reports a bounded primary-source search on 24 November 2026
that found no exact prior resolution in the sources inspected; that was
neither an exhaustive search nor a novelty certification. This integration
claims no new literature-wide search. No third-party paper is redistributed.

This draft remains open to mathematical correction. No strong-connectivity
claim for the unreduced graph,
finite-length equality, coefficient-sign rule for $K_m$, sharp cylinder
exponent, or uniform spectral gap is added.
