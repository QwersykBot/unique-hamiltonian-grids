# Asymptotic equality and transfer structure for thin-cylinder Hamiltonian cycles

**AI-authored research draft — 24 November 2026.**
The underlying arguments have received independent AI-agent logical review.
They have not received human peer review or proof-assistant verification.
The [review record](reviews/cylinder_transfer.md) identifies the exact reviewed
texts and the scope of that review. No literature-wide priority is asserted.

## 1. Exact model, statement, and dependency

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

For connectivity we use Sections 1–6 of the
[rectangular pairing-sector theorem](polynomial_cutoff.md) [2]: any two
retained, nonisolated, nonempty noncrossing-pairing states in the same sector
$h=|C-s|$, where $C=\sum_i(-1)^{i+1}x_i$ and $s=m\bmod2$, are joined in
both directions by full rectangular columns, without premature cycles or
empty intermediate states. Only connectivity is used here. Even widths use
only $h=0$; odd widths use only $h=1$. Both sectors are retained and
nonisolated, including the two-port case at width three. The bipartiteness
argument below is independent of this dependency.

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

## 4. Local columns preserve the shading when the seam is unused

Let \(a\) be the old support, and let \(z_i\) indicate a selected primal
vertical edge between rows \(i\) and \(i+1\), cyclically. Define the new
support by

\[
b_i=a_i\oplus z_i.                                  \tag{4}
\]

If the chosen column has input ports \(x\), output ports \(y\), and degree
two at every primal vertex, parity of the degree equation gives
\(y_i=b_{i-1}\oplus b_i\). The four colors around each primal vertex have
exactly two changes. Equivalently they satisfy [A2]: they are neither constant
nor checkerboard. A nonempty output frontier makes \(b\) mixed. In a
rectangular column the seam edge is absent, so \(z_m=0\) and the shading
\(c\) is preserved.

For actual transitions this describes the original column geometry exactly:
\(z_i=a_i\oplus b_i\), and the incoming and outgoing matchings are the
ones induced by the partial Hamiltonian paths. The application below needs
only the forward construction of rectangular connectors and their subsequent
completion to genuine Hamiltonian cycles. It does not require a syntactic
converse for arbitrary formal [B3] words.

## 5. Lifting a rectangular connector into the actual cylinder graph

Suppose actual states \(d,e\) have equal shading and their pairings are
retained, nonisolated states in the same rectangular sector. Take a connector from
\(P(d)\) to \(P(e)\). Begin with a genuine Hamiltonian prefix realizing
\(d\), and append its columns with the seam unused.

Every column is embedded in the new cylindrical strip with the wrap edge
unused. All visited vertices have degree two; the prefix remains a union of
paths because the connector's cycle-rejection rule is determined by its
pairing. Its final pairing is \(Q=P(e)\). Equation (4) preserves the shading
and gives the correct ports at each step.

Now append the remaining primal vertices, edges, and frontier stubs from a
Hamiltonian cycle realizing \(e\). This makes one Hamiltonian cycle:
collapse each old prefix path in that target cycle to an edge joining its
two frontier ports. Doing the same to the replacement prefix produces exactly
the same matching \(Q\). Consequently the union with the fixed target
suffix has the same component structure as the original target cycle.
All replacement vertices are visited and have degree two, so the single
component is Hamiltonian.

Assign this completed cycle its actual positive-window labels. Its initial
prefix is unchanged, and the window colors propagate across every new primal
vertical edge by (4). At the target cut, the pairing and shading equal those
of \(e\), so Section 3 recovers exactly \(e\). Every intermediate word is
now a column of an actual \(B\)-matrix and belongs to \(D_m\).
In particular all [B2]–[B3] forest-cycle, connectivity, and component-survival
requirements hold, as properties of that genuine cycle. We have not inferred
them by treating an enlarged formal state space as the actual graph.

The argument applies in both directions. Thus the rectangular connectivity
theorem connects actual cylinder states of a fixed shading and sector.

## 6. Even widths: every actual state lies over C = 0

For even \(m\), alternating summation of the cyclic primal degree equations
cancels every vertical edge, including the wrap edge. Hence each cylinder
transition has \(C(y)=-C(x)\).

The initial support condition [A1]/[B1] has isolated zero windows. Each such
zero contributes its two adjacent transition ports, one on each row parity,
so the initial charge is zero. Every actual state has a prefix from this
initial set; therefore every actual state has \(C=0\).

Consider the actual states

\[
f_0=2^{m-1}0,\qquad f_1=0\,2^{m-1}.
\]

The perimeter Hamiltonian cycle of an $m$-by-$2$ open rectangular strip,
embedded in the cylinder, realizes $f_0$ as its one-column $B$ word.
Rotating that cycle realizes $f_1$. Its $m-1$ positive windows form one path. They have
shadings zero and one respectively. Their port sets are \(\{1,m\}\) and
\(\{1,2\}\), each with its sole pairing, and both have charge zero.

By Section 5, any actual state of shading \(c\) is mutually reachable with
\(f_c\). The sector \(h=0\) is retained in the rectangular theorem even
when \(4\mid m\). Finally \(f_0\) and \(f_1\) are rotations of one
another, so they are the same vertex of \(D_m^*\). Every quotient vertex
is mutually reachable with that vertex.

## 7. Odd widths: every rotation orbit meets h = 1

For odd \(m\), the number of ports is even, so \(q=C-1\) is odd. Rotate
a port word one position to the right. Direct calculation gives

\[
C'=2x_m-C,\qquad q'=-q-2(1-x_m).                    \tag{5}
\]

Every rotation orbit contains a word with \(|q|=1\). Otherwise all its
\(q\)-values would have absolute value at least three, and (5) would
reverse the sign at each rotation. After the odd number \(m\) of rotations
the word returns to itself, contradicting that sign reversal.

Rotation preserves actual cylinder states, with positive labels recanonicalized.
Thus every quotient vertex has an actual representative in \(h=1\).
The same states \(f_0,f_1\) from Section 6 have \(q=1,-1\), respectively,
and opposite shadings. The rectangular \(h=1\) sector is nonisolated for
every odd \(m\ge3\). Section 5 connects any such representative of shading
\(c\) both ways to \(f_c\). Their rotation identification again proves
strong connectivity of \(D_m^*\).

## 8. Period and scope

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

## 9. Every eligible pairing occurs with both shades

At even width let $P$ be any noncrossing matching on a nonempty even port
set with $C=0$. At odd width initially suppose $P$ lies in $h=1$. For each
$c\in\{0,1\}$, the rectangular theorem supplies a roundtrip

$$
P(f_c)\longrightarrow P\longrightarrow P(f_c).
$$

Its endpoints and intermediate states are retained and nonisolated. Begin
with the genuine prefix of the seed cycle $f_c$, append the roundtrip with
the wrap edges unused, and append the seed cycle's genuine suffix at the
new final position. The path-contraction argument of Section 5 gives one
Hamiltonian cycle: the replacement prefix induces the same final matching
as the original prefix. Its shade remains $c$ throughout the connector.
Consequently the intermediate cut at $P$ realizes an actual $B$ state with
data $(P,c)$.

This argument starts with a formal rectangular matching $P$ and proves its
cylinder realization. It does not assume that realization as an input to
the connector theorem. The only actual state needed initially is $f_c$.

At odd width an arbitrary nonempty even port set can be rotated into
$h=1$ by Section 7. Rotate its matching as well, realize it with both
shades, and rotate the two realizing cycles back. Rotation preserves
complementarity of their supports. They therefore give the original
matching with both shades, although the numerical shade need not be
preserved by the rotation.

Combined with the injectivity in Section 3 and the even-width restriction
in Section 6, this identifies the actual state set exactly: both shades
of all nonempty noncrossing matchings at odd width, and both shades of
all such matchings with $C=0$ at even width.

## 10. A shading involution preserving the weighted transfer

For an actual state $d$, define $Jd$ by

$$
P(Jd)=P(d),\qquad c(Jd)=1-c(d).
$$

Section 9 supplies existence; Section 3 supplies uniqueness. Thus $J^2$ is
the identity. The reconstructed support of $Jd$ is $1-a$, since the port
differences are unchanged and the starting shade is reversed.

The positive connectivity labels are recomputed from the same $P$ and the
new positive-run matching $S$, using the components of $P\cup S$. They
are not retained from $d$. Nor is an existing prefix recolored in place:
the prefix realizing $Jd$ may have a different length and embedding, and
its own left cap is still zero. The construction in Section 9 is what
makes this operation legitimate in the actual state graph.

### 10.1 Preservation of actual edges

Take an actual edge $d\to e$ and a witnessing primal column. Its input
and output matchings are $P=P(d)$ and $Q=P(e)$; let $z_i$ indicate its
selected vertical edges, including the wrap edge. Apply the same column
to a genuine prefix realizing $Jd$. The input matching is still $P$, so
current-component connectivity and rejection of closed components have
exactly the same outcome. The output matching is $Q$.

Append a genuine suffix for $Je$. Its frontier matching is $Q$, so the
path-contraction argument again completes one Hamiltonian cycle. Color
propagation across the inserted column gives

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

### 10.2 Descent with multiplicities

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

## 11. The involution exchanges the exact terminal sets

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

## 12. Even widths: equal leading constants and an exponential error

Fix even $m\ge4$. Let $f$ be the row vector whose entry at a quotient
orbit is the number of first-column states in that orbit. The first-column
set is invariant under the dihedral symmetries, so a nonzero entry is the
orbit's size. Let $g_c,g_{nc}$ be column indicators of the two terminal
orbit sets. The exact walk enumeration of [1] is

$$
h_m^c(n+1)=fT^n g_c,\qquad
h_m^{nc}(n+1)=fT^n g_{nc},\qquad n\ge0.
$$

Sections 6 and 8 make $T$ primitive. Let $\rho>0$ be its Perron
eigenvalue, with positive right and left vectors $r,\ell$, normalized by

$$
Tr=\rho r,\qquad \ell T=\rho\ell,\qquad \ell r=1.
$$

Since $U$ commutes with $T$, the vector $\ell U$ is another positive
left Perron vector. Uniqueness gives $\ell U=\alpha\ell$ with
$\alpha>0$; applying $U$ twice gives $\alpha^2=1$, hence
$\ell U=\ell$. Section 11 gives $Ug_c=g_{nc}$, so

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

## 13. Odd widths and state counts

### 13.1 Cancellation of the negative peripheral eigenvalue

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

### 13.2 Exact numbers of unreduced states

Let $\mathrm{Cat}_j=\frac1{j+1}\binom{2j}{j}$. The exact state
identification in Section 9 yields

$$
|V(D_m)|=2\sum_{j=1}^{\lfloor m/2\rfloor}
  \binom{m}{2j}\mathrm{Cat}_j\quad(m\text{ odd}),
$$

and

$$
|V(D_{2p})|=2\sum_{j=1}^{p}\binom pj^2\mathrm{Cat}_j.
$$

The first formula chooses any nonempty even port set and one of its
noncrossing matchings. The second chooses equal numbers of ports from the
two row parities, exactly the condition $C=0$. Both have two shade choices.
For widths 3 through 10 the values are
$6,12,40,64,252,364,1668,2234$, agreeing with Table 1 of [1]. This finite
agreement is a consistency check; it is not used to prove realization or
any asymptotic assertion.

## 14. Sources, attribution, and bounded literature check

1. O. Bodroža-Pantić, H. Kwong, M. Pantić (2015),
   [A Conjecture on the Number of Hamiltonian Cycles on Thin Grid Cylinder Graphs](https://dmtcs.episciences.org/en/articles/2113/download),
   *DMTCS* **17:1**, 219–240,
   DOI [10.46298/dmtcs.2113](https://doi.org/10.46298/dmtcs.2113).
   Relevant printed pages: 221, coloring convention; 224, [A1]–[A4];
   225–227, prefix connectivity and [B1]–[B4]; 228, actual states and
   symmetry quotient; 237, period witnesses; 238, the stated questions.
2. [Polynomial cutoff for unique full-column fillings](polynomial_cutoff.md),
   Sections 1–6. This application uses the published source at commit
   `7f5f0c1268a4538e52e1fd16c4c0a51d25eca743`, SHA-256
   `46ab4d73958ff6b46aa49c2362e7ee446903388e5c13c79b5f776378bb266453`.
   Its quantitative refinement is unnecessary for the application; the
   nonempty pairing-sector connectivity conclusion is the dependency.
3. N. R. Beaton, J. W. Eng, C. E. Soteros (2016),
   [Polygons in restricted geometries subjected to infinite forces](https://www.nicholasbeaton.com/papers/BES2016.pdf),
   Section 4.1. This is relevant prior pairing-state connectivity work:
   the Hamiltonian 1-patterns that occur in Hamiltonian polygons form a
   strongly connected graph, by concatenating containing polygons using
   the construction in the proof of Theorem 6. It is not cited here as a
   correspondence with the exact 2015 cylinder $B$ states.
4. J. Đokić, K. Doroslovački, O. Bodroža-Pantić (2023),
   [A Spanning Union of Cycles in Thin Cylinder, Torus and Klein Bottle Grid Graphs](https://www.mdpi.com/2227-7390/11/4/846),
   *Mathematics* **11**, 846, especially Sections 4 and 7.
5. J. Đokić, K. Doroslovački, O. Bodroža-Pantić (2024),
   [The structure of the 2-factor transfer digraph common for thin cylinder, torus and Klein bottle grid graphs](https://doiserbia.nb.rs/img/doi/0354-5180/2024/0354-51802401057D.pdf),
   *Filomat* **38:1**, 57–65, especially Definition 3 and Theorem 5.

The transfer method, path connectivity information, and concatenation of
realizable patterns are established ideas. The application above provides
an explicit correspondence and path lifting for the particular window-label
model in [1]. The later structural results [4]–[5] concern binary outlet-word
2-factor transfer graphs, which allow several cycles and use a different
state model. Their similarly named matrices must not be identified with
$T_m^*$ in [1] without a correspondence theorem.

A bounded primary-source search on 24 November 2026 found no exact prior
resolution of these questions or the asymptotic conjecture in the sources inspected. This is neither
an exhaustive literature review nor a novelty certification. No third-party
paper is redistributed here. The argument and its AI review status remain
open to mathematical correction. No sign pattern for the coefficients of
$K_m$, sharp cylinder exponent, or uniform spectral gap is claimed.
