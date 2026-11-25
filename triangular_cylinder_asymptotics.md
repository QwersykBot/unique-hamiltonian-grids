# Asymptotic equality for Hamiltonian cycles on triangular cylinders

**AI-authored research draft — 25 November 2026**

> **Review status.** The complete argument has received independent AI-agent review; the [review record](reviews/triangular_cylinder.md) identifies the reviewed text and publication comparison. It has not received human peer review or proof-assistant verification. No identification with the labeled transfer matrix of [1] is asserted.

## Abstract

For a triangular grid cylinder of fixed circumference, we prove that contractible and noncontractible Hamiltonian cycles are asymptotically equinumerous. The argument uses a finite geometric transfer whose states record frontier edges, the pairing of unfinished paths, and winding parity. A unique isolated state contributes only to the two-column graph and is removed explicitly. Splicing complete cycles proves parity-complement closure and strong connectivity of the remaining actual states. Contractible cycles on two and three columns prove aperiodicity. The resulting primitive transfer commutes with parity complement, which exchanges its two terminal vectors; their Perron coefficients are therefore equal. The proof applies directly to every circumference at least three. Together with the published exact formula at circumference two, it establishes Conjecture 6 of Bodroža-Pantić, Kwong, Doroslovački, and Pantić [1].

## 1. Model and result

Fix integers \(m\ge3\) and \(a\ge2\). The graph \(G_{m,a}\) has vertices
\[
v_{i,j},\qquad 1\le i\le m,\quad 1\le j\le a,
\]
with row indices read cyclically, and edges
\[
\begin{aligned}
V_{i,j}&=v_{i,j}v_{i+1,j},\\
H_{i,j}&=v_{i,j}v_{i,j+1},\\
D_{i,j}&=v_{i,j}v_{i+1,j+1}.
\end{aligned}
\]
The last two families occur for \(j<a\). Embed the graph on an annulus by adding the indicated diagonal to every square of \(C_m\times P_a\). Thus all diagonals have the same orientation. Cycles are undirected selected edge sets on fixed labeled vertices; rotations, reflections, starting points, and traversal directions introduce no further quotient or multiplicity.

This is the graph \(T_{m,n}\) of [1, Section 2] with
\[
a=n+1.
\tag{1}
\]
Let \(N_0(m,a)\) and \(N_1(m,a)\) count its contractible and noncontractible Hamiltonian cycles. In the notation of [1],
\[
t_m^c(n)=N_0(m,n+1),\qquad
t_m^{nc}(n)=N_1(m,n+1).
\tag{2}
\]

**Theorem 1.** For each fixed \(m\ge3\), there are constants \(c_m>0\), \(\lambda_m>0\), and \(0<\theta_m<\lambda_m\) such that
\[
\begin{aligned}
t_m^c(n)&=c_m\lambda_m^{n-1}+O(\theta_m^{n-1}),\\
t_m^{nc}(n)&=c_m\lambda_m^{n-1}+O(\theta_m^{n-1}).
\end{aligned}
\tag{3}
\]
Consequently, for every fixed \(m\ge2\),
\[
\lim_{n\to\infty}\frac{t_m^{nc}(n)}{t_m^c(n)}=1.
\tag{4}
\]

Equation (4) is Conjecture 6 of [1]. At \(m=2\), retain the embedded multigraph convention, including the two parallel circumferential edges. The published calculation [1, Section 6.1] gives
\[
t_2^{nc}(1)=5,\qquad t_2^c(1)=4,\qquad
t_2^{nc}(n)=t_2^c(n)=2^{n+1}\quad(n\ge2).
\tag{5}
\]
Thus only \(m\ge3\) requires the proof below.

Fix a longitudinal meridian between rows \(m\) and \(1\). Its mod-two intersection with a cycle is the parity of the selected edges \(V_{m,j}\) and \(D_{m,j}\). An embedded simple closed curve in an annulus is contractible exactly when this parity is zero. We call the parity its *type*, denoted \(\beta(H)\in\{0,1\}\).

## 2. A finite geometric transfer

Process columns from left to right. Assign a vertical edge to its own column and an intercolumn edge to its left endpoint's column. At a cut after column \(j\), record
\[
s=(S,P,t).
\tag{6}
\]
Here \(S\subseteq\{H_i,D_i:1\le i\le m\}\) records the selected crossing edge types, with both endpoint rows retained. Absolute column indices are omitted. Truncate these edges at the cut: \(P\) pairs their individual frontier stubs through the processed prefix. Finally, \(t\in\mathbb F_2\) is the parity of all selected edges assigned to columns \(1,\ldots,j\).

The truncation is for connectivity only; an outgoing edge is counted in full for parity when its left endpoint is processed. Distinct outgoing edges ending at the same unprocessed vertex remain distinct stubs until that vertex is processed. This distinction is essential in a triangular strip.

At an internal cut of a complete Hamiltonian cycle, every processed vertex has selected degree two and no component is closed. Hence the prefix consists of unfinished paths and determines \(P\). These paths give a noncrossing matching, but we will not identify actual states with all formally possible matchings.

A state is *actual* if it occurs at an internal cut of some complete Hamiltonian cycle. Write \(\mathcal X_m\) for all actual states. This set is finite: there are at most \(2m\) frontier edge types, finitely many pairings of each subset, and two parity values. Actuality requires completion to a Hamiltonian cycle; initial reachability alone may include dead ends.

**Lemma 2 (state sufficiency).** A chosen set of vertical and outgoing edges at the next column determines its validity, its new frontier pairing, and its new parity from \((S,P,t)\) alone.

*Proof.* Attach each incoming stub to its recorded new-column endpoint. Impose degree two at every new vertex and reject any closed component during an internal transition. The remaining components pair the outgoing stubs uniquely. These tests use only the old pairing and the chosen edges. The parity increment is
\[
\delta=
\mathbf1_{\{V_m\text{ selected in the new column}\}}
+\mathbf1_{\{D_m\text{ selected outgoing}\}}
\pmod2.
\tag{7}
\]
Incoming edges were counted previously, so \(t'=t+\delta\).

At termination, choose no outgoing edges and require exactly one closed connected component. Its type is the stored parity plus the selected final-column wrap vertical contribution. No winding data for individual unfinished paths are required: pairing determines connectivity and total parity determines final type. Prefix and continuation occupy disjoint column regions of the fixed planar embedding, so substituting a realized prefix with the same frontier and pairing introduces no unrecorded crossing or vertex identification. \(\square\)

## 3. The exceptional cycle

**Lemma 3.** There is a unique Hamiltonian cycle with no selected vertical edge in either specified boundary column. It is the two-column cycle
\[
Z_m:\quad L_1,R_2,L_2,R_3,\ldots,L_m,R_1,L_1,
\tag{8}
\]
where \(L_i=v_{i,1}\), \(R_i=v_{i,2}\). Every other Hamiltonian cycle has a selected vertical edge in both boundary columns.

*Proof.* If the first column has no selected vertical, each of its vertices must use both available crossing edges, namely its horizontal and diagonal. These \(2m\) edges saturate every vertex of the second column and form (8). There can be no further column. At the right boundary, every vertex has precisely two incoming intercolumn edges. Selecting all of them saturates the preceding column in the same way. \(\square\)

The cycle \(Z_m\) has type one. Its sole cut state \(z\) has every frontier edge selected, pairs \(H_i\) with \(D_i\), and has \(t=1\). Such a frontier cannot occur after two or more processed columns: its last processed vertices already have two outgoing edges, leaving all earlier vertices in disconnected closed components. Thus its matching and parity are forced by the first column. Its opposite-parity formal state is not actual.

The next column is also saturated by incoming edges, so \(z\) has no internal outgoing transition. Producing its full outgoing frontier would require an empty incoming frontier, so it has no internal incoming transition either. It contributes precisely \(Z_m\), at \(a=2\).

Set
\[
\mathcal A_m=\mathcal X_m\setminus\{z\}.
\tag{9}
\]
Equivalently, these are the states occurring in complete cycles other than \(Z_m\). In particular every state in \(\mathcal A_m\) has a containing cycle with a selected vertical edge at both ends.

The original labeled transfer also has an isolated state used only at \(n=1\), which [1, Sections 6–7] removes before its Perron analysis. We prove the exclusion above directly; no correspondence between that labeled state and \(z\) is assumed.

## 4. Splicing and parity complement

**Lemma 4 (exact splice).** Suppose cycles \(A\) and \(B\) have selected vertical edges at a common row gap in their last and first columns, respectively. They can be joined into one Hamiltonian cycle. Every original state inside \(A\) is preserved, and every original state \((S,P,t)\) inside \(B\) becomes
\[
(S,P,t+\beta(A)).
\tag{10}
\]
The joined cycle has type \(\beta(A)+\beta(B)\).

*Proof.* Place the cycles consecutively, delete the two chosen vertical edges, and add the two horizontal seam edges joining their endpoints. The two spanning paths obtained by deletion become one spanning cycle. Modulo two, the change from the disjoint union is the boundary of an ordinary square in the underlying square grid, so it has zero meridian intersection, including at the cyclic row gap.

The altered edge of \(A\) lies in its last column, after all its old internal cuts; their data remain unchanged. Before any old cut of \(B\), its deleted first-column edge is replaced by one path through \(A\) with the same endpoints. This preserves \(S,P\). The assigned-edge parity changes by \(\beta(A)\), because the deletions and seam insertions contribute the same zero-parity square boundary. This proves (10), including the first and last original cuts. \(\square\)

We need an auxiliary whose boundary edges can accommodate prescribed joins. The square-grid subgraph contains the following three-column cycle \(U_m\):
\[
\begin{gathered}
(1,1),(m,1),(m-1,1),\ldots,(2,1),\\
(2,2),(3,2),\ldots,(m,2),\\
(m,3),(m-1,3),\ldots,(1,3),\\
(1,2),\quad\text{and back to }(1,1).
\end{gathered}
\tag{11}
\]
It visits every vertex once. Its only wrap edge is \(V_{m,1}\), so \(\beta(U_m)=1\). Its first column selects every vertical gap except 1, and its last column selects every gap except \(m\).

**Lemma 5 (gap alignment).** Given prescribed left and right joining gaps, a row rotation of \(U_m\) contains both required boundary edges.

*Proof.* The left requirement forbids one rotation, and the right requirement forbids one. At most two rotations are excluded; \(m\ge3\). \(\square\)

**Proposition 6.** The map
\[
J(S,P,t)=(S,P,t+1)
\tag{12}
\]
is an involution of \(\mathcal A_m\).

*Proof.* Choose a nonexceptional containing cycle for the given state. Prefix a rotated copy of \(U_m\), aligning its right boundary with a selected first-column vertical edge. Lemma 4 produces exactly (12). The joined cycle has more than two columns, so the new state is in \(\mathcal A_m\). Applying the same parity change twice restores the state. \(\square\)

## 5. Strong connectivity and aperiodicity

Let \(T\) be the nonnegative integer matrix on \(\mathcal A_m\) whose entry \(T_{s,s'}\) counts valid next-column edge selections producing \(s\to s'\). Multiplicities are retained; \(T\) is not merely the adjacency indicator.

**Proposition 7.** The directed support graph of \(T\) is strongly connected.

*Proof.* Take states \(d,e\) and containing cycles \(H_d,H_e\). Choose a selected right-boundary gap \(r\) of \(H_d\) and left-boundary gap \(q\) of \(H_e\). Keep both containing cycles at their original row indices.

If \(\beta(H_d)=1\), insert one copy of \(U_m\), rotated to accommodate \(r,q\). If \(\beta(H_d)=0\), insert two copies: choose any intermediate gap, and use Lemma 5 independently for their left and right requirements. In both cases the complete piece preceding \(H_e\) has type zero.

Lemma 4 preserves the exact state \(d\) and then the exact state \(e\). The successive cuts of the joined cycle give a directed walk \(d\to e\). All its states lie in \(\mathcal A_m\), since the joined cycle has more than two columns. Only the auxiliaries were rotated. \(\square\)

**Lemma 8.** For every \(m\ge3\), there are contractible Hamiltonian cycles on two and three columns, each selecting gap \(m-1\) at both ends.

*Proof.* For two columns, take the perimeter of the unrolled rectangle on rows \(1,\ldots,m\). It visits all vertices and has the required end edges.

For three columns, write the vertices as \(L_i,M_i,R_i\). Start with the rectangle perimeter, which visits every outer-column vertex and \(M_1,M_m\). Insert the remaining middle-column vertices in pairs by replacing
\[
L_rL_{r+1}
\quad\text{with}\quad
L_r-M_r-M_{r+1}-L_{r+1}.
\tag{13}
\]
For even \(m\), take \(r=2,4,\ldots,m-2\). For odd \(m\), take \(r=2,4,\ldots,m-3\), and insert the leftover vertex by replacing
\[
L_{m-2}L_{m-1}
\quad\text{with}\quad
L_{m-2}-M_{m-1}-L_{m-1}.
\tag{14}
\]
The first edge in (14) is an allowed diagonal. At \(m=3\), only (14) is needed. Each replacement inserts unused vertices into a surviving cycle edge. All vertices are therefore visited once. Neither construction uses a row-wrap edge, and gap \(m-1\) remains selected at both ends. \(\square\)

**Proposition 9.** The matrix \(T\) is primitive.

*Proof.* Self-splice two identical copies of either cycle in Lemma 8 along their common selected end gap. Lemma 4 preserves any chosen old cut state in both copies, because the first copy is contractible. The two occurrences are separated by exactly two or three columns, respectively. Hence the support graph has closed walks of lengths 2 and 3. Its strong connectivity implies that its period divides both lengths, so it is one. A finite irreducible, aperiodic nonnegative matrix is primitive. \(\square\)

## 6. Counting and the Perron coefficient

Let the row vector \(f\) count first-column edge selections producing each state in \(\mathcal A_m\). Let the column vector \(g_b\) count final-column edge selections closing a state into exactly one cycle of type \(b\). Lemma 2 gives the exact identity
\[
N_b(m,a)=fT^{a-2}g_b\qquad(a\ge3).
\tag{15}
\]
Every cycle has a unique sequence of assigned column geometries. Conversely, an accepted sequence has degree two at every vertex, no premature closed component, and exactly one final connected cycle. Thus it is Hamiltonian. All its internal states belong to \(\mathcal A_m\), and every nonexceptional cycle is included. At two columns the exact correction is
\[
N_0(m,2)=fg_0,\qquad N_1(m,2)=fg_1+1.
\tag{16}
\]

Use \(J\) also for the permutation matrix with \((Jv)_s=v_{Js}\). For any chosen next-column geometry, the degree and pairing checks are unchanged on replacing \(s,s'\) by \(Js,Js'\); equation (7) gives the same parity increment. Proposition 6 ensures the complementary states are actual. Consequently the same-geometry bijection preserves every multiplicity and gives
\[
TJ=JT.
\tag{17}
\]
At termination the same geometry closes complementary states with opposite final type. Therefore
\[
g_1=Jg_0.
\tag{18}
\]
No symmetry of the initial vector is required.

Let \(\lambda\) be the Perron root of \(T\), with positive right and left vectors \(r,\ell\), normalized by \(\ell^{\mathsf T}r=1\). Primitivity and (17) imply
\[
Jr=r,\qquad \ell^{\mathsf T}J=\ell^{\mathsf T}:
\tag{19}
\]
each positive Perron eigenspace is one-dimensional, and applying the involution twice forces its positive scalar multiplier to be one. Hence
\[
\ell^{\mathsf T}g_1=\ell^{\mathsf T}g_0.
\tag{20}
\]
The two-column contractible perimeter shows \(f\ne0\) and \(g_0\ne0\). Their common leading coefficient is therefore
\[
c=(fr)(\ell^{\mathsf T}g_0)>0.
\tag{21}
\]

Choose \(\theta\) strictly between the largest modulus of a non-Perron eigenvalue and \(\lambda\). Finite-dimensional spectral theory gives
\[
T^k=\lambda^k r\ell^{\mathsf T}+O(\theta^k).
\tag{22}
\]
Any polynomial factors from Jordan blocks are absorbed by this strict choice of \(\theta\). Combining (15), (20), and (22) gives
\[
N_b(m,a)=c\lambda^{a-2}+O(\theta^{a-2}),\qquad b=0,1.
\tag{23}
\]
The substitution \(a=n+1\) proves (3), and (5) supplies \(m=2\). This completes the proof of Theorem 1. \(\square\)

## 7. Method and scope

Pairings of frontier connections and concatenation arguments are established transfer methods. Beaton, Eng, and Soteros [2, Section 4.1] retain pairwise prefix connectivity and concatenate complete Hamiltonian polygons to prove strong connectivity of their realizable pattern graph. Complement involutions also appear in the 2-factor transfer of Đokić, Doroslovački, and Bodroža-Pantić [3, Lemma 3]. These references concern different state models.

Here the proof uses actual geometric states, an explicit isolated-state exclusion, and the effect of complete-cycle splicing on total winding parity. It does not require identifying these states or their matrix with the window-labeled transfer of [1], nor proving that every formal matching is realizable. No method-priority claim is made.

The conclusion holds for each fixed circumference. The constants and spectral separation may depend on \(m\); no uniform gap, finite-length equality, or sharp error exponent is asserted. The proof concerns the consistently oriented triangular cylinder defined above and makes no claim for arbitrary added edges. It uses no finite enumeration as a substitute for the all-width argument.

## 8. Bounded computational checks

An independent column-transfer implementation generates the entire reachable state graph at \(m=3,4\), removes states with no terminal completion, and then deletes \(z\). It retains 30 states and 180 directed arcs at \(m=3\), and 168 states and 2,032 arcs at \(m=4\). In both cases the retained graph has one strongly connected component, period one, exact weighted \(J\)-symmetry, and exchanged terminal vectors.

A separate whole-graph vertex-path enumeration agrees with the transfer on the following counts, also matching Tables 2 and 3 of [1] under \(n=a-1\):

| Circumference \(m\) | Vertex columns \(a\) | Contractible | Noncontractible |
|---:|---:|---:|---:|
| 3 | 2 | 6 | 10 |
| 3 | 3 | 48 | 42 |
| 3 | 4 | 312 | 318 |
| 4 | 2 | 8 | 21 |
| 4 | 3 | 200 | 124 |

The implementation also checks the two-column exception and the declared self-splice witnesses. The [checker](checks/check_triangular_model.py) and its [deterministic receipt](results/triangular_model.json) are supplied for reproduction. These are finite checks of conventions and implementation; the all-width conclusion follows from Sections 2–6.

## References

1. O. Bodroža-Pantić, H. Kwong, R. Doroslovački, and M. Pantić, *A limit conjecture on the number of Hamiltonian cycles on thin triangular grid cylinder graphs*, Discussiones Mathematicae Graph Theory **38** (2018), 405–427. [DOI: 10.7151/dmgt.2021](https://doi.org/10.7151/dmgt.2021). [Primary text](https://bibliotekanauki.pl/articles/31342332.pdf).
2. N. R. Beaton, J. W. Eng, and C. E. Soteros, *Polygons in restricted geometries subjected to infinite forces*, Journal of Physics A: Mathematical and Theoretical **49** (2016), 424002. [Author manuscript](https://www.nicholasbeaton.com/papers/BES2016.pdf), especially Section 4.1 and the concatenation construction in the proof of Theorem 6.
3. J. Đokić, K. Doroslovački, and O. Bodroža-Pantić, *The structure of the 2-factor transfer digraph common for thin cylinder, torus and Klein bottle grid graphs*, Filomat **38:1** (2024), 57–65. [DOI: 10.2298/FIL2401057D](https://doi.org/10.2298/FIL2401057D), especially Lemma 3. [Primary text](https://doiserbia.nb.rs/img/doi/0354-5180/2024/0354-51802401057D.pdf).
