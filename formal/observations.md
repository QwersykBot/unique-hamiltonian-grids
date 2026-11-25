# Physical observations of cylinder parity

The bounded-weight theorem has an interpretation in terms of what an observer
can learn from the edges of a Hamiltonian cycle. This note explains the exact
likelihood calculation and the finite normalization results. It uses the same
consistently triangulated cylinder, physical edge sets, and meridian-parity
classes as the [main formal development](README.md).

Fix a circumference $m\ge3$ and let $L$ be the number of vertex columns. A cycle
$C$ is an unordered Hamiltonian edge set on the fixed vertex labels. Its base
weight is

$$
W_w(C)=\prod_{e\in C}w_e.
$$

The field $w$ is shared by both parity classes. Unit activities give equal
weight to each edge set. Throughout, parity means the existing sum of physical
meridian-edge indicators modulo two; the Lean statements use this definition
directly.

## Independent noisy edge observations

For a fixed report $y$, let $q_1(e;y)$ be its likelihood factor when edge $e$
is selected, and let $q_0(e;y)$ be its likelihood factor when $e$ is absent.
Conditional independence of the edge reports gives

$$
\mathcal L_y(C)
=\prod_{e\in E(G)}
\begin{cases}
q_1(e;y),&e\in C,\\
q_0(e;y),&e\notin C.
\end{cases}
$$

There is one factor for every actual unordered ambient edge, including the
absent edges. For $q_0(e;y)>0$, define

$$
c_y=\prod_{e\in E(G)}q_0(e;y),\qquad
w_y(e)=w_e\frac{q_1(e;y)}{q_0(e;y)}.
$$

The exact identity is

$$
W_w(C)\mathcal L_y(C)=c_y W_{w_y}(C).
$$

Thus the unnormalized report mass in class $p$ satisfies

$$
M_p(y)=\sum_{C:\,p(C)=p}W_w(C)\mathcal L_y(C)
      =c_y Z_p(w_y),
$$

where $Z_p$ is the existing physical weighted parity count. The common factor
$c_y$ depends on the report and graph, and is independent of the selected
cycle and its parity. It may become arbitrarily small with length; strict
positivity is sufficient for this argument.

[NoisyCylinderLikelihood.lean](NoisyCylinderLikelihood.lean) proves these
product and sum identities on the existing `Selection` and `ParitySelection`
types. The identities hold for every $L$, including empty parity classes.

### Uniform finite bound

Suppose fixed constants satisfy $\epsilon>0$ and $r_->0$, and on actual edges

$$
\epsilon\le w_e\le M,\qquad
r_-\le\frac{q_1(e;y)}{q_0(e;y)}\le r_+.
$$

Then $w_y(e)$ lies in the fixed interval
$[\epsilon r_-,Mr_+]$. The
[physical weighted theorem](WeightedCountImbalance.lean) supplies $N\ge2$ and
$0\le\rho<1$, depending only on $m$ and these bounds, such that

$$
|M_0(y)-M_1(y)|\le\delta_L\bigl(M_0(y)+M_1(y)\bigr),\qquad
\delta_L=\rho^{\lfloor(L-2)/N\rfloor},\qquad L\ge3.
$$

The constants are chosen before the length, report, activity field, or
likelihood fields. They therefore cover arbitrary position dependence and
fields or reports that vary with length, as long as the same bounds apply.
Values assigned to nonedges have no effect.

When the pooled report mass is positive, normalization gives

$$
\left|\frac{M_0(y)}{M_0(y)+M_1(y)}-\frac12\right|
\le\frac{\delta_L}{2}.
$$

This is the posterior under the original common edge-product prior. The
normalization and its uniform physical application are proved in
[NoisyParityObservation.lean](NoisyParityObservation.lean).

### Binary reports

Let $\mathrm{fp}_e$ and $\mathrm{fn}_e$ denote the false-positive and
false-negative probabilities. The likelihood fields are

| Report on edge $e$ | $q_0(e;y)$ | $q_1(e;y)$ |
|---|---|---|
| Present | $\mathrm{fp}_e$ | $1-\mathrm{fn}_e$ |
| Absent | $1-\mathrm{fp}_e$ | $\mathrm{fn}_e$ |

If a fixed $0<\eta\le1/2$ satisfies
$\eta\le\mathrm{fp}_e,\mathrm{fn}_e\le1-\eta$, then every report obeys

$$
\frac{\eta}{1-\eta}
\le\frac{q_1(e;y)}{q_0(e;y)}
\le\frac{1-\eta}{\eta}.
$$

In the binary symmetric channel with fixed error probability $q\in(0,1)$,
take $\eta=\min(q,1-q)$. For example, error probability $1/10$ gives likelihood
ratios $1/9$ and $9$. These substitutions are elementary consequences of the
channel definition; the Lean interface accepts the resulting likelihood-ratio
bounds directly.

For the complete family of binary reports, summing the likelihood over all
reports gives one for each fixed cycle: the finite sum factors into a product
of the per-edge probability sums. Hence $\sum_y M_p(y)=Z_p(w)$. This identifies
the separately normalized report masses with the report laws conditioned on
parity. The general formal finite-mass theorem does not require this channel
normalization identity as a premise and does not encode a particular channel
alphabet.

## Comparing the two report laws

The finite lemma in
[FiniteParityObservation.lean](FiniteParityObservation.lean) states that if
$a_x,b_x\ge0$, the pooled total is positive, $0\le\delta<1$, and

$$
|a_x-b_x|\le\delta(a_x+b_x)\quad\text{for every }x,
$$

then both class totals $A=\sum_xa_x$ and $B=\sum_xb_x$ are positive and

$$
\operatorname{TV}(a/A,b/B)
=\frac12\sum_x\left|\frac{a_x}{A}-\frac{b_x}{B}\right|
\le\delta.
$$

Zero-mass atoms are allowed. The proof treats $\delta=0$ separately and never
divides by an individual atom's mass. The constant one is sharp for this
general conversion: two atoms with
$a=((1+\delta)/2,(1-\delta)/2)$ and $b$ in reversed order attain equality.
This does not assert optimality of the cylinder's contraction rate.

The physical finite-report application in `NoisyParityObservation.lean` applies
this lemma with $a_y=M_0(y)$ and $b_y=M_1(y)$. It derives positive class totals
from positive pooled report mass when $L-2\ge N$, and proves TV at most
$\delta_L$. The finite report alphabet is chosen after $N$ and $\rho$.

For a complete normalized observation channel, the best classification success
with equally likely parity classes is $(1+\operatorname{TV})/2$, so it is at most
$(1+\delta_L)/2$. Under the original pooled cycle prior, the pointwise posterior
bound gives the same success upper bound directly. The pointwise posterior
formula above uses that pooled prior; assigning equal prior probabilities to
the two classes introduces their separate partition-function normalizers.

## Scope and interpretation

The geometric rate is a fixed-circumference statement. The proofs do not
evaluate or optimize its numerical constants. In particular, a very small
fixed error probability can require a very long cylinder before the estimate
is informative.

A common noise bound is essential to the stated uniform conclusion. If
$q_L=|E(G_L)|^{-2}$, the probability of any flipped edge is at most
$|E(G_L)|q_L\to0$; the exact report then reveals parity with probability tending
to one. Correlations also matter: a noise distribution supported on errors
with even meridian parity can preserve the true parity despite noisy individual
edges. Such channels do not have the independent likelihood product used here.

The theorem covers a common edge-product prior with the stated bounds.
Additional prior correlations require their own representation and estimates.
The TV statement concerns report distributions; the full cycle distributions
conditioned on opposite parities have disjoint supports.

## Relation to earlier methods

Uniform contraction of positive transfer kernels and conditional forgetting
are established methods; see Douc, Moulines, and Ritov,
[Theorem 2 and Remark 1](https://arxiv.org/pdf/0712.0285). Related exponential
indistinguishability of topological sectors occurs in the triangular-lattice
dimer model of Ioselevich, Ivanov, and Feigelman,
[Section III](https://arxiv.org/pdf/cond-mat/0206451). That model and its
observables differ from the Hamiltonian selections used here.

The contribution of these modules is the exact connection between actual
physical selection likelihoods, the existing uniform weighted theorem, and
finite normalized observation masses. No new general contraction mechanism
or literature-wide priority is claimed.

## Exact exterior observations

Write $L=n+2$ with $n\ge1$, and choose one free interval of local slots
$[a,b)$ with $0\le a\le b\le n$. Here $V_c$ denotes the vertical edges in
column $c$, while $H_i,D_i$ cross from column $i$ to column $i+1$. Each symbol
includes all $m$ row positions. The physical ownership is:

| Factor | Owned physical edges | Observation rule |
|---|---|---|
| Initial | $V_0$ | Observe selected and absent edges |
| Local $i$, $0\le i<n$ | $H_i,D_i,V_{i+1}$ | Ignore these edges if $a\le i<b$; observe them otherwise |
| Terminal | $H_n,D_n,V_{n+1}$ | Observe selected and absent edges |

Thus the free edges include the vertical columns $a+1,\ldots,b$, not the
initial vertical column. Every other actual edge has its selected or absent
status recorded. [ExteriorGeometry.lean](ExteriorGeometry.lean) defines this
event on the original physical edge sets.

### One code per observation

A total geometry $\sigma$ assigns Boolean values to every physical edge,
including the ignored free edges. Different values at those free positions
describe the same exterior observation. The type `CanonicalExteriorCode`
removes this redundancy by setting all free flags to false. These false
values are placeholders; the agreement predicate still ignores the free
edges, so they impose no absence constraint on a cycle.

[CanonicalExteriorObservation.lean](CanonicalExteriorObservation.lean) proves
that each finite edge set determines exactly one canonical code. All codes
are included, even those no Hamiltonian selection realizes. Such impossible
observations have zero mass. If $\mathcal O_{a,b}$ is the canonical code set
and

$$
Z_p^\sigma(w;a,b)=
\sum_{C:\,p(C)=p}W_w(C)\,
\mathbf 1\{C\text{ agrees with }\sigma\text{ on the exterior}\},
$$

the exact partition identity is

$$
\sum_{\sigma\in\mathcal O_{a,b}}Z_p^\sigma(w;a,b)=Z_p(w).
$$

The canonical partition identities themselves hold for every $n,a,b$ and
arbitrary finite edge sets; the interval restrictions above are needed for
the contraction application.

### Uniform exterior estimate and TV

The theorem `TriangularCylinder.Transfer.exists_exteriorParityCount_totalVariation_bound`
in [ExteriorParityObservation.lean](ExteriorParityObservation.lean) proves
the normalized bound below and positivity of both original class totals.

Fix $m\ge3$, $\epsilon>0$, and a finite upper bound $M$. Impose the global
actual-edge bounds $\epsilon\le w_e\le M$, with the same field for both
parity classes. There are $N\ge2$ and $0\le\rho<1$, chosen before $n$, the
interval, the exterior prescription, and $w$, such that

$$
\left|Z_0^\sigma(w;a,b)-Z_1^\sigma(w;a,b)\right|
\le\delta_{a,b}\left(Z_0^\sigma(w;a,b)+Z_1^\sigma(w;a,b)\right),
\qquad
\delta_{a,b}=\rho^{\lfloor(b-a)/N\rfloor}.
$$

This is an unnormalized inequality for every exterior prescription,
including impossible ones. Its physical transfer formulation is
[ExteriorCountImbalance.lean](ExteriorCountImbalance.lean). An empty free
interval gives the trivial coefficient one.

If $Z_0(w)+Z_1(w)>0$ and $N\le b-a$, the partition identity and sharp finite-TV
lemma give $Z_0(w)>0$, $Z_1(w)>0$, and

$$
\frac12\sum_{\sigma\in\mathcal O_{a,b}}
\left|\frac{Z_0^\sigma(w;a,b)}{Z_0(w)}
      -\frac{Z_1^\sigma(w;a,b)}{Z_1(w)}\right|
\le\delta_{a,b}.
$$

These are the exterior observation laws under the physical weighted cycle
measure conditioned on the two parities. Their denominators are the original
`weightedParityCount` values, justified by the exact canonical partition.
Zero-mass observations need not be removed. The endpoint concerns one
contiguous free interval at fixed circumference under global activity bounds;
it does not combine separated free intervals or extend the observation
theorem to other graph or support families.
