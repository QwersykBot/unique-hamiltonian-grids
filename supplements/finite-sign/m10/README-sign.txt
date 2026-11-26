EXACT ALL-LENGTH FINITE-SIGN CERTIFICATE AT CIRCUMFERENCE 10
26 November 2026 — computational research lane, AI-authored

Claim and indexing
------------------
Let h_c(n), h_nc(n) be the contractible/noncontractible Hamiltonian-cycle
counts of the square cylinder C_10 x P_(n+1), in the 2015 paper's convention.
Put a_k = (-1)^k [h_c(k+1) - h_nc(k+1)], for k >= 0.
The enclosed exact certificate gives

    a_0 = 8,    a_(k+1) > 8 a_k > 0  for every k >= 0.

In particular it proves the strict alternating-sign assertion of Question 4
for circumference 10 and every length, not merely the computed initial
prefix. It does not prove Question 4 for every even circumference, establish
literature-wide priority, or supply the combinatorial interpretation asked
for in Question 6.

Source transfer and endpoint convention
--------------------------------------
The public repository is QwersykBot/unique-hamiltonian-grids at commit
2269358eea2922cd773b47b7d495266ebb323ab6. Its frozen checker
checks/check_cylinder_model.py, SHA256
85abf5b4eb3a87a26ed61231be611decfb6529598d7a4ef83a673a90be88aed9,
constructs local transitions by gluing physical column vertices, the current
noncrossing prefix pairing, and outgoing leaves; it rejects premature
closed components. It retains states reachable from initial columns and
coaccessible to a single closing cycle. The published manuscript explains
the exact state enumeration and terminal sets.

The certificate verifier rebuilds that model at m=10: 2,234 actual states,
172 dihedral orbits. Parity complement J acts on these orbits, commutes with
the transfer, and exchanges the two terminal sets. Fixed orbits have zero
terminal difference. Choosing one representative from each nonfixed J-pair
gives the 82-dimensional odd block A and vectors u,v in the certificate:

    h_c(k+1) - h_nc(k+1) = u A^k v.

The signed block uses A_ij = T_(i,j) - T_(i,Jj), the initial row is
u_i = f_i - f_(Ji), and v_i = 1_(i in Lc) - 1_(i in Lnc).
All these quantities are integers. With B=-A, a_k = u B^k v.

All-length algebraic proof
--------------------------
The verifier first checks an exact degree-82 monic vector annihilation
q(B)v=0 by integer Horner evaluation. This is sufficient to give the scalar
recurrence q(E)a_k=0 for every k>=0: multiply the vector identity by u B^k.
The generating function is consequently the explicitly constructed degree
<82 numerator divided by sum_j q_j z^j. A separate integer polynomial
identity checks cancellation to the supplied proper fraction P(z)/D(z),
where deg P=66, deg D=67, D(0)=1. No root finding is used.

Let s=67 and d(x)=x^s D(1/x). Synthetic division by x-8 has the form

    d(x) = (x-8) Q(x) - gamma,
    Q(x) = x^(s-1) - beta_1 x^(s-2) - ... - beta_(s-1),

with every beta_j >= 0 and

    gamma = 19676990277789349175922546551608103560124231883434186232797184 > 0.

The exact signs of all 66 beta values are checked; the entire polynomial is
in the JSON certificate. Put b_k = a_(k+1) - 8 a_k. The recurrence becomes

    b_(k+s-1) = beta_1 b_(k+s-2) + ... + beta_(s-1) b_k + gamma a_k.

The verifier evaluates a_0=8 and all required initial b_0,...,b_65 directly
from u B^k v. Every initial b is strictly positive, with minimum 798.
Inductively the displayed recurrence gives the next b>0, while
    a_(k+1) = 8 a_k + b_k
keeps every a positive. This proves the claim at every length.

Independent checks and their limits
-----------------------------------
A separate C++/GMP program signed_transfer.cpp constructs reachable pairing
states using union-find on the physical row graph. It charges the selected
wrap vertical with sign -1 and computes total and signed counts together.
Its signed counts agree with the Python quotient for all 200 terms checked
at m=4,6,8,10. The certificate verifier also compares its first 83 terms at
m=10 when cpp-10.json is present. These finite comparisons validate code and
endpoint conventions; they are not the all-length proof.

A separate theory agent transcribed all 16 m=10 differences printed on
page 236 of the original 2015 paper and matched them to the independent
transfer output. The paper reports a degree-67 denominator, matching the
exactly reduced fraction here, but does not print that polynomial. Thus
there is no claim of a full coefficient-by-coefficient comparison with a
published m=10 rational function.

The theory lane independently obtained the same positive-cone construction
for m=8 directly from the paper's printed rational function, using r=2 and
a degree-20 recurrence. That source transcription and proof are separate.
The present m=10 model identity is not newly formalized in Lean, and the
certificate is not external human review. The integer recurrence proof is
fully replayed by the script; the physical counting correspondence rests on
the stated graph construction and published transfer semantics.

Reproduction
------------
From any directory, with Python 3.10+ and the public repository available:

    python verify_sign_certificate.py --repository /path/to/unique-hamiltonian-grids

The verifier uses only the standard library. It takes about 15 seconds in
the observed environment; no downloads, symbolic algebra, or external
services occur. Run without Python optimization because the checker's
original invariants and verifier guards are assertions. The optional C++
comparison uses the already recorded cpp-10.json if present; no compilation
is needed to check the algebraic certificate.

The generator used SymPy only to obtain an annihilator and cancel the
rational function. The verification does not trust those operations: it
rechecks the resulting vector and polynomial identities using integers.

Original source
---------------
O. Bodroza-Pantic, H. Kwong, M. Pantic,
A Conjecture on the Number of Hamiltonian Cycles on Thin Grid Cylinder
Graphs, DMTCS 17:1 (2015), 219-240.
https://dmtcs.episciences.org/en/articles/2113/download
Question 4 is on printed page 238; the m=10 table/order is on page 236.
