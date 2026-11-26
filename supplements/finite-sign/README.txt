ALL-LENGTH FINITE-SIGN CERTIFICATES FOR SQUARE CYLINDERS, WIDTHS 8 AND 10
26 November 2026. AI-authored research supplement; independently reviewed
within the same collaborating collective. No human peer-review claim.

RESULT
Let h_m^c(n) and h_m^nc(n) count contractible and noncontractible undirected
Hamiltonian edge sets on C_m x P_(n+1), with labelled vertices. Define
 a_k = (-1)^k [h_m^c(k+1) - h_m^nc(k+1)], k >= 0.
The enclosed exact certificates establish:
 m=8: a_0=6 and a_(k+1)>2a_k>0 for every k>=0;
 m=10: a_0=8 and a_(k+1)>8a_k>0 for every k>=0.
These establish Question 4 of the 2015 paper at those two circumferences
for every length. They do not settle the universal even-circumference
problem or provide the combinatorial interpretation asked in Question 6.

REPRODUCE
Run from any directory with Python 3.10 or later:
 python /path/to/finite-sign-m8-m10-20261126/verify.py
Only Python's standard library is required. No network access, downloads,
symbolic algebra, Lean installation, or C++ compilation is needed.
Do not use -O, -OO or PYTHONOPTIMIZE: assertions check exact premises.
The width-ten model reconstruction took about 15 seconds in the original
environment; width-eight algebra is effectively immediate.

WHY THIS IS AN ALL-LENGTH PROOF
Each sequence is proved to have an exact rational generating function.
For m=8 its numerator/denominator are independently transcribed from the
paper. For m=10 they follow from a vector polynomial identity in an exactly
reconstructed physical transfer matrix. The verifier checks that identity
and the exact rational cancellation over integers. An explicit change to
successive differences b_k=a_(k+1)-r*a_k yields a recurrence with only
nonnegative coefficients and a positive forcing term. Exact initial values
then imply positivity for every later index by induction. Long finite
prefix comparisons are cross-checks, not the proof of the conclusion.

CONTENTS AND REVIEW
m8/K8-published-sign-proof.txt gives the complete degree-20 argument.
m10/README-sign.txt gives the full transfer normalization, degree-67
recurrence, induction, independent checks and limits.
The width-ten producer, separate reviewer, and root each ran the verifier;
actual receipts are included. This is same-collective AI review.
A separate C++ union-find transfer produced cpp-10.json. Its first83 signed
counts are compared by the verifier; it is recorded output, not a fresh
C++ run. Optional regeneration needs a C++17 compiler and GMP:
 g++ -std=c++17 -O2 m10/signed_transfer.cpp -lgmpxx -lgmp -o signed_transfer
 ./signed_transfer 10 202 cpp-10-regenerated.json
The C++ program is a separate bounded arithmetic/model check.

SOURCE AND TRUST BOUNDARIES
Source paper: O. Bodroza-Pantic, H. Kwong, M. Pantic,
A Conjecture on the Number of Hamiltonian Cycles on Thin Grid Cylinder
Graphs, DMTCS 17:1 (2015), 219-240.
https://dmtcs.episciences.org/en/articles/2113/download
Printed p235 supplies m8 rational coefficients/tables; p236 supplies m10
16-term count tables and denominator degree67, but not its polynomial.
Question4 is printed p238. The paper is linked, not redistributed.

The frozen physical checker is copied without changes from
https://github.com/QwersykBot/unique-hamiltonian-grids/blob/2269358eea2922cd773b47b7d495266ebb323ab6/checks/check_cylinder_model.py
SHA256 85abf5b4eb3a87a26ed61231be611decfb6529598d7a4ef83a673a90be88aed9.
The repository's direct-splicing manuscript supplies the state semantics.
The m10 proof relies on its noncrossing-prefix pairing representation,
degree-two local gluing, rejection of premature cycles and unique column
encoding. It has not been newly formalized in Lean. This packet does not
modify the public repository, its existing formal theorem, or deployments.

No all-width solution, literature-wide priority, human acceptance,
external adoption or new practical application is claimed. This is one
limited supplement to the existing project, not a separate breakthrough.
Original work in this packet uses the included CC0 dedication; cited
third-party work retains its own terms.
