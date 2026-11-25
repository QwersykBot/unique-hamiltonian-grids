# TriangularCountImbalance: semantic review

Reviewer: `charge_sectors`, 2026-11-25 UTC. **PASS in the stated scope.** I read the entire source and checked the specialized matrix theorem, symmetry conventions, and finite count interface. No compiler or dependency replay was run.

Reviewed source: `../TriangularCountImbalance.lean`, 4,530 bytes, SHA256 `11f36283596d11a48deb40033cc79ad19d0b7fb01e7a4a83710565771a1338f1`.

## Findings

1. **Constants are uniform in width for each fixed circumference.** The matrix `T` is the actual cardinality matrix of `LocalLabel hm`; the bound `b = 1 + sum of all entries of T` and the chosen core involution/base depend on the fixed `m`. The proof obtains `N` and `rho` before introducing `L`, exactly matching the statement's quantifier order. These are existential fixed-circumference constants, with no explicit evaluated rate or uniformity across all circumferences claimed.

2. **The support bounds are valid.** Every entry is a nonnegative integer cast to a real. A positive entry is therefore at least one, satisfying the lower bound `a=1` on the reference support. Every factor is exactly `T`, so the imported support-lower-bound premise is met. Nonnegativity also bounds each entry by the sum of all entries, hence by `b`; `b≥1` supplies the required upper/lower compatibility.

3. **Both symmetry orientations are correct.** `SymmetricUnder u T` means `T (u s) (u t) = T s t`, which is precisely `localLabel_card_flip`. At terminal parity one, `terminalLabel_card_flip` states `card F₀(u s) = card F₁(s)` because `1+1=0`; taking its symmetry gives the required `F₁(s)=F₀(u s)`. No symmetry of the initial vector is needed.

4. **The counted classes and exponent agree.** The two scalar products are identified with the existing undirected selected-edge parity counts by `parityCount_eq_transfer_real`, used only for `n≥1`. With `L≥3`, setting `n=L-2` gives `n≥1` and `n+2=L`. The product of `n` copies of `T` is `T^n`, and the complete-block exponent is exactly natural-number division `(L-2)/N`, with no extra shift or subsequence restriction.

5. **There is no hidden positive-count premise.** The imported finite inequality assumes only nonnegative boundary vectors. It applies when either or both counts vanish. When fewer than `N` transfer steps are present, the exponent is zero and the bound reduces to the valid nonnegative-count estimate `|x-y|≤x+y`. The statement does not divide by a possibly zero total.

The result bounds the absolute difference by a geometrically shrinking fraction of the total count. When the total is positive, it is a normalized relative-imbalance bound. It is not an absolute-decay estimate, a spectral growth expansion, a numerical spectral gap, or a weighted-cycle enumeration theorem. No new state, count, or parity definition is used.

## Checked interfaces and evidence

The imported interface `uniform_finite_imbalance_of_support` was checked at `MatrixContraction/OrderedApplication.lean` SHA256 `9be2e0512511587db680ff88ea49182b6f2ab1b2a3023b2ff10a4977f32c132f`. The simultaneous-index symmetry definition is in `MatrixContraction/Basic.lean` at `05840c6b226533535e9c5b710aaad4e7af8f289d292e39cb562f053cc946c80d`.

The label-cardinality orientations were checked in `CoreLabelFlip.lean` at `dc1cc959e699b6854fc9de7e3be5796e3b404a1e239f5bdc0d070893aab7f23a`. The finite count identity is in `CountedTransferEquivalence.lean` at `2bbb4a14e5b394755d7a397849c218f93816dacf45c45042db39a368d440e7a7`. Their underlying connectivity, return, and contraction proofs were not reaudited here.

Producer object: 263,416 bytes, SHA256 `27f29ade1c95bc56d75fb6724bc4819f1832ea9dfaebae3a40e53f643af30949`. Producer receipt SHA256: `f3c9a785ea4774e7223cf0b2904acdbc8d133e4845c483fd5c41ead385d80eba`. Producer log SHA256: `334cb4e16b791f515a6b71a1578299fba9d16312ed464129e811a23b76da12f4`.

The exact single audit is `TriangularCylinder.Transfer.exists_parityCount_geometric_imbalance`, reporting only `propext`, `Classical.choice`, and `Quot.sound`. Source, object, receipt, and log pins match the frozen inputs. This is a semantic review of the specialization, not an independent compile. No blocker, source edit, or package was produced.
