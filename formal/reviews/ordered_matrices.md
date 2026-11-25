# Independent statement-fidelity audit: ordered matrix application

Date: 2026-11-25. Reviewer: `/root/external_math_validation_route`.

## Verdict and independence

**Scoped pass; no blocker or necessary correction found.** `OrderedApplication.lean` faithfully composes support-derived positive blocks, ordered-product contraction, and a scalar ratio limit. The original factor order is preserved; the residual suffix is treated correctly; the finite and limit statements have sufficient explicit positivity assumptions. Neither a positive block nor the limiting conclusion is assumed.

I authored none of `Basic.lean`, `Limits.lean`, `PositiveBlocks.lean`, or `OrderedApplication.lean`. I read their complete sources and the relevant pinned Mathlib definitions and theorem statements. This is independent source-level mathematical review of that algebra layer. I did not edit or rebuild these files. I did not self-audit my separately authored `EnumeratedWalk.lean`.

This result is a generic theorem about finite real matrices and endpoint vectors. It is not the concrete cylinder counting theorem.

## Exact pins

All modules are under `/workspace/scratch/4a160f238522/cylinder_formalization_20261125/MatrixContraction/`.

| File | SHA-256 |
| --- | --- |
| `OrderedApplication.lean` | `9be2e0512511587db680ff88ea49182b6f2ab1b2a3023b2ff10a4977f32c132f` |
| `Basic.lean` | `05840c6b226533535e9c5b710aaad4e7af8f289d292e39cb562f053cc946c80d` |
| `Limits.lean` | `8c14236bf79aed99d426fb62ea4de4145ff74c96ac9182927e248f74f86967a0` |
| `PositiveBlocks.lean` | `d5bde70fb3484824be3093f88ee3a955377424916f4e742d37caff82fe7bdbfc` |

The pinned environment is Lean 4.19.0, commit `6caaee842e94`, and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The local Mathlib checkout had no tracked changes. The imported source and compiled-object hashes matched `ordered_application_receipts/verification.json` when checked.

## Actual mathematical statement

The index type is finite and has a supplied state `v`, hence is nonempty. A fixed nonnegative reference matrix `T` satisfies:

- for every ordered pair `x,y`, some nonnegative integer power has `(T^k)(x,y)>0`;
- returns of lengths 2 and 3 are positive at the same supplied state `v`.

There is one fixed involutory permutation `u` and fixed real bounds `0<a≤b`. Every factor in every list is nonnegative, is at least `a` on the positive-entry support of `T`, is everywhere at most `b`, and satisfies `B(u i,u j)=B(i,j)`. Positive entries outside the reference support are allowed. Factors are not assumed to commute with one another, and `T` itself need not be invariant under `u`.

For an ordered list product `P`, put `Z₀=f·(Pg)` and `Z₁=f·(P(g∘u))`, with nonnegative `f,g`. The finite theorem derives fixed `N≥2` and `0≤ρ<1`, uniform over all such lists and boundary vectors, and proves

`|Z₀−Z₁| ≤ ρ^(floor(length/N)) (Z₀+Z₁)`.

The family theorem allows the entire factor list and both boundary vectors to vary with the external index. It assumes the list lengths tend to infinity and **`Z₀(n)+Z₁(n)>0` for every index**, and concludes `Z₀(n)/Z₁(n) → 1`.

## Product order and residual

The inspected upstream `List.prod` definition is `foldr (· * ·) 1`, so `[B₁,B₂,B₃].prod = B₁*(B₂*(B₃*1))`. Upstream `Matrix.mul`, `mulVec`, and `dotProduct` are the standard finite-sum operations; `mulVec` acts on column vectors. `Basic.act` uses the corresponding right fold and is proved equal to `blocks.prod *ᵥ z`.

`fullChunks` takes the first `N` factors and recurses on the remaining suffix. `fullChunks_flatten_append_drop` reconstructs the original list, and the product identity is proved for an arbitrary monoid, requiring no commutativity. With `k=floor(length/N)`, `fullChunks_spec` derives exact chunk length from `kN≤length`. The residual is the actual suffix after those `kN` factors and has length less than `N` when `N>0`.

Thus the original product is exactly `block₁ · … · block_k · R`. On a right boundary vector, `R` acts first. The residual product is proved nonnegative and invariant under `u` from its constituent factors. An empty residual gives the identity matrix, whose required properties are proved. A short or empty original list has zero complete blocks and receives the valid finite bound with exponent zero; no factor is reordered, discarded, or silently replaced.

## Positive blocks are derived

`eventual_positive_powers` chooses positive-power routes `x→v` and `v→y`. Positive returns of lengths 2 and 3 at that same `v` generate every return length at least 2. A finite sum of the chosen route lengths plus 2 supplies one exponent threshold that works for every ordered pair. Nonnegativity ensures concatenated positive summands cannot be canceled by other summands.

For variable factors, the proof sets `M=1+sum(T entries)`, `c=a/M`, and `S=cT`. Every factor dominates `S` entrywise: on the positive support this follows from `S≤a`, and off the support it follows from nonnegativity. Ordered multiplication therefore makes every length-`N` product dominate `S^N`. The strictly positive minimum of the finitely many entries of `S^N` supplies `lower>0`. The supplied state `v` explicitly witnesses the nonempty index-pair set used in this minimum.

The constant matrix with all entries `b` supplies an upper comparison. The chosen `upper` is at least `lower` and at least the sum of that comparison matrix's `N`th-power entries. Hence every block entry lies between `lower` and `upper`, and `ρ=1−lower/upper` lies in `[0,1)`. I inspected the upstream nonempty finite infimum definition and its positivity and entry-bound lemmas. There is no assumed primitive exponent or assumed positive-block hypothesis.

The resulting constants are existential. This source does not establish a particular sharp exponent such as `N=2·card(ι)` or a cylinder-specific numerical contraction rate.

## Contraction and limit assumptions

`SymmetricUnder` means simultaneous index relabeling, not transpose symmetry. It preserves the odd subspace `z(u i)=−z(i)`. Since `u` is a permutation, every odd vector has coordinate sum zero, including when `u` has fixed points. Subtracting the all-ones matrix times `lower` therefore leaves a positive block's action on odd vectors unchanged. The remainder matrix is nonnegative and bounded above by `ρ` times the original block, giving the pointwise contraction.

The difference `g−g∘u` is odd because `u` is involutive, and its absolute value is bounded by `g+g∘u`. The residual preserves oddness and the absolute-value comparison. Ordered induction through the complete blocks and a nonnegative left dot product yield the finite imbalance estimate. No invariant or strictly positive left boundary is needed.

For the limit, `N≥2` implies a fixed nonzero divisor, so natural-number division preserves divergence of list lengths. The upstream geometric-decay theorem applies to every `0≤ρ<1`, including `ρ=0`. Consequently the relative imbalance tends to zero.

The positive-total assumption is essential and remains explicit: nonnegative vectors alone could both vanish. It is required at every index in this theorem, which is stronger than an eventual-positivity formulation. It is not inferred from support connectivity or hidden in a division step.

The proof normalizes both endpoints by their positive total, shows each tends to `1/2`, and applies the ordinary quotient limit theorem at a nonzero limiting denominator. Early values of `Z₁` are not required to be positive. This does not compromise the limit: once the imbalance factor `ε` is below one, `2Z₁ ≥ (1−ε)(Z₀+Z₁)>0`. Thus the conventional ratio is well-defined eventually, independently of Lean's totalized division at any earlier zero denominator. I checked the actual upstream `Filter.Tendsto`, `atTop`, division-limit, geometric-decay, natural-division divergence, and common-denominator cancellation statements used here.

## Application boundary and verification evidence

A concrete cylinder application must still construct its finite actual-state matrices and endpoint vectors and prove the reference connectivity, common-state returns, uniform entry bounds, simultaneous involution symmetry, terminal exchange, positive totals, and exact correspondence between endpoint values and the desired cycle counts. None of those cylinder identifications is supplied by this generic algebra theorem. No Perron asymptotic expansion, annular topology, or priority claim follows merely from this audit.

The inspected existing receipt records successful warnings-as-errors compilation of `OrderedApplication.lean` and its audit module. The main finite and limit theorems have only `[propext, Classical.choice, Quot.sound]` dependencies. All four reviewed algebra sources lack `sorry`, `admit`, custom axiom declarations, `unsafe`, and `native_decide`. These are inspected existing compilation results; this reviewer did not perform a redundant rebuild.
