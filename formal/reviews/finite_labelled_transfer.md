# Statement-fidelity audit: finite labelled transfer and accepted-count ratio

**Verdict: scoped pass; no blocker or necessary correction found.**

Reviewer: `/root/external_math_validation_route`, 2026-11-25. I authored neither reviewed module nor the imported matrix-contraction layer. I read both complete sources and the relevant pinned Mathlib definitions, and reused my previous full algebra-layer audit after verifying its four source pins remain unchanged. This was read-only: no module edits, builds, or finite tests.

## Exact pins and evidence

Prototype root: `/workspace/scratch/4a160f238522/cylinder_formalization_20261125/`.

| Source | SHA-256 |
|---|---|
| `FiniteTransfer.lean` | `c0944775990d54f418c31570dea12c852fc7f9d1c011642f98f4fd41392310a1` |
| `AcceptedRatio.lean` | `c139b7eff4dffb670d01c69f36be757875204b71db8ac3d91f777fff657e5238` |

Reused review: `/workspace/scratch/4a160f238522/ordered_matrix_statement_fidelity_audit_20261125.md`. Its reviewed `MatrixContraction/Basic`, `Limits`, `PositiveBlocks`, and `OrderedApplication` hashes still match; in particular `OrderedApplication.lean` remains `9be2e0512511587db680ff88ea49182b6f2ab1b2a3023b2ff10a4977f32c132f`.

The pinned environment is Lean 4.19.0, commit `6caaee842e94`, and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The Mathlib checkout has no tracked changes. Existing receipts `verification/finite_transfer/verification.json` and `verification/accepted_ratio/verification.json` match the actual source and olean hashes, including audit modules and recorded local dependencies. They report successful warnings-as-errors compilation and respectively nine and four audited theorems, using only `propext`, `Classical.choice`, and `Quot.sound`. These are inspected existing results, not a new replay.

## Actual counted types and zero-length behavior

`LabelledPath E n i j` is recursively defined from dependent choices, independently of matrices:

- At zero steps it is `ULift (PLift (i = j))`.
- At `n+1` steps it is `Σ k, E i k × LabelledPath E n k j`.

Thus each step records its next state and its particular local label. Parallel labels are counted separately, loops are permitted, and states may recur. This is an exact-length labelled transfer walk, not a simple-graph path predicate. Finite state and label types give finite path types by induction.

At zero steps, equality-proof irrelevance makes the lifted type a singleton when `i=j`; it is empty otherwise. There is no multiplicity from equality proofs, and no transition label is selected. The cardinality is the Kronecker delta, agreeing with the matrix identity.

`Accepted E I F n` is exactly

`Σ i, I i × Σ j, LabelledPath E n i j × F j`.

An accepted object retains its initial label, ordered local labels, and terminal label. Consequently its zero-step cardinality is `Σ i, card(I i) * card(F i)`: initial and terminal labels remain present and must occupy the same state. The definitions themselves do not require nonempty states or labels; the later ratio theorem supplies explicit inhabitation assumptions.

No statement identifies these objects with Hamiltonian cycles, quotients cyclic roots or traversal directions, or assumes that such overcount has already disappeared. The finite theorem counts exactly the dependent type it defines. Any multiplicity introduced by a later cylinder encoding must be addressed by a genuine accepted-object/selected-edge-set equivalence; this obligation is not discharged here.

## Cardinalities, ordering, and real casts

`transitionMatrix E i j = card(E i j)` is a natural-number multiplicity matrix. The successor cardinality proof uses the actual sigma/product cardinality lemmas, giving

`card(Path(n+1,i,j)) = Σ k, card(E i k) * card(Path(n,k,j))`.

The first label therefore precedes the shorter suffix. The proof uses `pow_succ'`, namely `T^(n+1) = T * T^n`, and standard `Matrix.mul_apply`; it does not transpose the direction. The accepted-count formula is `initialVector · (T^n * terminalVector)`, with the initial vector on the left and the terminal vector a column vector.

`realTransitionMatrix` is the entrywise image under `Nat.castRingHom ℝ`. The power identity is proved using the ring-hom matrix multiplication identity and the identity matrix at exponent zero. Real path and accepted counts are exact casts of the natural cardinality theorems. Both numerator and denominator of the final ratio are individually cast to `ℝ` before division; there is no natural-number division, approximation, or changed multiplicity.

I checked the pinned sigma/product-cardinality and lifted-proposition instances, `Fintype.card_pos_iff`, and the actual matrix `dotProduct`, `mulVec`, and `map_mul` definitions/statements used in these bridges.

## Positivity and symmetry are derived at the advertised level

`realTransitionMatrix_pow_pos_iff` proves, for every exponent including zero, that a strictly positive power entry is equivalent to an inhabited `LabelledPath` type. It follows from the exact real cardinality and `card_pos_iff`, not from an independently assumed graph interpretation.

The ratio theorem explicitly requires a path between every ordered state pair and returns of lengths 2 and 3 at the **same** displayed `base`. The base also witnesses nonempty state type. Using the unchanged `eventual_positive_powers` theorem, these hypotheses derive one threshold beyond which every power entry is strictly positive. No primitive exponent is an input.

Given an initial label and a terminal label, positive power entries produce an actual accepted tuple. Thus nonempty total initial and terminal types suffice for eventual positive counts; pointwise positive boundary vectors are not required.

The supplied equivalences have the correct directions:

- `edgeEquiv i j : E (u i) (u j) ≃ E i j` yields simultaneous-index invariance `T(u i,u j)=T(i,j)`.
- `terminalEquiv i : F₁ i ≃ F₀(u i)` yields the second terminal vector `g ∘ u`.

The state permutation is explicitly involutive. An inhabitant of some `F₀ j` produces an inhabitant of `F₁(u j)` using `u(u j)=j`; nonemptiness of the second terminal family is therefore derived. No symmetry of the initial family is required. The theorem uses these equivalences through cardinalities: it does not assert a coherent involution of individual local labels or an exact finite-length bijection between the two accepted families.

## Eventual denominators and removal of the finite shift

The final conclusion is eventual strict positivity of the real `F₁` accepted count, together with `card(Accepted F₀ n) / card(Accepted F₁ n) → 1`. Both sector counts are proved positive for all `n ≥ N`; early counts may vanish.

To apply the existing algebra theorem, the proof supplies `List.replicate (n+N) T`. Its product is exactly `T^(n+N)`. Each positive matrix entry is at least 1 because it is a cast natural cardinality. The common upper bound `b = 1 + Σ entries(T)` is finite and at least 1; nonnegativity bounds every entry by it. Hence the algebra theorem's lower-support, upper-bound, and symmetry hypotheses are all proved.

Crucially, the algebra theorem requires a strictly positive total at every index. The new proof satisfies that premise on the shifted family using the already-derived positivity of both accepted counts at `n+N`; it does not silently replace everywhere positivity by eventual positivity. The lengths `n+N` tend to infinity.

Finally, the pinned `tendsto_add_atTop_iff_nat N` states exactly that convergence of `f(n+N)` is equivalent to convergence of `f(n)` on natural-number `atTop`. Its forward direction removes the finite shift. The separate eventual-denominator conclusion ensures the ordinary quotient is well-defined throughout a tail, independently of Lean's totalized division at any earlier zero denominator.

## Remaining application boundary

This is a homogeneous finite labelled-transfer ratio theorem. A cylinder application still must construct the actual finite state and label families, prove the required path connectivity/common returns and supplied equivalences, and establish the exact accepted-object equivalence with the intended undirected selected Hamiltonian edge sets and parity sectors, including the length convention. Neither these files nor this audit establish that correspondence, an annular topology theorem, or the cylinder asymptotic theorem.
