# TriangularCountRatio independent source/API review

**Result: PASS. No blocker found.**

Target: `TriangularCountRatio.lean`, 3,014 bytes, SHA256 `86ab3d21d7cd4267176c0be24b18c95d14663f1314d888d952897d6e33cf8227`. The source remained unchanged. Its four direct import source pins were checked against the frozen handoffs.

Reviewer: `/root/formal_matrix_contraction`; target author: `/root`. I read the entire target, the complete frozen AcceptedRatio, CountedTransferEquivalence and CoreLabelFlip sources, and the exact coreFlip, count definitions and pinned Mathlib filter lemmas used. I used the preceding complete reviews of CoreConnectivity, CommonReturns and the actual boundary-choice witnesses. I authored AcceptedRatio and several lower-level dependencies; this is an independent review of the final composition, not a wholly independent review of the transitive mathematics. No proof/configuration edits, compiler invocation, replay, optional tests, or compiled-object validation were performed. The existing strict compiler/axiom receipt was read as author-supplied evidence and was not reproduced.

## Exact conclusion

For every fixed natural circumference m with hm:3<=m, `Transfer.triangular_parity_ratio_limit m hm` proves both:

1. Eventually over all natural total lengths L, the existing natural-number denominator `parityCount m L hm 1` is strictly positive.
2. The real ratio of the existing `parityCount ... 0` to `parityCount ... 1` tends to one as the full length L tends to infinity.

`parityCount` is the frozen filtered finite count of `CountedHamiltonian.Selection (graph m L hm)`: undirected selected Hamiltonian edge finsets on fixed vertex labels, with traversal/root witnesses only in Prop. Its parity is the existing selected-edge meridian sum. The final module introduces no replacement count, extra traversal multiplicity, or topology identification.

## Generic instantiation and equivalence directions

The finite state type is exactly `CoreState hm`, and the label families are exactly LocalLabel, InitialLabel, TerminalLabel 0 and TerminalLabel 1. The local classical DecidableEq instance supplies the existing finite counting machinery; it does not change state or label data.

`coreFlipEquiv hm` has underlying function `coreFlip hm`, and the supplied involutivity theorem is definitionally the required one. `localLabelFlipEquiv hm s t` runs from E(s,t) to E(u(s),u(t)), so taking `.symm` supplies precisely the generic hypothesis E(u(s),u(t)) equivalent to E(s,t). `terminalLabelFlipEquiv hm 1 s` runs from F1(s) to F(1+1)(u(s)); simplifying 1+1=0 gives precisely F1(s) equivalent to F0(u(s)). No reversed numerator or terminal function enters.

The generic accepted-ratio theorem has no initial-label symmetry hypothesis, and the final theorem supplies none. It uses only actual nonempty initial choices and zero-parity terminal choices, already provided by the concrete common witness. CoreConnectivity supplies all-pairs actual LocalLabel paths. Both the length-two and length-three returns use the same existing `commonCoreState m hm`. The generic theorem derives eventual positive denominators and the accepted count limit; positivity for every short length is not assumed.

CoreLabelFlip's complete source preserves the vertical-mask label data and obtains local co-occurrence in a single actual spliced witness. Its terminal equivalence flips the actual total cycle parity. This matches the finite counted-label types used by the exact count equivalence.

## Finite correspondence is used only in its valid range

The exact counted equivalence applies to width n+2 with n>=1. Both uses of `parityCount_eq_card_accepted` are under `eventually_ge_atTop 1`: one for denominator positivity and one for equality of the ratios. Therefore the final proof does not assert the width-two count correspondence or require a short-length accepted/count equality that was not proved.

For positivity, the generic result first gives positive real-cast accepted cardinality. After the valid count rewrite, `Nat.cast_pos.mp` yields the actual natural count's positivity at n+2. Thus the first conjunct is a Nat inequality on the original count, not merely a statement about an alternate scalar.

## Removing the shift in both conclusions

The positivity proof transports its event along `Filter.map (fun n : Nat => n+2) atTop` using `eventually_map`, then uses the pinned Mathlib equality `map_add_atTop_eq_nat 2` to identify that filter with atTop. It therefore proves eventual positivity for all sufficiently large L.

The ratio proof establishes eventual equality between accepted ratios and actual ratios at width n+2, with the accepted function on the left. `tendsto_congr'` is used in the matching direction to obtain the shifted actual limit. `tendsto_add_atTop_iff_nat 2` then removes the shift. This is convergence of the entire natural-length sequence, not merely an even/odd subsequence or an unremoved transfer exponent.

## Pins and scope limits

| Direct import | SHA256 |
|---|---|
| AcceptedRatio | c139b7eff4dffb670d01c69f36be757875204b71db8ac3d91f777fff657e5238 |
| CountedTransferEquivalence | 2bbb4a14e5b394755d7a397849c218f93816dacf45c45042db39a368d440e7a7 |
| CoreConnectivity | a0be084d04c8fc6257600cd80a1fd1be1227979f8594685ce88751be299edd17 |
| CoreLabelFlip | dc1cc959e699b6854fc9de7e3be5796e3b404a1e239f5bdc0d070893aab7f23a |

The reviewed Mathlib filter statements are from pinned commit c44e0c8ee63ca166450922a373c7409c5d26b00b: eventually_map, tendsto_congr', map_add_atTop_eq_nat and tendsto_add_atTop_iff_nat. CoreStateFlip uses pin 9f6971da8b14b6f1bc73d806d124dbe90c7047bdfa9a6224bdbcb4858509bf63. CountedHamiltonian uses pin 8a0e8cd07056a3b869758f5a0abe8001ad67ed15724f6cfdd017e6aafa0b9bd4.

The existing author receipt is verification/triangular_count_ratio/verification.json. The theorem is for fixed m>=3 and combinatorial meridian parity on the existing simple cylinder graph. It does not identify these classes with annular contractibility, settle circumference-two multigraph conventions, prove an absolute spectral expansion, or assert a uniform joint limit in m and L.

## Final revision: reciprocal orientation — focused diff review PASS

Final source SHA256: `f9b13d53a60ed9bf0953c4dec06be44c5392d83cfc9c5bb7a1340afa0bd216c3` (3,887 bytes). This section reviews the appended reciprocal proof against the preserved original snapshot at verification/triangular_count_ratio_review/original_source.lean, SHA256 `86ab3d21d7cd4267176c0be24b18c95d14663f1314d888d952897d6e33cf8227`. The exact diff adds only sixteen lines before the final namespace end; the original imports, definitions and complete main theorem remain unchanged. The preceding full-source review therefore applies to that unchanged body, and this section covers the addition. No compiler/replay or binary validation was performed for either scope.

`triangular_parity_ratio_limit_reciprocal m hm` proves eventual natural-number positivity of the existing class-zero count and convergence of the actual class-one/class-zero ratio to one. Its numerator/denominator order is exactly the reciprocal of the original result, matching the requested odd/even orientation without redefining the count.

The positivity proof is valid independently of the inverse limit step. Convergence of the original ratio to 1 implies that ratio is eventually positive, by the open positive neighborhood of 1. Intersecting with the original eventual positive class-one denominator gives a positive class-zero real numerator through div_pos_iff_of_pos_right. Nat.cast_pos then gives strict positivity of the original Nat count. No assumption that either short-length count is positive is introduced.

The inverse limit uses the pinned Mathlib Filter.Tendsto.inv₀ theorem, whose only nonvanishing hypothesis is that the LIMIT is nonzero. Here that limit is 1. It does not require every ratio value or count to be nonzero. The pointwise inv_div identity reverses the quotient, and inv_one restores the limit 1, yielding precisely the desired full-length reciprocal ratio. No inverse-continuity assertion at zero occurs.

The final statement remains fixed-m>=3, actual undirected selection counts, and combinatorial meridian parity. No topology or circumference-two claim is added. Existing final author receipt verification/triangular_count_ratio/verification.json reports two exact standard-axiom audits and strict compilation; those are author evidence, not a new build by this reviewer.
