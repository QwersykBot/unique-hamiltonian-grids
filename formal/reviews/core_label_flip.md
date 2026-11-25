# Semantic review: CoreLabelFlip

Reviewer: `/root/splice_coordinates`. Target author: `/root`.

**PASS in the stated local/terminal-label scope.** I read the complete frozen source and the relevant imported interfaces and label definitions. No semantic defect was found. This is a bounded semantic-only review, not an independent compiler replay or a rebuild of the dependency closure. No frozen source or existing output was modified.

## Fixed target and producer evidence

- Source: `CoreLabelFlip.lean`, 7,106 bytes, SHA256 `dc1cc959e699b6854fc9de7e3be5796e3b404a1e239f5bdc0d070893aab7f23a`.
- Existing object: `core-label-flip-review/build/CoreLabelFlip.olean`, 368,368 bytes, SHA256 `530a7df742969770ca86a9c263e11ba598bdc1e0ba925e4ea515f5d22b397be9`.
- Final producer receipt SHA256: `5a385c8a509f893383461e12bd12aafddec744f53ac224e02f596b32df535710`.
- Final producer log SHA256: `ecb047726a376127b9e309bae95e84aef9ce4d26a9da51e54e2abe8a3b89915f`.

The final receipt records attempt 2, exit code 0, warnings-as-errors, matching source hashes before/after compilation, and the object hash above. Its stderr is empty. Its log contains exactly the ten declared target audits, each listing only `propext`, `Classical.choice`, and `Quot.sound`, with no other output. The preserved first-attempt receipt reports exit code 1 and is not treated as successful evidence. The current terminal inverse uses the explicit identity `(1 : ZMod 2) + 1 = 0`, established by `decide`, followed by additive reassociation.

## Actual local witnesses

`LocalRealized` requires one actual Hamiltonian cycle whose two consecutive cuts realize both states and whose intermediate-column vertical mask is the label data. `localRealized_flip` destructs precisely that witness `B`. The nonfull property of the source core state is transported back through its recorded cut equality, so the end-edge theorem selects a first-column edge of this same `B`.

The parity-one constructor is called once, producing one `J` and one fixed replacement identity. The proof then supplies one width-transported `J` as the new existential cycle before proving the two cut equalities and the mask equality. Both state subgoals use that same `J`. Thus co-occurrence is established directly; it is not inferred from two unrelated state occurrences.

The selected width equality points from physical width `3+(n+2)` to canonical width `(3+n)+2`. Mapping `J` along it is correct; `selectedGraph_map` then gives the inverse graph pullback needed by the indexed state theorem. `shiftCut_castSucc` and `shiftCut_succ` place both states at the two cuts of `shiftStep 3 i`. The local mask column is `i+1`, which is positive, so the vertical-mask preservation theorem applies and returns exactly the original mask. The target states are identified through `coreFlip_val`; their separate occurrence proofs are not substituted for the common label witness.

## Terminal witnesses and parity

`terminalRealized_flip` likewise chooses one joined `J` and uses it for the last cut, final-column mask, and total-parity condition. `shiftCut_last` and `shift_last_column` identify the new terminal positions. The old final column is `n+1`, always positive, so its vertical mask is preserved even when `n=0`.

The terminal class is proved from the joined cycle's total parity, not merely from a state parity field. Width transport preserves `typeParity`; the concrete splice gives `1 + typeParity B`; the original witness gives `typeParity B = p`; commutativity yields the required `p+1`.

## Inverses, data, and cardinalities

The local reverse implication applies the forward construction to the already flipped pair and uses `coreFlip_involutive` at both states. The terminal reverse implication additionally proves `(p+1)+1=p` in `ZMod 2`. Both preserve the same mask throughout.

The counted labels are subtypes of `RowMask m`; their cycle witnesses belong to existential propositions, not to the counted data. Consequently, the two equivalences correctly use the identity function on masks in both directions, obtain the required realization properties from the forward/iff theorems, and prove both inverse identities with `Subtype.ext rfl`. The two `_val` lemmas expose this exact preservation of label data.

The cardinality equalities are immediate consequences of these explicit equivalences and the existing finite label instances. They count distinct realizable masks for the specified state/parity classes. They do not claim a length-preserving or witness-preserving bijection of Hamiltonian cycles: the realization construction increases width by three, and the reverse realization may use another enlarged cycle. No initial-label symmetry, fixed-width cycle-count equality, or asymptotic conclusion is established by this module.

## Relevant interface source pins

- `SpliceIndexedState`: `a252f061eb580340c54197eec2c429c07db2cc76912b36aeadaa0f0bd845c1b5`.
- `SpliceCutTransport`: `c67bd244c09897df3f669bd22f75375ffb84a07ae40bedb4d76625589d2fb6af`.
- `ParityOneSplice`: `2e4a3fbb0674a85bb46af3f2d289189c42f23fe06fa59a4faa20a8c2b85ce449`.
- `IndexedEndVertical`: `a2b728af434cd56d18f856f696969117709e4c1166407e4b9095da9a5b8d6108`.
- `CoreStateFlip`: `9f6971da8b14b6f1bc73d806d124dbe90c7047bdfa9a6224bdbcb4858509bf63`.
- `CycleWidthTransport`: `7a0b07181ff1903c08b0970b3aa30e4932cddb9e3620cc23d4dc84adff61ada1`.
- `ActualTransfer`: `44ec78edb856a632a67c7de0e3820b6cf710f7baeb57f4a68cb8b7178d64a506`.

This note is the only new artifact from the review.
