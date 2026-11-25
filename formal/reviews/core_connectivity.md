# CoreConnectivity independent source/API review

**Result: PASS. No blocker found.**

Target: `CoreConnectivity.lean`, 8,082 bytes, SHA256 `a0be084d04c8fc6257600cd80a1fd1be1227979f8594685ce88751be299edd17`. The digest was unchanged before and after review. All four direct-dependency source pins match the existing author receipt.

Reviewer: `/root/formal_matrix_contraction`. Target author: `/root/direct_splice_formalization`. I read the complete target source and the complete `StateEndVertical` source, checked the frozen CoreState/Occurs definitions, and used the immediately preceding complete reviews of SpliceLeftState, CommonReturns, StateInterval and the relevant right-state/tail parity interfaces. I authored AuxiliaryParity and some earlier dependencies, so this is an independent review of the composition, not of every transitive dependency. No source/configuration edits, compiler invocation, replay, optional tests, or compiled-object verification were performed. The existing receipt was read as author-supplied evidence, not reproduced.

## Main statement and actual witnesses

`Transfer.core_path_nonempty hm σ τ` assumes only m>=3 and two values of the existing CoreState subtype. It concludes an inhabited finite LocalLabel path from σ to τ. Unpacking each subtype supplies an actual occurrence at a nonterminal cut of an actual ambient Hamiltonian cycle, plus nonfullness of its outgoing H/D masks. No abstract path, realization, connectedness, primitivity, or same-cycle occurrence premise is added.

The original witness widths are j1+1+k1 and j2+1+k2 with k1,k2>=1. They may be exactly two. `StateEndVertical.exists_selected_end_edges_of_nonfull_stateAt` handles that case explicitly: j=0,k=1, and absence of an end vertical would force both masks full. For widths at least three it derives the required end edges from the selected cycle's actual degree/connectivity. Thus no hidden minimum width three is imposed on the original occurrence witnesses.

## Two actual splices, with one final cycle

1. A connector U selects the prescribed gap at each end and has total typeParity equal to typeParity(C1). The actual first splice produces M, its exact selected graph identity, total parity addition, and preservation of C1's old left state. Hence typeParity(M)=typeParity(C1)+typeParity(C1)=0 in ZMod2. The prescribed outer right edge of U survives in M: the helper compares last column u-1 with the deleted first column 0, using u>=2. This does not require distinct row gaps or nonwrap gaps.
2. The actual second splice uses that retained edge of M and the actual selected left edge of C2. Its returned J is used throughout both endpoint proofs. The source equality composes left-state preservation for J/M, left-state preservation for M/C1, and the original σ occurrence equality. The target equality uses the exact graph identity of this same J and the zero-splice right-state theorem. Connectedness of the inserted cut-open M graph is derived by deleting its actual selected Hamiltonian-cycle edge; it is not assumed. Since M has total parity zero, typeParity(J)=typeParity(C2), giving the required zero increment.

There is no substitution of a second existential J for one endpoint. The final invocation of `path_between_stateAt` passes that same J, its actual Hamiltonicity proof, and both established endpoint equalities.

## Source cutoff, coordinates, and boundary cases

The source endpoint uses the frozen left-state theorem whose assigned parity includes V and outgoing D with source column <=j1. Deleted V edges and seams lie strictly beyond the old source cut; in the second splice the remaining left width is k1+u>=1. The target endpoint uses the frozen right-state argument: unchanged strict-tail V/D sums have source column greater than j2, complementing the same <=j2 assigned prefix. Outgoing D at the cut is included, including when j1 or j2 is zero.

The two width wrappers only reassociate widths and preserve row and numeric column values. `stateAt_left_eq_of_splice_width` substitutes an equality of widths and then applies the exact frozen theorem; no geometric shift of the source cut occurs. The target cut is shifted by the actual left-block width (j1+1+k1)+u.

## Exact interval and path direction

The final source cut is j1. The target cut is ((j1+1+k1)+u)+j2. Their difference is exactly

    (((j1+1+k1)+u)+j2)-j1 = 1+k1+u+j2.

It is at least four, since k1>=1 and u>=2; there is no subtraction truncation or reversed path. The final width is ((j1+1+k1)+u)+(j2+1+k2), and k2>=1 keeps the target nonterminal. The source is also nonterminal with remaining width (k1+u)+(j2+1+k2). The joined width is at least six, so StateInterval's width>=3/core-membership requirement is derived even when both originals have width two. Every local label is obtained from the consecutive cut sequence of the same final J.

## Frozen direct dependency pins

| Dependency | SHA256 |
|---|---|
| CommonReturns | e7071f8e42b4b3dd9668c1ceb82fa9055706ef940bab0fcc31f23d931afb6313 |
| StateEndVertical | ae3a2af383b5a755d61feeac4c69483d85a514c1017248d35d05526c04455d32 |
| AuxiliaryParity | a04ff35c5df77e473b6bbbede3083fc956a2eec026d02298bfe9866009012688 |
| StateInterval | ac1b574fadd028a149e8dbed3244c5c196b505c89e7d11d9e8f75031811bcbb4 |

The existing author receipt is `verification/core_connectivity_receipt.json`; its reported strict compilation/axiom audits are separate from this source review. The reviewed module proves all-pairs path existence for the actual core label support. It does not itself prove parity-flip label equivalences or the final count ratio theorem.
