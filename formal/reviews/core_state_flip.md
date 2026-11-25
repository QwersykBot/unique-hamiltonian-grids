# Core-state flip and parity-one splice: semantic review

Reviewer: `charge_sectors`, 2026-11-25 UTC. **PASS in the stated scope.** I read both entire frozen sources and checked the relevant existing construction and state interfaces. No compiler was run for this review.

Reviewed sources:

- `CoreStateFlip.lean`, 5,770 bytes, SHA256 `9f6971da8b14b6f1bc73d806d124dbe90c7047bdfa9a6224bdbcb4858509bf63`.
- `ParityOneSplice.lean`, 2,359 bytes, SHA256 `2e4a3fbb0674a85bb46af3f2d289189c42f23fe06fa59a4faa20a8c2b85ce449`.

## Construction and state meaning

The aligned three-column auxiliary supplies a standard Hamiltonian cycle with type parity one and the requested selected right-end vertical. The selected-edge splice theorem joins it to the old cycle at the same row gap and returns one actual Hamiltonian cycle `J`, its total-parity sum, and its exact selected-edge set.

The gadget `GA` is the selected auxiliary graph with that selected right-end edge deleted. The frozen cycle-deletion theorem proves it connected. The old selected first-end edge is converted to graph adjacency using the genuine vertical-edge nonloop property. The exact splice selected-edge identity then gives the same `replacementGraph` used by the reachability and state-field lemmas. The factory's existential points and graph therefore come from one construction, with no independent choices for different conclusions.

`stateAt_flip_of_splice` assembles horizontal, diagonal, reachability, and parity equalities for the same graphs and splice. Its reachability component has both required premises: connected gadget and selected old edge. The parity component uses the two explicit trail hypotheses; the occurrence construction supplies them from the two Hamiltonian cycles. The global increment `1 + typeParity B` yields the raw flip's `oldParity + 1` through the existing assigned-parity theorem.

For occurrence closure, the nonfull actual state supplies a selected old first-end vertical through `StateEndVertical`, including the two-column case. The three-column auxiliary changes the cut from `j` to `3+j` and keeps the positive suffix width `k`. `StateWidthTransport.occurs_joined_state` supplies an actual occurrence of the joined state with precisely that cut. The four-field equality identifies it with the raw flipped state.

The `CoreState` proof preserves nonfullness because `RawBoundaryState.flip` changes only parity. Involution and absence of fixed points are inherited from the raw flip, and the equivalence uses that same involution in both directions. Neither module claims local-label preservation, terminal-label preservation, transfer-weight symmetry, or a counting bijection.

## Verification scope

The relevant interfaces checked were `exists_aligned_three_column_auxiliary`, `exists_splice_of_selected_edges`, `selected_cycle_delete_edge_connected`, `selected_splice_comap`, `stateAt_parity_add_of_splice`, `RawBoundaryState.flip` and its involution/nonfixed-point lemmas, and the actual `Occurs`/`CoreState` definitions. This composition review does not replace the separate proofs and reviews of those dependencies.

The producer output for `CoreStateFlip` is 222,768 bytes, SHA256 `fe33ab49e625d4c6f883e7930662a54e919e96a887ab2f684d3f9fa032146fbb`; its producer receipt SHA256 is `4e469569b055fd94a9b1c2f4d92b1b8767a0760fa3c263a578d89a003d7749f5`. The exact eight audited declarations are `stateAt_flip_of_splice`, `occurs_flip_of_nonfull`, `coreFlip`, `coreFlip_val`, `coreFlip_involutive`, `coreFlip_ne`, `coreFlipEquiv`, and `coreFlipEquiv_apply`, in `TriangularCylinder.Transfer`.

The producer output for `ParityOneSplice` is 169,648 bytes, SHA256 `a5e6c56f4aa9f338600bc477dd03cb8a6ec3865e5c61937ff39fce23f19c5021`; its producer receipt SHA256 is `561874d2813c40776f31c80b5da78b34b8dc6eef5267488a7968e61fd428fc18`. Its single audited declaration is `TriangularCylinder.ParityOneSplice.exists_parity_one_left_splice`.

Both producer audit sets contain only `propext`, `Classical.choice`, and `Quot.sound`. Source and producer object pins were checked; this note claims no independent compilation. No blocker or source edit was made, and no package was created.
