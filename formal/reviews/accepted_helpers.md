# Bounded read-only reviews of root-authored accepted-data helpers

Reviewer lane: `/root/formal_matrix_contraction`. Each review read the complete named source and checked the indicated interfaces against the frozen definitions. These were statement/data/indexing reviews, not independent compiler replays. No source or build artifact was modified for a review. Result for all four: **PASS, no blocker identified**.

## AcceptedGraph

Source SHA256: `a713fa20cb2d4dcd85daad50e796732f191b2d9fd8d03b979b935ec71b18ebcd`.

The physical-ID membership equivalence follows from `toEdge` injectivity and the existing geometry flag definition. `acceptedGraph` is exactly `fromEdgeSet` of `acceptedEdges`. Ambient membership proves both the graph inclusion and the absence of edge loss under reconstruction. The V/H/D mask recovery theorems identify all physical columns and cuts with their recorded masks. No degree, connectedness, Hamiltonian, or global compatibility premise is concealed in those statements.

## AcceptedExtensionality

Source SHA256: `40167558c4c3ff4e2922c165470c69fa19aa572d4a60b87ac4964a9db595596b`.

`last_observed_state` handles length zero through the path's endpoint equality and handles successors by dropping the first labelled step. `observed_step` retains the predicate of the actual label at consecutive observed states. The actual initial/local/terminal realization predicates use the correct physical V positions: column 0, local column i+1, and final column n+1. The terminal observation remains valid at n=0.

The path extensionality argument requires injective label values, matches successive target states, and recursively identifies the remaining path. For actual mask subtypes, subtype extensionality supplies that injectivity. The accepted-object extensionality theorem uses every cut state and every column mask; it does not assume a global Hamiltonian presentation or conflate labels with their existential witnesses.

## AcceptedStateRecovery

Source SHA256: `3660e0f14a3815d452fb76cf293e3818bcaa4d98184b17a860c5afdf9095f341`.

The first-column relation follows from the actual vertical mask and ambient inclusion. The inductive relation step compares the reconstructed graph with an actual local witness using old H/D masks, the induction hypothesis for old reachability, and the new V mask. Reconstructed connectedness is an explicit premise; the comparison witness's connectedness is derived from its actual Hamiltonian cycle. The source therefore proves exactly the conditional R-field recovery it states. It neither assumes nor establishes unconditional reconstructed connectedness or Hamiltonicity.

## AcceptedUniqueness

Source SHA256: `5f901a823d12074683a03336c224c0429684f50cc43b5a2a289dd75534a1aab9`.

Full raw-state equality combines the exact H/D fields, conditional R recovery, and unconditional parity recovery. Equal reconstructed edge sets give equal reconstructed graphs, transfer the explicit connectedness premise, and then yield identical recorded states and vertical masks; the existing accepted extensionality theorem supplies equality of objects.

`acceptedSelectionOfRealization` packages the existing finset and parity only after receiving an explicit exact Hamiltonian-realization proof. Connectedness follows from that proof. The full right inverse then combines physical edge recovery with the conditional accepted-object uniqueness result. Its n≥1 requirement matches the domain of the canonical `selectionAccepted` map. It does not establish realization existence or a counting equivalence by itself.
