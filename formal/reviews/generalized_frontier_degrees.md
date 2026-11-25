# Root semantic review: generalized degrees and optional subdivision

Date: 2026-11-25 UTC. Reviewer: flowing-tick. Status: PASS within scope.

## Generalized boundary degrees: current full-column application

I read the entire FrontierDegreesGeneral.lean source, SHA256
f43ea3e7c4465edcb75f2dd8beaa6e298201c9d55c3c186c404dd53d3467061a.
It imports only the frozen FrontierDegrees module. No prior source was edited.

The boundary neighbor set is exactly the union of the two embedded neighbor
sets. Because the embeddings have disjoint interiors, a shared neighbor can
only be a shared boundary vertex c, with both P.Adj b c and Q.Adj b c.
The hypothesis excluding this conjunction is therefore precisely the required
global disjointness condition. The proof analyzes the four Sum cases and uses
injectivity to equate the boundary labels in the sole potentially overlapping
case. Set.ncard_union_eq then applies under explicit finite vertex types.

The suffix-only corollary correctly derives that conjunction's negation from
absence of Q boundary edges. It places no restriction on P boundary edges.
Consequently it fits the selected full-column convention: P owns the current
column's selected verticals, Q has no edge entirely in that boundary, and
physical degrees add without counting an edge twice.

The degree-two corollaries reuse the previously reviewed interior identities.
Their boundary premise is the sum of counts equal to two, allowing 2+0, 1+1,
and 0+2. They neither assume nor infer connectivity. Empty boundaries and empty
interior types remain valid; a universally quantified degree assertion on an
empty whole vertex type is vacuous. The new statements fully discharge the
specific degree-sum obligation requested in Atrium397/400/402, conditional on
the separate concrete column-cut decomposition and its local degree premises.
They do not by themselves verify those premises for the cylinder model.

## Optional parked subdivision

I also read the complete FrontierSubdivision.lean source, SHA256
221cabfe3de31ae84b83520fd6fb488b4378fb8b7929129e173d557109e57b3d.
This file is an alternative representation and is not a dependency of the
chosen full-column proof. No concrete cut-stub realization file was created.

The incidence graph gives every distinct stub one left and one right endpoint.
The contracted graph existentially joins the endpoints of each stub. The
contraction sends a stub to its left endpoint, sends its left incidence to a
reflexive reachable pair, and sends its right incidence to an existing crossing
edge. Thus it is correctly treated as a reachability map, not an adjacency
homomorphism. Conversely, every contracted crossing edge has a witnessed stub
that supplies a two-edge path. All non-core vertices attach to their left
endpoint. These maps prove Preconnected equivalence, and the corresponding
maps on Nonempty witnesses correctly establish Connected equivalence.

The claims need no finite types or injective endpoint maps. If an interior
type is empty, existence of the endpoint map forces B empty; there is no
unaccounted isolated-stub exception. Duplicate endpoint pairs preserve
connectivity but can change degrees: two stubs between one left and one right
vertex produce a four-cycle before contraction and a single edge afterwards.
The source explicitly records that limitation and makes no Hamiltonicity claim.

## Independent source-only replay

The root-owned verify_extensions.py compiled FrontierSubstitution,
FrontierDegrees, FrontierDegreesGeneral, and FrontierSubdivision, in that order,
into a newly created empty root-extension-replay/build directory. The Lean
search path used that directory followed by the pinned Mathlib environment;
no prebuilt local proof module was supplied. All four compilations passed with
warnings as errors, empty stderr, and only propext, Classical.choice, and
Quot.sound in the requested declaration audits. All four compiled module hashes
match their authors' recorded hashes. The receipt records the exact versions,
commands, source hashes, and axiom declarations. Source pins, dependency
manifest, and tracked Mathlib files were unchanged during replay.

The source-pin JSON used for that four-module replay is preserved verbatim as
extension-sources.snapshot.json in this directory. A future bundle may add the
separately reviewed edge-replacement module to the top-level pin list without
changing the modules checked by this receipt.

These are independently reviewed generic graph lemmas and compiler checks,
not full cylinder asymptotic theorems, topological classification, external
human acceptance, or evidence of adoption.
