import CountedHamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Exact selected-edge characterization bridges

These statements concern finite undirected edge sets and Mathlib's standard
`Walk.IsHamiltonianCycle`.  No abstract existence theorem for connected
2-regular graphs is constructed here.  The reverse bridge takes such a cycle
as an input and proves that it exhausts the selected edges before transferring
it to the original graph.
-/

namespace CountedHamiltonian

open SimpleGraph

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A walk and its spanning subgraph have exactly the same undirected edges. -/
theorem walk_spanningCoe_edgeSet {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) : p.toSubgraph.spanningCoe.edgeSet = p.edgeSet := by
  change p.toSubgraph.edgeSet = p.edgeSet
  exact p.edgeSet_toSubgraph

/-- Reconstructing a graph from the walk's selected edges gives its spanning
walk subgraph, including the same ambient vertex type. -/
theorem fromEdgeSet_selectedEdges {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) :
    fromEdgeSet (selectedEdges p : Set (Sym2 V)) = p.toSubgraph.spanningCoe := by
  rw [coe_selectedEdges, ← walk_spanningCoe_edgeSet, fromEdgeSet_edgeSet]

/-- The selected spanning graph of a standard Hamiltonian cycle is connected. -/
theorem hamiltonian_selected_connected {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsHamiltonianCycle) :
    (fromEdgeSet (selectedEdges p : Set (Sym2 V))).Connected := by
  rw [fromEdgeSet_selectedEdges]
  have hs : p.toSubgraph.IsSpanning := fun w =>
    p.mem_verts_toSubgraph.mpr (hp.mem_support w)
  exact (p.toSubgraph.spanningCoeEquivCoeOfSpanning hs).connected_iff.mpr
    p.toSubgraph_connected.coe

/-- Every vertex of the selected spanning graph has exactly two neighbors. -/
theorem hamiltonian_selected_ncard {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsHamiltonianCycle) (w : V) :
    ((fromEdgeSet (selectedEdges p : Set (Sym2 V))).neighborSet w).ncard = 2 := by
  rw [fromEdgeSet_selectedEdges]
  change (p.toSubgraph.neighborSet w).ncard = 2
  exact hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support w)

/-- The forward characterization holds without an extra finiteness or
nonemptiness hypothesis: the Hamiltonian witness supplies both. -/
theorem realization_selected_connected_two {G : SimpleGraph V}
    {E : Finset (Sym2 V)} (h : HasHamiltonianRealization G E) :
    (fromEdgeSet (E : Set (Sym2 V))).Connected ∧
      ∀ v, ((fromEdgeSet (E : Set (Sym2 V))).neighborSet v).ncard = 2 := by
  rcases h with ⟨v, p, hp, rfl⟩
  exact ⟨hamiltonian_selected_connected hp, hamiltonian_selected_ncard hp⟩

omit [DecidableEq V] in
/-- Membership in an ambient simple graph rules out all diagonal pairs, so
`fromEdgeSet` loses no selected edge. -/
theorem selectedGraph_edgeSet {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet) :
    (fromEdgeSet (E : Set (Sym2 V))).edgeSet = (E : Set (Sym2 V)) := by
  rw [edgeSet_fromEdgeSet]
  ext e
  exact ⟨fun h => h.1, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (hE he)⟩⟩

omit [DecidableEq V] in
/-- The selected graph embeds into the original graph by the identity map. -/
theorem selectedGraph_le {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet) :
    fromEdgeSet (E : Set (Sym2 V)) ≤ G := by
  simpa only [fromEdgeSet_edgeSet] using fromEdgeSet_mono hE

/-- In a finite graph with exactly two neighbors per vertex, a standard
Hamiltonian cycle uses every graph edge. -/
theorem hamiltonian_edgeSet_eq_of_ncard [Finite V] {H : SimpleGraph V}
    {v : V} {p : H.Walk v v} (hp : p.IsHamiltonianCycle)
    (hdeg : ∀ w, (H.neighborSet w).ncard = 2) : p.edgeSet = H.edgeSet := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hcyc : H.IsCycles := fun {_} _ => hdeg _
  have hspan : p.toSubgraph.spanningCoe = H := by
    ext w x
    exact hp.isCycle.adj_toSubgraph_iff_of_isCycles hcyc
      (p.mem_verts_toSubgraph.mpr (hp.mem_support w)) x
  rw [← walk_spanningCoe_edgeSet, hspan]

/-- Exact finite-set recovery, including exclusion of ignored diagonal pairs. -/
theorem selectedEdges_eq_of_hamiltonian_selected [Finite V]
    {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet)
    {v : V} {p : (fromEdgeSet (E : Set (Sym2 V))).Walk v v}
    (hp : p.IsHamiltonianCycle)
    (hdeg : ∀ w, ((fromEdgeSet (E : Set (Sym2 V))).neighborSet w).ncard = 2) :
    selectedEdges p = E := by
  apply Finset.coe_injective
  rw [coe_selectedEdges, hamiltonian_edgeSet_eq_of_ncard hp hdeg,
    selectedGraph_edgeSet hE]

/-- Transferring a walk into a supergraph preserves its selected edge set. -/
theorem selectedEdges_mapLe {H G : SimpleGraph V} (hHG : H ≤ G)
    {v w : V} (p : H.Walk v w) : selectedEdges (p.mapLe hHG) = selectedEdges p := by
  apply selectedEdges_eq_of_edgeSet_eq
  simp [Walk.mapLe, Walk.edgeSet_map, Hom.coe_ofLE]

/-- Given a standard Hamiltonian cycle in the 2-regular selected graph, it
realizes the entire exact selected edge set in the original graph. -/
theorem realization_of_selected_hamiltonian [Finite V]
    {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet)
    {v : V} {p : (fromEdgeSet (E : Set (Sym2 V))).Walk v v}
    (hp : p.IsHamiltonianCycle)
    (hdeg : ∀ w, ((fromEdgeSet (E : Set (Sym2 V))).neighborSet w).ncard = 2) :
    HasHamiltonianRealization G E := by
  refine ⟨v, p.mapLe (selectedGraph_le hE), ?_, ?_⟩
  · exact hp.map (Hom.ofLE (selectedGraph_le hE)) Function.bijective_id
  · rw [selectedEdges_mapLe]
    exact selectedEdges_eq_of_hamiltonian_selected hE hp hdeg

omit [DecidableEq V] in
/-- The ncard formulation is exactly the usual degree formulation whenever
the neighbor set is equipped with its finite enumeration. -/
theorem neighborSet_ncard_eq_degree (H : SimpleGraph V) (v : V)
    [Fintype (H.neighborSet v)] : (H.neighborSet v).ncard = H.degree v := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

end CountedHamiltonian
