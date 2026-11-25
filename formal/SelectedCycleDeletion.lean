import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Deleting a selected edge from a Hamiltonian cycle

The exact graph selected by a Hamiltonian cycle is connected. Transferring
the cycle into this selected graph shows that each selected edge lies on a
cycle, hence is not a bridge. Its deletion therefore preserves connectedness.

No finiteness typeclass is required: the Hamiltonian witness supplies a walk
whose support contains every vertex. No cylinder or splicing statement is
proved in this module.
-/

namespace CylinderFrontier

open SimpleGraph

/-- Deleting any selected edge from the exact selected graph of a Hamiltonian
cycle leaves a connected graph on the original vertex type. -/
theorem selected_cycle_delete_edge_connected {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} (C : G.Walk u u)
    (hC : C.IsHamiltonianCycle) (he : s(x, y) ∈ C.edges) :
    ((fromEdgeSet C.edgeSet).deleteEdges {s(x, y)}).Connected := by
  let H := fromEdgeSet C.edgeSet
  have htransfer : ∀ e, e ∈ C.edges → e ∈ H.edgeSet := by
    intro e he'
    change e ∈ (fromEdgeSet C.edgeSet).edgeSet
    rw [edgeSet_fromEdgeSet]
    exact ⟨he', G.not_isDiag_of_mem_edgeSet (C.edges_subset_edgeSet he')⟩
  let D := C.transfer H htransfer
  have hD : D.IsCycle := hC.isCycle.transfer htransfer
  have hsupport : ∀ v, v ∈ D.support := by
    intro v
    simpa only [D, Walk.support_transfer] using hC.mem_support v
  have hconnected : H.Connected := (connected_iff_exists_forall_reachable H).mpr
    ⟨u, fun v => (D.takeUntil v (hsupport v)).reachable⟩
  apply hconnected.connected_delete_edge_of_not_isBridge
  intro hbridge
  have hnot := (isBridge_iff_adj_and_forall_cycle_not_mem.mp hbridge).2 D hD
  apply hnot
  simpa only [D, Walk.edges_transfer] using he

#print axioms selected_cycle_delete_edge_connected

end CylinderFrontier
