import BoundaryParityUpdates
import AcceptedGraph
import AcceptedExtensionality

/-!
# Exact parity of reconstructed accepted data

Actual realization witnesses force the initial, local, and terminal parity
identities. Induction through the observed cuts therefore recovers every
recorded parity and the total physical edge weight. No connectedness or
Hamiltonian realization of the reconstructed graph is needed for these
identities. The existing selection parity is identified when a realization
proof is supplied separately.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding BoundaryParity CountedHamiltonian
open scoped BigOperators

/-- Every reconstructed cut has its recorded parity, without a connectivity premise. -/
theorem acceptedGraph_parity {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (c : Fin (n + 1)) :
    (cutState hm (acceptedGraph w) c).parity = (acceptedCutStates w c).val.parity := by
  refine Fin.induction ?_ (fun i ih => ?_) c
  · rw [cutState_parity_initial, acceptedGraph_vertical, acceptedGraph_diagonal]
    exact (initialLabel_parity hm (acceptedCutStates w 0)
      ⟨acceptedVerticalMasks w 0, accepted_initial_realized w⟩).symm
  · rw [cutState_parity_succ, ih, acceptedGraph_vertical, acceptedGraph_diagonal]
    exact (localLabel_parity hm (acceptedCutStates w i.castSucc) (acceptedCutStates w i.succ)
      ⟨acceptedVerticalMasks w i.succ.castSucc, accepted_local_realized w i⟩).symm

/-- Every accepted object has exactly its terminal class as total physical meridian weight. -/
theorem acceptedEdges_parity {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    (∑ e ∈ acceptedEdges w, meridianWeight hm e) = p := by
  rw [acceptedEdges, sum_realizedEdges_eq_selectedIds,
    ← selectedPhysicalIds_realizedEdges hm (acceptedGeometry w)]
  change (∑ id ∈ selectedPhysicalIds hm (acceptedGraph w),
    meridianWeight hm (toEdge hm id)) = p
  rw [selectedPhysicalIds_sum_terminal, acceptedGraph_parity, acceptedGraph_vertical]
  exact (terminalLabel_parity hm p (acceptedCutStates w (Fin.last n))
    ⟨acceptedVerticalMasks w (Fin.last (n + 1)), accepted_terminal_realized w⟩).symm

/-- The same identity for the existing physical-ID geometry parity definition. -/
theorem acceptedGeometry_parity {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : geometryParity hm (acceptedGeometry w) = p := by
  change (∑ id ∈ idsOfGeometry (acceptedGeometry w), meridianWeight hm (toEdge hm id)) = p
  rw [← sum_realizedEdges_eq_selectedIds hm (acceptedGeometry w) (meridianWeight hm)]
  exact acceptedEdges_parity w

/-- A separately supplied Hamiltonian realization has the existing counted parity `p`. -/
theorem selectionParity_acceptedEdges {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n)
    (hRealization : HasHamiltonianRealization (graph m (n + 2) hm) (acceptedEdges w)) :
    selectionParity hm ⟨acceptedEdges w, hRealization⟩ = p :=
  acceptedEdges_parity w

end TriangularCylinder.Transfer
