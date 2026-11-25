import AcceptedStateRecovery
import AcceptedParity

/-!
# Unique accepted encoding once realization is supplied

The reconstructed physical graph determines every recorded state field.
For the boundary relation this uses its connectedness, while parity follows
from the local label identities. Equal reconstructed edge sets therefore
give equal accepted objects whenever the graph is connected. A separately
supplied Hamiltonian realization then gives a counted parity selection whose
canonical encoding is the original object. Realization existence is separate.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding CountedHamiltonian

/-- A connected reconstructed graph recovers every field of its recorded raw state. -/
theorem acceptedGraph_state {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (hconn : (acceptedGraph w).Connected)
    (c : Fin (n + 1)) :
    cutState hm (acceptedGraph w) c = (acceptedCutStates w c).val :=
  RawBoundaryState.ext (acceptedGraph_horizontal w c) (acceptedGraph_diagonal w c)
    (acceptedGraph_reach w hconn c) (acceptedGraph_parity w c)

/-- Equal physical edge sets distinguish accepted objects once connectedness is known. -/
theorem accepted_ext_of_edges_eq {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w z : AcceptedObject hm p n) (hconn : (acceptedGraph w).Connected)
    (hE : acceptedEdges w = acceptedEdges z) : w = z := by
  have hG : acceptedGraph w = acceptedGraph z := by
    unfold acceptedGraph
    rw [hE]
  have hconnZ : (acceptedGraph z).Connected := hG ▸ hconn
  apply accepted_ext
  · funext c
    apply Subtype.ext
    rw [← acceptedGraph_state w hconn c, ← acceptedGraph_state z hconnZ c, hG]
  · rw [← acceptedGraph_vertical w, ← acceptedGraph_vertical z, hG]

/-- A separately proved exact realization gives the existing counted parity selection. -/
def acceptedSelectionOfRealization {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n)
    (hRealization : HasHamiltonianRealization (graph m (n + 2) hm) (acceptedEdges w)) :
    ParitySelection hm p (n + 2) :=
  ⟨⟨acceptedEdges w, hRealization⟩, selectionParity_acceptedEdges w hRealization⟩

/-- Any supplied exact Hamiltonian realization forces reconstructed connectedness. -/
theorem acceptedGraph_connected_of_realization {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n)
    (hRealization : HasHamiltonianRealization (graph m (n + 2) hm) (acceptedEdges w)) :
    (acceptedGraph w).Connected := by
  obtain ⟨v, C, hC, hE⟩ := hRealization
  change (fromEdgeSet (acceptedEdges w : Set (Sym2 (Vertex m (n + 2))))).Connected
  rw [← hE]
  exact hamiltonian_selected_connected hC

/-- Once exact realization exists, the counted-selection encoding recovers the
entire accepted object, including every state and each physical label. -/
theorem selectionAccepted_of_realization {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {p : ZMod 2} (w : AcceptedObject hm p n)
    (hRealization : HasHamiltonianRealization (graph m (n + 2) hm) (acceptedEdges w)) :
    selectionAccepted hm hn p (acceptedSelectionOfRealization w hRealization) = w := by
  apply Eq.symm
  apply accepted_ext_of_edges_eq w _ (acceptedGraph_connected_of_realization w hRealization)
  rw [acceptedEdges_selectionAccepted]
  rfl

end TriangularCylinder.Transfer
