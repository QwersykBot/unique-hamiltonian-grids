import SelectedCharacterization
import ConnectedTwoRegular

/-!
# Finite selected-edge characterization

This file composes the separately supplied generic connected degree-two
wrapper with the exact selected-edge bridges.  The result concerns the fixed
ambient vertex labels and an undirected finite edge set, not a rooted or
oriented cycle presentation.  It makes no cylinder-counting or topology claim.
-/

namespace CountedHamiltonian

open SimpleGraph

variable {V : Type*} [Finite V] [DecidableEq V]

/-- An admissible finite selection is Hamiltonian exactly when its spanning
selected graph is connected and has two neighbors at every vertex. -/
theorem realization_iff_connected_two {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet) :
    HasHamiltonianRealization G E ↔
      (fromEdgeSet (E : Set (Sym2 V))).Connected ∧
        ∀ v, ((fromEdgeSet (E : Set (Sym2 V))).neighborSet v).ncard = 2 := by
  refine ⟨realization_selected_connected_two, ?_⟩
  rintro ⟨hconn, hdeg⟩
  obtain ⟨v, p, hp⟩ :=
    ConnectedTwoRegular.exists_isHamiltonianCycle_of_neighbor_ncard_two hconn hdeg
  exact realization_of_selected_hamiltonian hE hp hdeg

/-- The usual degree form of the same exact selected-edge characterization. -/
theorem realization_iff_connected_degree_two {G : SimpleGraph V}
    {E : Finset (Sym2 V)} [LocallyFinite (fromEdgeSet (E : Set (Sym2 V)))]
    (hE : (E : Set (Sym2 V)) ⊆ G.edgeSet) :
    HasHamiltonianRealization G E ↔
      (fromEdgeSet (E : Set (Sym2 V))).Connected ∧
        ∀ v, (fromEdgeSet (E : Set (Sym2 V))).degree v = 2 := by
  simpa only [neighborSet_ncard_eq_degree] using realization_iff_connected_two hE

/-- Without a precondition on the selection, admissibility is part of the
characterization. This explicitly prevents hidden diagonal or ambient-nonedge
pairs from passing through `fromEdgeSet`. -/
theorem realization_iff_subset_connected_two {G : SimpleGraph V}
    {E : Finset (Sym2 V)} :
    HasHamiltonianRealization G E ↔
      (E : Set (Sym2 V)) ⊆ G.edgeSet ∧
        (fromEdgeSet (E : Set (Sym2 V))).Connected ∧
          ∀ v, ((fromEdgeSet (E : Set (Sym2 V))).neighborSet v).ncard = 2 := by
  constructor
  · intro h
    refine ⟨?_, realization_selected_connected_two h⟩
    intro e he
    exact selection_edge_mem G (⟨E, h⟩ : Selection G) he
  · rintro ⟨hE, hconn, hdeg⟩
    exact (realization_iff_connected_two hE).mpr ⟨hconn, hdeg⟩

end CountedHamiltonian
