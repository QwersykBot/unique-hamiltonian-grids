import RowRotation
import SpliceSelectedGraph
import SelectedCycleDeletion

/-!
# A concrete parity-one left splice

The constructor returns one actual joined cycle together with the connected
three-column gadget and exact selected-graph identity. It is independent of
which cuts of the old cycle will subsequently be encoded as boundary states.
-/

namespace TriangularCylinder.ParityOneSplice

open SimpleGraph SplicePrefixCoordinates CylinderFrontier.EdgeReplacement

/-- Prepend an aligned actual three-column auxiliary at a selected first-end
vertical. The same joined cycle has parity increment one and realizes the
exact connected-gadget replacement of that old selected edge. -/
theorem exists_parity_one_left_splice {m b : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ b)
    (r s : Fin m) (hrs : NextRow r s) {v : Vertex m b}
    (B : (graph m b hm).Walk v v) (hB : B.IsHamiltonianCycle)
    (hfirst : s((r, firstCol b hb), (s, firstCol b hb)) ∈ B.edges) :
    ∃ w : Vertex m (3 + b), ∃ J : (graph m (3 + b) hm).Walk w w,
      ∃ GA : SimpleGraph (Vertex m 3), ∃ a₀ a₁ : Vertex m 3,
        J.IsHamiltonianCycle ∧ typeParity hm J = 1 + typeParity hm B ∧
        GA.Connected ∧
        (fromEdgeSet B.edgeSet).Adj (r, firstCol b hb) (s, firstCol b hb) ∧
        (fromEdgeSet J.edgeSet).comap (columnSumEquiv m 3 b) =
          replacementGraph (fromEdgeSet B.edgeSet) GA
            (r, firstCol b hb) (s, firstCol b hb) a₀ a₁ := by
  classical
  have ha : 2 ≤ 3 := by decide
  obtain ⟨u, A, hA, hAparity, _, hAright⟩ :=
    exists_aligned_three_column_auxiliary m hm r s r s hrs hrs
  obtain ⟨J, hJ, hparity, hset⟩ :=
    exists_splice_of_selected_edges hm ha hb r s hrs A B hA hB hAright hfirst
  let a₀ : Vertex m 3 := (r, lastCol 3 ha)
  let a₁ : Vertex m 3 := (s, lastCol 3 ha)
  let GA : SimpleGraph (Vertex m 3) :=
    (fromEdgeSet A.edgeSet).deleteEdges {s(a₀, a₁)}
  refine ⟨_, J, GA, a₀, a₁, hJ, ?_, ?_, ?_, ?_⟩
  · simpa only [hAparity] using hparity
  · exact CylinderFrontier.selected_cycle_delete_edge_connected A hA hAright
  · exact (fromEdgeSet_adj B.edgeSet).mpr
      ⟨hfirst, (vertical_edge hm r s hrs (firstCol b hb)).ne⟩
  · exact SpliceSelectedGraph.selected_splice_comap hm ha hb r s A B J hset

#print axioms exists_parity_one_left_splice

end TriangularCylinder.ParityOneSplice
