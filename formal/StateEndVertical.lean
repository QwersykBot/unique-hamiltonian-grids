import BoundaryVertical
import BoundaryState
import SelectedCharacterization

/-!
# Selected end verticals from a nonfull actual boundary state

Three or more columns use the frozen end-vertical theorem. At exactly two
columns, a missing vertical at either end forces every horizontal and forward
diagonal across the unique cut, contradicting the nonfull-mask assumption.
No reference zigzag, transfer graph, or parity statement is needed.
-/

namespace TriangularCylinder.StateEndVertical

open SimpleGraph BoundaryState BoundaryVertical TriangularEdgeEncoding

/-- At the unique two-column cut, either missing end forces both masks full. -/
theorem full_masks_of_no_end_vertical_two_columns {m : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m 2)) (hsub : H ≤ graph m 2 hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (firstCol 2 (by decide)) ∨
      NoVerticalAt H (lastCol 2 (by decide))) :
    ∀ r, (stateAt (j := 0) (k := 1) hm (by decide) H).horizontal r = true ∧
      (stateAt (j := 0) (k := 1) hm (by decide) H).diagonal r = true := by
  letI : NeZero m := ⟨by omega⟩
  intro r
  have hcross : H.Adj (r, boundaryCol 0 1) (r, nextCol (j := 0) (k := 1) (by decide)) ∧
      H.Adj (r, boundaryCol 0 1) (r + 1, nextCol (j := 0) (k := 1) (by decide)) := by
    rcases hno with hfirst | hlast
    · exact first_crossings_selected_of_no_vertical hm (by decide) H hsub hdeg hfirst r
    · exact last_crossings_selected_of_no_vertical hm (by decide) H hsub hdeg hlast r
  constructor
  · exact (stateAt_horizontal_iff (j := 0) (k := 1) hm (by decide) H r).mpr hcross.1
  · apply (stateAt_diagonal_iff (j := 0) (k := 1) hm (by decide) H r).mpr
    have hsucc : rowSucc hm r = r + 1 :=
      (nextRow_iff_add_one hm r (rowSucc hm r)).mp (nextRow_rowSucc hm r)
    simpa only [hsucc] using hcross.2

/-- A nonfull state of an actual Hamiltonian cycle has selected verticals at
both physical ends, including the two-column case. -/
theorem exists_selected_verticals_of_nonfull_stateAt {m j k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) {v : Vertex m (j + 1 + k)}
    (C : (graph m (j + 1 + k) hm).Walk v v) (hC : C.IsHamiltonianCycle)
    (hnonfull : ¬ (∀ r, (stateAt hm hk (fromEdgeSet C.edgeSet)).horizontal r = true ∧
      (stateAt hm hk (fromEdgeSet C.edgeSet)).diagonal r = true)) :
    (∃ r s : Fin m, NextRow r s ∧
      (fromEdgeSet C.edgeSet).Adj
        (r, firstCol (j + 1 + k) (by omega)) (s, firstCol (j + 1 + k) (by omega))) ∧
    (∃ r s : Fin m, NextRow r s ∧
      (fromEdgeSet C.edgeSet).Adj
        (r, lastCol (j + 1 + k) (by omega)) (s, lastCol (j + 1 + k) (by omega))) := by
  classical
  have hsub := cycle_selectedGraph_le hm C
  have hconn : (fromEdgeSet C.edgeSet).Connected := by
    simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_connected hC
  have hdeg : ∀ w, ((fromEdgeSet C.edgeSet).neighborSet w).ncard = 2 := by
    intro w
    simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_ncard hC w
  by_cases hthree : 3 ≤ j + 1 + k
  · exact exists_selected_verticals_at_both_ends hm hthree
      (fromEdgeSet C.edgeSet) hsub hconn hdeg
  · have hj : j = 0 := by omega
    have hkone : k = 1 := by omega
    subst j
    subst k
    constructor
    · by_contra h
      apply hnonfull
      apply full_masks_of_no_end_vertical_two_columns hm (fromEdgeSet C.edgeSet) hsub hdeg
      left
      intro r s hrs hadj
      exact h ⟨r, s, hrs, hadj⟩
    · by_contra h
      apply hnonfull
      apply full_masks_of_no_end_vertical_two_columns hm (fromEdgeSet C.edgeSet) hsub hdeg
      right
      intro r s hrs hadj
      exact h ⟨r, s, hrs, hadj⟩

/-- The same end availability in the selected-edge form used by concrete splicing. -/
theorem exists_selected_end_edges_of_nonfull_stateAt {m j k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) {v : Vertex m (j + 1 + k)}
    (C : (graph m (j + 1 + k) hm).Walk v v) (hC : C.IsHamiltonianCycle)
    (hnonfull : ¬ (∀ r, (stateAt hm hk (fromEdgeSet C.edgeSet)).horizontal r = true ∧
      (stateAt hm hk (fromEdgeSet C.edgeSet)).diagonal r = true)) :
    (∃ r s : Fin m, NextRow r s ∧
      s((r, firstCol (j + 1 + k) (by omega)),
        (s, firstCol (j + 1 + k) (by omega))) ∈ C.edges) ∧
    (∃ r s : Fin m, NextRow r s ∧
      s((r, lastCol (j + 1 + k) (by omega)),
        (s, lastCol (j + 1 + k) (by omega))) ∈ C.edges) := by
  obtain ⟨⟨r, s, hrs, hfirst⟩, ⟨t, u, htu, hlast⟩⟩ :=
    exists_selected_verticals_of_nonfull_stateAt hm hk C hC hnonfull
  exact ⟨⟨r, s, hrs, hfirst.1⟩, ⟨t, u, htu, hlast.1⟩⟩

#print axioms full_masks_of_no_end_vertical_two_columns
#print axioms exists_selected_verticals_of_nonfull_stateAt
#print axioms exists_selected_end_edges_of_nonfull_stateAt

end TriangularCylinder.StateEndVertical
