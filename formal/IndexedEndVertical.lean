import StateEndVertical
import CycleWidthTransport

/-!
# Selected physical end edges from a nonfull indexed cut state

An actual cycle is transported temporarily to the split width expected by
`StateEndVertical`. The conclusion is transported back to selected edges
of the same original cycle, at its original first and last columns.
-/

namespace TriangularCylinder.IndexedEndVertical

open SimpleGraph BoundaryState Transfer CycleWidthTransport

private theorem widthEquiv_firstCol {m L L' : ℕ} (h : L = L')
    (hL : 2 ≤ L) (r : Fin m) :
    widthEquiv h (r, firstCol L hL) = (r, firstCol L' (h ▸ hL)) := by
  cases h
  rfl

private theorem widthEquiv_lastCol {m L L' : ℕ} (h : L = L')
    (hL : 2 ≤ L) (r : Fin m) :
    widthEquiv h (r, lastCol L hL) = (r, lastCol L' (h ▸ hL)) := by
  cases h
  rfl

/-- A nonfull indexed cut state of an actual Hamiltonian cycle provides
selected vertical edges at both ends of that same original cycle. -/
theorem exists_selected_end_edges_of_nonfull_cutState {m n : ℕ}
    (hm : 3 ≤ m) {v : Vertex m (n + 2)}
    (C : (graph m (n + 2) hm).Walk v v) (hC : C.IsHamiltonianCycle)
    (c : Fin (n + 1))
    (hnonfull : ¬ FullOutgoing (cutState hm (fromEdgeSet C.edgeSet) c)) :
    (∃ r s : Fin m, NextRow r s ∧
      s((r, firstCol (n + 2) (by omega)),
        (s, firstCol (n + 2) (by omega))) ∈ C.edges) ∧
    (∃ r s : Fin m, NextRow r s ∧
      s((r, lastCol (n + 2) (by omega)),
        (s, lastCol (n + 2) (by omega))) ∈ C.edges) := by
  let D := C.map (widthHom hm (cutWidth_eq c).symm)
  have hD : D.IsHamiltonianCycle :=
    map_isHamiltonianCycle hm (cutWidth_eq c).symm C hC
  have hgraph : fromEdgeSet D.edgeSet = cutGraph (fromEdgeSet C.edgeSet) c :=
    selectedGraph_map hm (cutWidth_eq c).symm C
  have hk : 1 ≤ cutTail c := cutTail_pos c
  have hnonfullD : ¬ FullOutgoing
      (stateAt (j := c.val) (k := cutTail c) hm hk (fromEdgeSet D.edgeSet)) := by
    rw [hgraph]
    exact hnonfull
  obtain ⟨⟨r, s, hrs, hfirst⟩, ⟨t, u, htu, hlast⟩⟩ :=
    StateEndVertical.exists_selected_verticals_of_nonfull_stateAt
      (j := c.val) (k := cutTail c) hm hk D hD hnonfullD
  rw [hgraph] at hfirst hlast
  simp only [cutGraph, SimpleGraph.comap_adj, widthEquiv_firstCol] at hfirst
  simp only [cutGraph, SimpleGraph.comap_adj, widthEquiv_lastCol] at hlast
  exact ⟨⟨r, s, hrs, hfirst.1⟩, ⟨t, u, htu, hlast.1⟩⟩

#print axioms exists_selected_end_edges_of_nonfull_cutState

end TriangularCylinder.IndexedEndVertical
