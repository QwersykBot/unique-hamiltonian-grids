import ColumnGeometry

/-!
Two consecutive physical columns embed injectively into any cylinder with
that cut. Full crossing means every H and D at the cut is actually selected.
No degree, connectedness or Hamiltonian premise is imposed in this module.
-/

namespace TriangularCutSaturation

open SimpleGraph TriangularCylinder TriangularEdgeEncoding

/-- Shift the two local columns to the consecutive columns at cut `c`. -/
def columnShift {m L : ℕ} (c : Fin (L - 1)) (x : Vertex m 2) : Vertex m L :=
  (x.1, ⟨c.val + x.2.val, by have hc := c.isLt; have hx := x.2.isLt; omega⟩)

theorem columnShift_injective {m L : ℕ} (c : Fin (L - 1)) :
    Function.Injective (columnShift (m := m) c) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun v : Vertex m L => v.1) h
  · apply Fin.ext
    have hc := congrArg (fun v : Vertex m L => v.2.val) h
    simp only [columnShift] at hc
    omega

@[simp] theorem columnShift_left {m L : ℕ} (c : Fin (L - 1)) (r : Fin m) :
    columnShift c (r, 0) = (r, lowerCol c) := by
  simp [columnShift, lowerCol]

@[simp] theorem columnShift_right {m L : ℕ} (c : Fin (L - 1)) (r : Fin m) :
    columnShift c (r, 1) = (r, upperCol c) := rfl

/-- All physical horizontal and diagonal edges at this cut are present. -/
def FullCrossingAt {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin (L - 1)) : Prop :=
  ∀ r : Fin m,
    H.Adj (r, lowerCol c) (r, upperCol c) ∧
      H.Adj (r, lowerCol c) (rowSucc hm r, upperCol c)

/-- Membership of a selected physical ID gives adjacency in the concrete
selected spanning graph, with diagonal pairs excluded by the ambient edge. -/
theorem selectedId_adj {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L)
    {id : EdgeId m L} (hid : id ∈ idsOfGeometry g) :
    (fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))).Adj
      (sourceVertex id) (targetVertex hm id) := by
  apply (fromEdgeSet_adj _).mpr
  constructor
  · change toEdge hm id ∈ realizedEdges hm g
    exact Finset.mem_image.mpr ⟨id, hid, rfl⟩
  · exact (show (graph m L hm).Adj (sourceVertex id) (targetVertex hm id) from
      Or.inl (forward_source_target hm id)).ne

/-- The Boolean full-H/D mask condition implies actual full crossing. -/
theorem fullCrossingAt_of_masks {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L)
    (c : Fin (L - 1)) (hfull : ∀ r : Fin m, g.2.1 c r = true ∧ g.2.2 c r = true) :
    FullCrossingAt hm
      (fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))) c := by
  intro r
  constructor
  · apply selectedId_adj hm g (id := .inr (.inl (r, c)))
    exact (mem_idsOfGeometry g _).mpr (hfull r).1
  · apply selectedId_adj hm g (id := .inr (.inr (r, c)))
    exact (mem_idsOfGeometry g _).mpr (hfull r).2

end TriangularCutSaturation
