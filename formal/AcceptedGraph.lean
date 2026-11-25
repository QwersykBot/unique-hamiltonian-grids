import AcceptedReconstruction

/-!
# The exact physical graph of accepted data

Reconstruction selects precisely the recorded physical V/H/D masks. The
resulting spanning graph lies in the actual cylinder ambient and loses no
edge when formed from its selected edge set. No degree, connectivity, or
Hamiltonian realization is asserted here.
-/

namespace TriangularEdgeEncoding

open TriangularCylinder

/-- An actual physical edge is selected by a geometry exactly when its ID is marked. -/
theorem mem_realizedEdges_iff {m L : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (id : EdgeId m L) :
    toEdge hm id ∈ realizedEdges hm g ↔ geometryFlag g id = true := by
  constructor
  · intro h
    obtain ⟨other, hother, heq⟩ := Finset.mem_image.mp h
    have hid : other = id := toEdge_injective hm heq
    subst other
    exact (mem_idsOfGeometry g id).mp hother
  · intro h
    exact Finset.mem_image.mpr ⟨id, (mem_idsOfGeometry g id).mpr h, rfl⟩

end TriangularEdgeEncoding

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding CountedHamiltonian

/-- The spanning selected graph reconstructed from the physical accepted data. -/
def acceptedGraph {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : SimpleGraph (Vertex m (n + 2)) :=
  fromEdgeSet (acceptedEdges w : Set (Sym2 (Vertex m (n + 2))))

/-- Every reconstructed adjacency belongs to the actual cylinder graph. -/
theorem acceptedGraph_le {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : acceptedGraph w ≤ graph m (n + 2) hm :=
  selectedGraph_le (fun _ he => acceptedEdges_mem w he)

/-- Forming the simple graph neither loses nor adds a reconstructed physical edge. -/
theorem acceptedGraph_edgeSet {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    (acceptedGraph w).edgeSet = (acceptedEdges w : Set (Sym2 (Vertex m (n + 2)))) :=
  selectedGraph_edgeSet (fun _ he => acceptedEdges_mem w he)

/-- Every reconstructed column has exactly its recorded vertical mask. -/
theorem acceptedGraph_vertical {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    verticalMask hm (acceptedGraph w) = acceptedVerticalMasks w := by
  funext c r
  rw [Bool.eq_iff_iff, verticalMask_physical_iff, acceptedGraph_edgeSet]
  exact mem_realizedEdges_iff hm (acceptedGeometry w) (Sum.inl (r, c))

/-- Every reconstructed cut has exactly its recorded outgoing horizontal mask. -/
theorem acceptedGraph_horizontal {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (c : Fin (n + 1)) :
    (cutState hm (acceptedGraph w) c).horizontal = (acceptedCutStates w c).val.horizontal := by
  funext r
  rw [Bool.eq_iff_iff, cutState_horizontal_physical_iff, acceptedGraph_edgeSet]
  exact mem_realizedEdges_iff hm (acceptedGeometry w) (Sum.inr (Sum.inl (r, cutEdgeIndex c)))

/-- Every reconstructed cut has exactly its recorded outgoing diagonal mask. -/
theorem acceptedGraph_diagonal {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (c : Fin (n + 1)) :
    (cutState hm (acceptedGraph w) c).diagonal = (acceptedCutStates w c).val.diagonal := by
  funext r
  rw [Bool.eq_iff_iff, cutState_diagonal_physical_iff, acceptedGraph_edgeSet]
  exact mem_realizedEdges_iff hm (acceptedGeometry w) (Sum.inr (Sum.inr (r, cutEdgeIndex c)))

end TriangularCylinder.Transfer
