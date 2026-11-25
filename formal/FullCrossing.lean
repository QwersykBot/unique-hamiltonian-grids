import ColumnEmbedding
import ZigzagException
import CycleSaturation

/-!
If a connected two-regular selected graph contains every horizontal and
diagonal edge across one cut, it already contains the entire two-column
zigzag cycle. Saturation of that supplied cycle forces exactly two columns.
The result applies to actual selected edges, without a frontier surrogate.
-/

namespace TriangularCutSaturation

open SimpleGraph TriangularCylinder TriangularEdgeEncoding

/-- The actual zigzag selected graph maps to the two columns at a full cut. -/
def zigzagInto {m L : ℕ} (hm : 3 ≤ m) (H : SimpleGraph (Vertex m L))
    (c : Fin (L - 1)) (hfull : FullCrossingAt hm H c) :
    TriangularZigzag.selectedGraph hm →g H where
  toFun := columnShift c
  map_rel' := by
    intro x y hxy
    rcases (TriangularZigzag.selectedGraph_adj hm x y).mp hxy with
      ⟨r, h⟩ | ⟨r, h⟩
    · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [TriangularZigzag.left, TriangularZigzag.right,
          columnShift_left, columnShift_right] using (hfull r).1
      · simpa only [TriangularZigzag.left, TriangularZigzag.right,
          columnShift_left, columnShift_right] using (hfull r).1.symm
    · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [TriangularZigzag.left, TriangularZigzag.right,
          columnShift_left, columnShift_right] using (hfull r).2
      · simpa only [TriangularZigzag.left, TriangularZigzag.right,
          columnShift_left, columnShift_right] using (hfull r).2.symm

theorem zigzagInto_injective {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin (L - 1))
    (hfull : FullCrossingAt hm H c) : Function.Injective (zigzagInto hm H c hfull) :=
  columnShift_injective c

/-- A full physical H/D cut in a finite connected two-regular graph forces
the whole vertex set to consist of exactly those two columns. No ambient
edge-containment premise is needed for this stronger saturation statement. -/
theorem length_two_of_fullCrossingAt {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin (L - 1))
    (hconn : H.Connected) (hdegree : ∀ v, (H.neighborSet v).ncard = 2)
    (hfull : FullCrossingAt hm H c) : L = 2 := by
  obtain ⟨v, p, hp⟩ := TriangularZigzag.exists_selectedGraph_isHamiltonianCycle hm
  let f := zigzagInto hm H c hfull
  have hc : (p.map f).IsCycle := hp.isCycle.map (zigzagInto_injective hm H c hfull)
  have hglobal := CycleSaturation.length_eq_card_of_neighbor_ncard_two hconn hdegree hc
  have hglobal' : p.length = m * L := by simpa [Vertex] using hglobal
  have hlocal : p.length = m * 2 := by simpa [Vertex] using hp.length_eq
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (hglobal'.symm.trans hlocal)

/-- A Hamiltonian column geometry can have a full outgoing H/D mask only
when the entire graph has two columns. -/
theorem length_two_of_full_crossing_masks {m L : ℕ} (hm : 3 ≤ m)
    (g : HamiltonianGeometry m L hm) (c : Fin (L - 1))
    (hfull : ∀ r : Fin m, g.val.2.1 c r = true ∧ g.val.2.2 c r = true) :
    L = 2 :=
  length_two_of_fullCrossingAt hm _ c g.property.1 g.property.2
    (fullCrossingAt_of_masks hm g.val c hfull)

/-- Consequently no full outgoing H/D cut is present in a geometry with
at least three columns. -/
theorem not_full_crossing_masks {m L : ℕ} (hm : 3 ≤ m) (hL : 3 ≤ L)
    (g : HamiltonianGeometry m L hm) (c : Fin (L - 1)) :
    ¬ (∀ r : Fin m, g.val.2.1 c r = true ∧ g.val.2.2 c r = true) := by
  intro hfull
  have h := length_two_of_full_crossing_masks hm g c hfull
  omega

end TriangularCutSaturation
