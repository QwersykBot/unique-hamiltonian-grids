import SpliceTailWeights
import StateWidthTransport
import BoundaryParityUpdates

/-!
# Assigned-prefix parity under the same concrete left splice

The whole-cycle parity difference and all strictly-beyond-cut physical
contributions determine the assigned-prefix parity difference. The tail
equality is proved from the exact replacement graph, and the total sums use
the existing trail-to-selected-ID theorem. No new parity convention is used.
-/

namespace TriangularCylinder.SpliceAssignedParity

open SimpleGraph TriangularEdgeEncoding BoundaryState BoundaryParity
open SplicePrefixCoordinates StateWidthTransport SpliceTailWeights
open CylinderFrontier.EdgeReplacement
open scoped BigOperators

/-- A selected replacement with a known total parity increment has that
same increment at every old prefix, including the cut at column zero. -/
theorem assignedParity_add_of_splice
    {m a j k : ℕ} (hm : 3 ≤ m) (hb : 2 ≤ j + 1 + k)
    (GA : SimpleGraph (Vertex m a))
    {v : Vertex m (j + 1 + k)} {w : Vertex m (a + (j + 1 + k))}
    (B : (graph m (j + 1 + k) hm).Walk v v)
    (J : (graph m (a + (j + 1 + k)) hm).Walk w w)
    (hB : B.IsTrail) (hJ : J.IsTrail)
    (a₀ a₁ : Vertex m a) (r s : Fin m)
    (hsplice : (fromEdgeSet J.edgeSet).comap (columnSumEquiv m a (j + 1 + k)) =
      replacementGraph (fromEdgeSet B.edgeSet) GA
        (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb) a₀ a₁)
    (delta : ZMod 2) (hparity : typeParity hm J = delta + typeParity hm B) :
    assignedParity hm ((fromEdgeSet J.edgeSet).comap (fullWidthEquiv m a j k)) =
      assignedParity hm (fromEdgeSet B.edgeSet) + delta := by
  let GB := fromEdgeSet B.edgeSet
  let GJ := fromEdgeSet J.edgeSet
  let tVB : ZMod 2 := ∑ c : Fin (j + 1 + k), if j < c.val then
    (if (selectedGeometry hm GB).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0
  let tDB : ZMod 2 := ∑ c : Fin (j + 1 + k - 1), if j < c.val then
    (if (selectedGeometry hm GB).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0
  let tVJ : ZMod 2 := ∑ c : Fin (a + (j + 1 + k)), if a + j < c.val then
    (if (selectedGeometry hm GJ).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0
  let tDJ : ZMod 2 := ∑ c : Fin (a + (j + 1 + k) - 1), if a + j < c.val then
    (if (selectedGeometry hm GJ).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0
  have hV : tVJ = tVB := vertical_tail_eq hb GA GB GJ a₀ a₁ r s hsplice hm
  have hD : tDJ = tDB := diagonal_tail_eq hb GA GB GJ a₀ a₁ r s hsplice hm
  have hsumJ : assignedParity hm (GJ.comap (fullWidthEquiv m a j k)) + (tVJ + tDJ) =
      ∑ id ∈ selectedPhysicalIds hm GJ, meridianWeight hm (toEdge hm id) := by
    rw [fullWidthEquiv_eq_widthEquiv m a j k, assignedParity_comap_widthEquiv]
    exact selected_filter_add_tail hm GJ (a + j)
  have hsumB : assignedParity hm GB + (tVB + tDB) =
      ∑ id ∈ selectedPhysicalIds hm GB, meridianWeight hm (toEdge hm id) := by
    unfold assignedParity
    rw [assignedIds_eq_filter]
    exact selected_filter_add_tail hm GB j
  have htotalJ : assignedParity hm (GJ.comap (fullWidthEquiv m a j k)) + (tVB + tDB) =
      typeParity hm J := by
    rw [← hV, ← hD, typeParity_eq_selectedPhysicalIds hm J hJ]
    exact hsumJ
  have htotalB : assignedParity hm GB + (tVB + tDB) = typeParity hm B := by
    rw [typeParity_eq_selectedPhysicalIds hm B hB]
    exact hsumB
  apply add_right_cancel (b := tVB + tDB)
  calc
    _ = typeParity hm J := htotalJ
    _ = delta + typeParity hm B := hparity
    _ = (assignedParity hm GB + delta) + (tVB + tDB) := by
      rw [← htotalB]
      ac_rfl

/-- The same statement for the parity field of the frozen state encoder. -/
theorem stateAt_parity_add_of_splice
    {m a j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (GA : SimpleGraph (Vertex m a))
    {v : Vertex m (j + 1 + k)} {w : Vertex m (a + (j + 1 + k))}
    (B : (graph m (j + 1 + k) hm).Walk v v)
    (J : (graph m (a + (j + 1 + k)) hm).Walk w w)
    (hB : B.IsTrail) (hJ : J.IsTrail)
    (a₀ a₁ : Vertex m a) (r s : Fin m)
    (hsplice : (fromEdgeSet J.edgeSet).comap (columnSumEquiv m a (j + 1 + k)) =
      replacementGraph (fromEdgeSet B.edgeSet) GA
        (r, firstCol (j + 1 + k) (by omega))
        (s, firstCol (j + 1 + k) (by omega)) a₀ a₁)
    (delta : ZMod 2) (hparity : typeParity hm J = delta + typeParity hm B) :
    (stateAt hm hk ((fromEdgeSet J.edgeSet).comap (fullWidthEquiv m a j k))).parity =
      (stateAt hm hk (fromEdgeSet B.edgeSet)).parity + delta := by
  exact assignedParity_add_of_splice hm (by omega) GA B J hB hJ a₀ a₁ r s hsplice delta hparity

#print axioms assignedParity_add_of_splice
#print axioms stateAt_parity_add_of_splice

end TriangularCylinder.SpliceAssignedParity
