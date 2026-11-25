import CoreStateFlip
import SpliceCutTransport
import CycleWidthTransport

/-!
# The same left splice at every indexed old cut

An equal-width wrapper allows the same old and joined cycles to be used at
all their old cuts. The shifted fixed-width encoder then gives the full
flipped state. Old positive-column vertical masks are preserved as data.
-/

namespace TriangularCylinder.SpliceIndexedState

open SimpleGraph BoundaryState Transfer SplicePrefixCoordinates
open SpliceCutTransport CylinderFrontier.EdgeReplacement

/-- The full same-splice equality is independent of how the old width is
presented as a prefix, boundary column and suffix. -/
theorem stateAt_flip_of_splice_width
    {m a b j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (hwidth : j + 1 + k = b)
    (GA : SimpleGraph (Vertex m a))
    {v : Vertex m b} {w : Vertex m (a + b)}
    (B : (graph m b hm).Walk v v) (J : (graph m (a + b) hm).Walk w w)
    (hB : B.IsTrail) (hJ : J.IsTrail)
    (a₀ a₁ : Vertex m a) (r s : Fin m) (hGA : GA.Connected)
    (hxy : (fromEdgeSet B.edgeSet).Adj
      (r, firstCol b (by omega)) (s, firstCol b (by omega)))
    (hsplice : (fromEdgeSet J.edgeSet).comap (columnSumEquiv m a b) =
      replacementGraph (fromEdgeSet B.edgeSet) GA
        (r, firstCol b (by omega)) (s, firstCol b (by omega)) a₀ a₁)
    (hparity : typeParity hm J = 1 + typeParity hm B) :
    stateAt (j := a + j) hm hk
        ((fromEdgeSet J.edgeSet).comap (widthEquiv (by omega : (a + j) + 1 + k = a + b))) =
      RawBoundaryState.flip (stateAt hm hk
        ((fromEdgeSet B.edgeSet).comap (widthEquiv hwidth))) := by
  subst b
  simp only [widthEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id]
  rw [← StateWidthTransport.fullWidthEquiv_eq_widthEquiv m a j k]
  exact stateAt_flip_of_splice hm hk GA B J hB hJ a₀ a₁ r s hGA hxy hsplice hparity

/-- Every old indexed cut of the same pair of cycles has the flipped state
after the fixed-width presentation is shifted by the inserted width. -/
theorem cutState_flip_of_splice
    {m a n : ℕ} (hm : 3 ≤ m) (GA : SimpleGraph (Vertex m a))
    {v : Vertex m (n + 2)} {w : Vertex m (a + (n + 2))}
    (B : (graph m (n + 2) hm).Walk v v)
    (J : (graph m (a + (n + 2)) hm).Walk w w)
    (hB : B.IsTrail) (hJ : J.IsTrail)
    (a₀ a₁ : Vertex m a) (r s : Fin m) (hGA : GA.Connected)
    (hxy : (fromEdgeSet B.edgeSet).Adj
      (r, firstCol (n + 2) (by omega)) (s, firstCol (n + 2) (by omega)))
    (hsplice : (fromEdgeSet J.edgeSet).comap (columnSumEquiv m a (n + 2)) =
      replacementGraph (fromEdgeSet B.edgeSet) GA
        (r, firstCol (n + 2) (by omega)) (s, firstCol (n + 2) (by omega)) a₀ a₁)
    (hparity : typeParity hm J = 1 + typeParity hm B) (c : Fin (n + 1)) :
    cutState hm ((fromEdgeSet J.edgeSet).comap
        (widthEquiv (by omega : (a + n) + 2 = a + (n + 2)))) (shiftCut a c) =
      RawBoundaryState.flip (cutState hm (fromEdgeSet B.edgeSet) c) := by
  rw [cutState_shiftCut_eq_stateAt, cutState_eq_stateAt]
  exact stateAt_flip_of_splice_width hm (cutTail_pos c) (cutWidth_eq c)
    GA B J hB hJ a₀ a₁ r s hGA hxy hsplice hparity

/-- The new local/terminal column masks retain the same physical V choices.
Only old column zero is excluded because its chosen splice edge is removed. -/
theorem verticalMask_shift_of_splice
    {m a n : ℕ} (hm : 3 ≤ m)
    (GA : SimpleGraph (Vertex m a)) (GB : SimpleGraph (Vertex m (n + 2)))
    (GJ : SimpleGraph (Vertex m (a + (n + 2))))
    (a₀ a₁ : Vertex m a) (r s : Fin m)
    (hsplice : GJ.comap (columnSumEquiv m a (n + 2)) =
      replacementGraph GB GA
        (r, firstCol (n + 2) (by omega)) (s, firstCol (n + 2) (by omega)) a₀ a₁)
    (c : Fin (n + 2)) (hc : 0 < c.val) :
    verticalMask hm (GJ.comap (widthEquiv (by omega : (a + n) + 2 = a + (n + 2))))
        (ColumnTailSums.shiftCol a (by omega : (a + n) + 2 = a + (n + 2)) c) =
      verticalMask hm GB c := by
  funext t
  rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
  simp only [comap_adj, widthEquiv_shiftCol]
  exact SpliceRightRegion.right_adj_iff_of_pos_column (j := n + 1) (k := 0)
    (by omega) GA GB GJ a₀ a₁ r s hsplice
    (t, c) (TriangularEdgeEncoding.rowSucc hm t, c) hc

#print axioms stateAt_flip_of_splice_width
#print axioms cutState_flip_of_splice
#print axioms verticalMask_shift_of_splice

end TriangularCylinder.SpliceIndexedState
