import SpliceRightRegion
import BoundaryParity

/-!
# Equality of physical parity contributions strictly beyond an old cut

Only the frozen selectedGeometry and meridian weights are used. No new state
parity is defined. The two tail sums retain precisely the V and D last-row
contributions whose source column is strictly greater than the cut.
-/

namespace TriangularCylinder.SpliceTailWeights

open SimpleGraph TriangularEdgeEncoding BoundaryState BoundaryParity Transfer
open SplicePrefixCoordinates SpliceRightRegion CylinderFrontier.EdgeReplacement
open scoped BigOperators

theorem selectedGeometry_vertical_true_iff {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin L) (t : Fin m) :
    (selectedGeometry hm H).1 c t = true ↔ H.Adj (t, c) (rowSucc hm t, c) := by
  rw [selectedGeometry_vertical, verticalMask_iff]

theorem selectedGeometry_diagonal_true_iff {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin (L - 1)) (t : Fin m) :
    (selectedGeometry hm H).2.2 c t = true ↔
      H.Adj (t, lowerCol c) (rowSucc hm t, upperCol c) := by
  classical
  simp only [selectedGeometry, geometryOfIds, decide_eq_true_eq,
    mem_selectedPhysicalIds, toEdge, sourceVertex, targetVertex, SimpleGraph.mem_edgeSet]

private theorem sum_prefix_add_tail {L : ℕ} (f : Fin L → ZMod 2) (j : ℕ) :
    (∑ c : Fin L, if c.val ≤ j then f c else 0) +
        (∑ c : Fin L, if j < c.val then f c else 0) = ∑ c : Fin L, f c := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c.val ≤ j
  · simp only [hc, Nat.not_lt.mpr hc, if_true, if_false, add_zero]
  · simp only [hc, Nat.lt_of_not_ge hc, if_true, if_false, zero_add]

/-- The existing selected-ID sum splits into its source-filtered part and
the two strictly-beyond-cut physical last-row sums. -/
theorem selected_filter_add_tail {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (j : ℕ) :
    (∑ id ∈ (selectedPhysicalIds hm H).filter
        (fun id => (sourceVertex id).2.val ≤ j), meridianWeight hm (toEdge hm id)) +
      ((∑ c : Fin L, if j < c.val then
          (if (selectedGeometry hm H).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0) +
        (∑ c : Fin (L - 1), if j < c.val then
          (if (selectedGeometry hm H).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0)) =
      ∑ id ∈ selectedPhysicalIds hm H, meridianWeight hm (toEdge hm id) := by
  rw [← idsOfGeometry_selectedGeometry hm H,
    sum_idsOfGeometry_filter_le_meridian_eq_lastRow,
    sum_idsOfGeometry_meridian_eq_lastRow]
  simp only [Finset.sum_filter]
  have hV := sum_prefix_add_tail
    (fun c => if (selectedGeometry hm H).1 c (lastRow m hm) then (1 : ZMod 2) else 0) j
  have hD := sum_prefix_add_tail
    (fun c => if (selectedGeometry hm H).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) j
  calc
    _ = ((∑ c : Fin L, if c.val ≤ j then
            (if (selectedGeometry hm H).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0) +
          (∑ c : Fin L, if j < c.val then
            (if (selectedGeometry hm H).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0)) +
        ((∑ c : Fin (L - 1), if c.val ≤ j then
            (if (selectedGeometry hm H).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0) +
          (∑ c : Fin (L - 1), if j < c.val then
            (if (selectedGeometry hm H).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0)) := by
      ac_rfl
    _ = _ := congrArg₂ (· + ·) hV hD

section Replacement

variable {m a j k : ℕ} (hb : 2 ≤ j + 1 + k)
variable (GA : SimpleGraph (Vertex m a)) (GB : SimpleGraph (Vertex m (j + 1 + k)))
variable (GJ : SimpleGraph (Vertex m (a + (j + 1 + k))))
variable (a₀ a₁ : Vertex m a) (r s : Fin m)
variable (hsplice : GJ.comap (columnSumEquiv m a (j + 1 + k)) =
  replacementGraph GB GA
    (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb) a₀ a₁)

include hsplice

/-- Every V contribution strictly beyond the old cut is unchanged. -/
theorem vertical_tail_eq (hm : 3 ≤ m) :
    (∑ c : Fin (a + (j + 1 + k)), if a + j < c.val then
        (if (selectedGeometry hm GJ).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0) =
      ∑ c : Fin (j + 1 + k), if j < c.val then
        (if (selectedGeometry hm GB).1 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0 := by
  apply ColumnTailSums.sum_tail_shift a (j + 1 + k) j
  intro c hc
  have hflag : (selectedGeometry hm GJ).1 (Fin.natAdd a c) (lastRow m hm) =
      (selectedGeometry hm GB).1 c (lastRow m hm) := by
    rw [Bool.eq_iff_iff, selectedGeometry_vertical_true_iff, selectedGeometry_vertical_true_iff]
    exact right_vertical_adj_iff hb GA GB GJ a₀ a₁ r s hsplice c hc _ _
  rw [hflag]

/-- Every D contribution strictly beyond the old cut is unchanged. -/
theorem diagonal_tail_eq (hm : 3 ≤ m) :
    (∑ c : Fin (a + (j + 1 + k) - 1), if a + j < c.val then
        (if (selectedGeometry hm GJ).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0) =
      ∑ c : Fin (j + 1 + k - 1), if j < c.val then
        (if (selectedGeometry hm GB).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) else 0 := by
  have hwidth : a + (j + 1 + k) - 1 = a + (j + 1 + k - 1) := by omega
  apply ColumnTailSums.sum_tail_shift_of_eq a (j + 1 + k - 1) j hwidth
  intro c _
  have hflag : (selectedGeometry hm GJ).2.2 (ColumnTailSums.shiftCol a hwidth c) (lastRow m hm) =
      (selectedGeometry hm GB).2.2 c (lastRow m hm) := by
    rw [Bool.eq_iff_iff, selectedGeometry_diagonal_true_iff, selectedGeometry_diagonal_true_iff]
    exact right_intercolumn_adj_iff hb GA GB GJ a₀ a₁ r s hsplice hwidth c _ _
  rw [hflag]

end Replacement

#print axioms selectedGeometry_vertical_true_iff
#print axioms selectedGeometry_diagonal_true_iff
#print axioms selected_filter_add_tail
#print axioms vertical_tail_eq
#print axioms diagonal_tail_eq

end TriangularCylinder.SpliceTailWeights
