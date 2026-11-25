import SplicePrefixReachability
import BoundaryState

/-!
# The non-parity state fields under a left cylinder splice

The deleted old edge is vertical in its first column. Consequently no old
edge joining different columns is altered. The shifted outgoing horizontal
and diagonal masks therefore agree at every old cut, including cut zero.
The frozen reachability theorem supplies equality of the boundary relation.
Assigned-prefix parity is a separate obligation.
-/

namespace TriangularCylinder.SpliceStateFields

open SimpleGraph BoundaryState SplicePrefixCoordinates
open CylinderFrontier.EdgeReplacement SplicePrefixReachability

theorem fullWidth_boundaryCol {m a j k : ℕ} (r : Fin m) :
    fullWidthEquiv m a j k (r, boundaryCol (a + j) k) =
      rightVertex a (r, boundaryCol j k) := by
  apply Prod.ext rfl
  apply Fin.ext
  rfl

theorem fullWidth_nextCol {m a j k : ℕ} (hk : 1 ≤ k) (r : Fin m) :
    fullWidthEquiv m a j k (r, nextCol (j := a + j) hk) =
      rightVertex a (r, nextCol (j := j) hk) := by
  apply Prod.ext rfl
  apply Fin.ext
  rfl

section Replacement

variable {m a j k : ℕ} (hb : 2 ≤ j + 1 + k)
variable (GA : SimpleGraph (Vertex m a)) (GB : SimpleGraph (Vertex m (j + 1 + k)))
variable (GJ : SimpleGraph (Vertex m (a + (j + 1 + k))))
variable (a₀ a₁ : Vertex m a) (r s : Fin m)
variable (hsplice : GJ.comap (columnSumEquiv m a (j + 1 + k)) =
  replacementGraph GB GA
    (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb) a₀ a₁)

include hsplice

/-- Every old adjacency between different columns is preserved by the splice. -/
theorem right_adj_iff_of_col_ne (x y : Vertex m (j + 1 + k)) (hcol : x.2 ≠ y.2) :
    GJ.Adj (rightVertex a x) (rightVertex a y) ↔ GB.Adj x y := by
  change (GJ.comap (columnSumEquiv m a (j + 1 + k))).Adj
    (Sum.inr x) (Sum.inr y) ↔ _
  rw [hsplice]
  change (GB.Adj x y ∧ ¬((x = (r, firstCol (j + 1 + k) hb) ∧
      y = (s, firstCol (j + 1 + k) hb)) ∨
    (x = (s, firstCol (j + 1 + k) hb) ∧
      y = (r, firstCol (j + 1 + k) hb)))) ↔ GB.Adj x y
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hcol rfl

/-- The outgoing horizontal mask is unchanged after shifting the old cut. -/
theorem stateAt_horizontal_eq (hm : 3 ≤ m) (hk : 1 ≤ k) :
    (stateAt hm hk (GJ.comap (fullWidthEquiv m a j k))).horizontal =
      (stateAt hm hk GB).horizontal := by
  funext t
  rw [Bool.eq_iff_iff, stateAt_horizontal_iff, stateAt_horizontal_iff]
  simp only [comap_adj, fullWidth_boundaryCol, fullWidth_nextCol]
  apply right_adj_iff_of_col_ne hb GA GB GJ a₀ a₁ r s hsplice
  intro h
  have hv := congrArg Fin.val h
  change j = j + 1 at hv
  omega

/-- The consistently oriented outgoing diagonal mask is unchanged. -/
theorem stateAt_diagonal_eq (hm : 3 ≤ m) (hk : 1 ≤ k) :
    (stateAt hm hk (GJ.comap (fullWidthEquiv m a j k))).diagonal =
      (stateAt hm hk GB).diagonal := by
  funext t
  rw [Bool.eq_iff_iff, stateAt_diagonal_iff, stateAt_diagonal_iff]
  simp only [comap_adj, fullWidth_boundaryCol, fullWidth_nextCol]
  apply right_adj_iff_of_col_ne hb GA GB GJ a₀ a₁ r s hsplice
  intro h
  have hv := congrArg Fin.val h
  change j = j + 1 at hv
  omega

/-- A connected inserted graph and a selected removed edge preserve the
actual boundary-reachability Boolean matrix. -/
theorem stateAt_reach_eq (hm : 3 ≤ m) (hk : 1 ≤ k) (hA : GA.Connected)
    (hxy : GB.Adj (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb)) :
    (stateAt hm hk (GJ.comap (fullWidthEquiv m a j k))).reach =
      (stateAt hm hk GB).reach := by
  funext t u
  rw [Bool.eq_iff_iff, stateAt_reach_iff, stateAt_reach_iff]
  change (joinedPrefix GJ).Reachable (Sum.inr t) (Sum.inr u) ↔ _
  simpa only [prefixEquiv_boundary] using
    old_prefix_reachable_iff_of_comap hb GA GB GJ a₀ a₁ r s hA hxy hsplice
      (Sum.inr t) (Sum.inr u)

end Replacement

#print axioms fullWidth_boundaryCol
#print axioms fullWidth_nextCol
#print axioms right_adj_iff_of_col_ne
#print axioms stateAt_horizontal_eq
#print axioms stateAt_diagonal_eq
#print axioms stateAt_reach_eq

end TriangularCylinder.SpliceStateFields
