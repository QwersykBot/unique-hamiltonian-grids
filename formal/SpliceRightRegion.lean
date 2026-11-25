import SpliceStateFields
import ColumnTailSums

/-!
# Selected old edges strictly beyond the splice deletion

The only removed old edge lies in old column zero.  Thus old vertical
edges at a positive column are unchanged. Every old intercolumn edge is
unchanged as well. These physical-adjacency identities supply the tail
terms used in the assigned-prefix parity comparison.
-/

namespace TriangularCylinder.SpliceRightRegion

open SimpleGraph SplicePrefixCoordinates TriangularEdgeEncoding
open CylinderFrontier.EdgeReplacement ColumnTailSums

/-- Shifting a cut index shifts its lower physical column. -/
theorem lowerCol_shift {m a b : ℕ} (h : a + b - 1 = a + (b - 1))
    (c : Fin (b - 1)) (r : Fin m) :
    (r, lowerCol (shiftCol a h c)) = rightVertex a (r, lowerCol c) := by
  apply Prod.ext rfl
  apply Fin.ext
  rfl

/-- Shifting a cut index shifts its upper physical column. -/
theorem upperCol_shift {m a b : ℕ} (h : a + b - 1 = a + (b - 1))
    (c : Fin (b - 1)) (r : Fin m) :
    (r, upperCol (shiftCol a h c)) = rightVertex a (r, upperCol c) := by
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

/-- A positive old column cannot be an endpoint of the deleted old edge. -/
theorem right_adj_iff_of_pos_column (x y : Vertex m (j + 1 + k))
    (hx : 0 < x.2.val) :
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
    rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> exact Nat.lt_irrefl 0 hx

/-- Every vertical adjacency strictly beyond an old cut is preserved. -/
theorem right_vertical_adj_iff (c : Fin (j + 1 + k)) (hc : j < c.val)
    (t u : Fin m) :
    GJ.Adj (t, Fin.natAdd a c) (u, Fin.natAdd a c) ↔ GB.Adj (t, c) (u, c) := by
  exact right_adj_iff_of_pos_column hb GA GB GJ a₀ a₁ r s hsplice
    (t, c) (u, c) (Nat.lt_of_le_of_lt (Nat.zero_le j) hc)

/-- Every old intercolumn adjacency survives, expressed in shifted cut indices. -/
theorem right_intercolumn_adj_iff
    (h : a + (j + 1 + k) - 1 = a + (j + 1 + k - 1))
    (c : Fin (j + 1 + k - 1)) (t u : Fin m) :
    GJ.Adj (t, lowerCol (shiftCol a h c)) (u, upperCol (shiftCol a h c)) ↔
      GB.Adj (t, lowerCol c) (u, upperCol c) := by
  rw [lowerCol_shift, upperCol_shift]
  apply SpliceStateFields.right_adj_iff_of_col_ne hb GA GB GJ a₀ a₁ r s hsplice
  intro heq
  have hv := congrArg Fin.val heq
  change c.val = c.val + 1 at hv
  omega

end Replacement

#print axioms lowerCol_shift
#print axioms upperCol_shift
#print axioms right_adj_iff_of_pos_column
#print axioms right_vertical_adj_iff
#print axioms right_intercolumn_adj_iff

end TriangularCylinder.SpliceRightRegion
