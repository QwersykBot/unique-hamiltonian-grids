import ColumnCut
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coordinates for a prefix after a left cylinder is spliced on

The source is all vertices of the left block, together with the old prefix
interior and its complete boundary column. The target is the canonical
joined prefix interior and the same boundary rows. The explicit width
equivalence only reassociates natural-number widths and preserves every
row and numeric column coordinate.

All definitions permit empty interiors, including j = 0. This file proves
coordinate identities and injectivity only, not selected-edge, reachability,
Hamiltonian, parity, or counting statements.
-/

namespace TriangularCylinder.SplicePrefixCoordinates

/-- The full two-block vertex bijection, with the existing physical embeddings. -/
def columnSumEquiv (m a b : ℕ) : Vertex m a ⊕ Vertex m b ≃ Vertex m (a + b) :=
  (Equiv.prodSumDistrib (Fin m) (Fin a) (Fin b)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin m)) finSumFinEquiv)

@[simp] theorem columnSumEquiv_left {m a b : ℕ} (x : Vertex m a) :
    columnSumEquiv m a b (Sum.inl x) = leftVertex b x := rfl

@[simp] theorem columnSumEquiv_right {m a b : ℕ} (x : Vertex m b) :
    columnSumEquiv m a b (Sum.inr x) = rightVertex a x := rfl

@[simp] theorem columnSumEquiv_row {m a b : ℕ} (x : Vertex m a ⊕ Vertex m b) :
    (columnSumEquiv m a b x).1 = Sum.elim Prod.fst Prod.fst x := by
  cases x <;> rfl

abbrev SourcePrefix (m a j : ℕ) := Vertex m a ⊕ (Vertex m j ⊕ Fin m)
abbrev TargetPrefix (m a j : ℕ) := Vertex m (a + j) ⊕ Fin m

/-- Put both interiors into their original adjacent column blocks. -/
def toPrefix {m a j : ℕ} : SourcePrefix m a j → TargetPrefix m a j
  | Sum.inl x => Sum.inl (leftVertex j x)
  | Sum.inr (Sum.inl x) => Sum.inl (rightVertex a x)
  | Sum.inr (Sum.inr r) => Sum.inr r

/-- Split the joined interior at the left block's width; preserve boundary rows. -/
def ofPrefix {m a j : ℕ} : TargetPrefix m a j → SourcePrefix m a j
  | Sum.inl x =>
      if hx : x.2.val < a then
        Sum.inl (x.1, ⟨x.2.val, hx⟩)
      else
        Sum.inr (Sum.inl (x.1, ⟨x.2.val - a, by have := x.2.isLt; omega⟩))
  | Sum.inr r => Sum.inr (Sum.inr r)

theorem ofPrefix_toPrefix {m a j : ℕ} (x : SourcePrefix m a j) :
    ofPrefix (toPrefix x) = x := by
  rcases x with x | x | r
  · simp [toPrefix, ofPrefix, leftVertex, x.2.isLt]
  · have hx : ¬ a + x.2.val < a := by omega
    simp [toPrefix, ofPrefix, rightVertex, hx]
  · rfl

theorem toPrefix_ofPrefix {m a j : ℕ} (x : TargetPrefix m a j) :
    toPrefix (ofPrefix x) = x := by
  cases x with
  | inl x =>
      dsimp only [ofPrefix]
      split_ifs with hx
      · apply congrArg Sum.inl
        apply Prod.ext
        · rfl
        · apply Fin.ext
          rfl
      · apply congrArg Sum.inl
        apply Prod.ext
        · rfl
        · apply Fin.ext
          change a + (x.2.val - a) = x.2.val
          omega
  | inr r => rfl

/-- A coordinate bijection that keeps the old boundary row labels unchanged. -/
def prefixEquiv (m a j : ℕ) : SourcePrefix m a j ≃ TargetPrefix m a j where
  toFun := toPrefix
  invFun := ofPrefix
  left_inv := ofPrefix_toPrefix
  right_inv := toPrefix_ofPrefix

@[simp] theorem prefixEquiv_left {m a j : ℕ} (x : Vertex m a) :
    prefixEquiv m a j (Sum.inl x) = Sum.inl (leftVertex j x) := rfl

@[simp] theorem prefixEquiv_old_interior {m a j : ℕ} (x : Vertex m j) :
    prefixEquiv m a j (Sum.inr (Sum.inl x)) = Sum.inl (rightVertex a x) := rfl

@[simp] theorem prefixEquiv_boundary {m a j : ℕ} (r : Fin m) :
    prefixEquiv m a j (Sum.inr (Sum.inr r)) = Sum.inr r := rfl

/-- Reassociate the total widths without changing any coordinate value. -/
def fullWidthEquiv (m a j k : ℕ) :
    Vertex m ((a + j) + 1 + k) ≃ Vertex m (a + (j + 1 + k)) where
  toFun x := (x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩)
  invFun x := (x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩)
  left_inv x := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl

@[simp] theorem fullWidthEquiv_row {m a j k : ℕ} (x : Vertex m ((a + j) + 1 + k)) :
    (fullWidthEquiv m a j k x).1 = x.1 := rfl

@[simp] theorem fullWidthEquiv_col {m a j k : ℕ} (x : Vertex m ((a + j) + 1 + k)) :
    (fullWidthEquiv m a j k x).2.val = x.2.val := rfl

@[simp] theorem fullWidthEquiv_symm_row {m a j k : ℕ} (x : Vertex m (a + (j + 1 + k))) :
    ((fullWidthEquiv m a j k).symm x).1 = x.1 := rfl

@[simp] theorem fullWidthEquiv_symm_col {m a j k : ℕ} (x : Vertex m (a + (j + 1 + k))) :
    ((fullWidthEquiv m a j k).symm x).2.val = x.2.val := rfl

/-- Map the left block and old prefix directly into the actual joined cylinder. -/
def physicalPrefix {m : ℕ} (a j k : ℕ) : SourcePrefix m a j → Vertex m (a + (j + 1 + k))
  | Sum.inl x => leftVertex (j + 1 + k) x
  | Sum.inr x => rightVertex a (ColumnCut.prefixVertex j k x)

@[simp] theorem physicalPrefix_left {m a j k : ℕ} (x : Vertex m a) :
    physicalPrefix a j k (Sum.inl x) = leftVertex (j + 1 + k) x := rfl

@[simp] theorem physicalPrefix_old {m a j k : ℕ} (x : Vertex m j ⊕ Fin m) :
    physicalPrefix a j k (Sum.inr x) = rightVertex a (ColumnCut.prefixVertex j k x) := rfl

/-- The canonical prefix map and direct physical splice map agree exactly. -/
theorem fullWidth_prefixVertex_eq_physicalPrefix {m a j k : ℕ} (x : SourcePrefix m a j) :
    fullWidthEquiv m a j k (ColumnCut.prefixVertex (a + j) k (prefixEquiv m a j x)) =
      physicalPrefix a j k x := by
  rcases x with x | x | r <;> apply Prod.ext
  · rfl
  · apply Fin.ext
    rfl
  · rfl
  · apply Fin.ext
    rfl
  · rfl
  · apply Fin.ext
    rfl

/-- The direct physical prefix map cannot identify any source vertices. -/
theorem physicalPrefix_injective {m a j k : ℕ} :
    Function.Injective (physicalPrefix (m := m) a j k) := by
  intro x y hxy
  have hcanon : ColumnCut.prefixVertex (a + j) k (prefixEquiv m a j x) =
      ColumnCut.prefixVertex (a + j) k (prefixEquiv m a j y) := by
    apply (fullWidthEquiv m a j k).injective
    simpa only [fullWidth_prefixVertex_eq_physicalPrefix] using hxy
  apply (prefixEquiv m a j).injective
  apply (CylinderFrontier.prefixEmbedding (Vertex m (a + j)) (Fin m) (Vertex m k)).injective
  exact (ColumnCut.vertexEquiv m (a + j) k).injective hcanon

/-- The first old column is a boundary column exactly when its old interior is empty. -/
def firstPrefixVertex {m : ℕ} : (j : ℕ) → Fin m → Vertex m j ⊕ Fin m
  | 0, r => Sum.inr r
  | j + 1, r => Sum.inl (r, ⟨0, Nat.succ_pos j⟩)

@[simp] theorem prefixVertex_firstPrefixVertex_row {m j k : ℕ} (r : Fin m) :
    (ColumnCut.prefixVertex j k (firstPrefixVertex j r)).1 = r := by
  cases j <;> rfl

@[simp] theorem prefixVertex_firstPrefixVertex_col {m j k : ℕ} (r : Fin m) :
    (ColumnCut.prefixVertex j k (firstPrefixVertex j r)).2.val = 0 := by
  cases j <;> rfl

/-- The chosen first-column vertex has the expected original physical coordinate,
including the old-prefix case j = 0. -/
theorem prefixVertex_firstPrefixVertex {m j k : ℕ} (h : 2 ≤ j + 1 + k) (r : Fin m) :
    ColumnCut.prefixVertex j k (firstPrefixVertex j r) = (r, firstCol (j + 1 + k) h) := by
  cases j <;> apply Prod.ext
  · rfl
  · apply Fin.ext
    rfl
  · rfl
  · apply Fin.ext
    rfl

#print axioms columnSumEquiv
#print axioms columnSumEquiv_left
#print axioms columnSumEquiv_right
#print axioms ofPrefix_toPrefix
#print axioms toPrefix_ofPrefix
#print axioms prefixEquiv_boundary
#print axioms fullWidth_prefixVertex_eq_physicalPrefix
#print axioms physicalPrefix_injective
#print axioms prefixVertex_firstPrefixVertex

end TriangularCylinder.SplicePrefixCoordinates
