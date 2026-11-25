import TriangularCylinder
import FrontierAttachment

/-!
# Decomposing a selected cylinder graph at a column

The complete last processed column is the shared boundary. Earlier columns
form the prefix interior, and later columns form the suffix interior. The
prefix owns every edge within the boundary column; the suffix owns none.
Column locality is derived from the actual triangular-cylinder adjacency.
No frontier state, transition, or transfer weight is defined here.
-/

namespace TriangularCylinder.ColumnCut

open SimpleGraph

abbrev CutVertex (m j k : ℕ) := Vertex m j ⊕ (Fin m ⊕ Vertex m k)

/-- Place the prefix, boundary column, and suffix into their original columns. -/
def toVertex {m j k : ℕ} : CutVertex m j k → Vertex m (j + 1 + k)
  | Sum.inl x => (x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩)
  | Sum.inr (Sum.inl r) => (r, ⟨j, by omega⟩)
  | Sum.inr (Sum.inr x) => (x.1, ⟨j + 1 + x.2.val, by have := x.2.isLt; omega⟩)

/-- Recover the unique region by comparing the column number with the cut. -/
def ofVertex {m j k : ℕ} (x : Vertex m (j + 1 + k)) : CutVertex m j k :=
  if hi : x.2.val < j then
    Sum.inl (x.1, ⟨x.2.val, hi⟩)
  else if hb : x.2.val = j then
    Sum.inr (Sum.inl x.1)
  else
    Sum.inr (Sum.inr (x.1, ⟨x.2.val - (j + 1), by have := x.2.isLt; omega⟩))

theorem ofVertex_toVertex {m j k : ℕ} (x : CutVertex m j k) :
    ofVertex (toVertex x) = x := by
  rcases x with x | r | x
  · simp [toVertex, ofVertex, x.2.isLt]
  · simp [toVertex, ofVertex]
  · have hi : ¬ j + 1 + x.2.val < j := by omega
    have hb : ¬ j + 1 + x.2.val = j := by omega
    simp [toVertex, ofVertex, hi, hb]

theorem toVertex_ofVertex {m j k : ℕ} (x : Vertex m (j + 1 + k)) :
    toVertex (ofVertex x) = x := by
  unfold ofVertex
  split_ifs with hi hb
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      exact hb.symm
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      change j + 1 + (x.2.val - (j + 1)) = x.2.val
      omega

/-- The canonical, explicitly invertible column-cut bijection. -/
def vertexEquiv (m j k : ℕ) : CutVertex m j k ≃ Vertex m (j + 1 + k) where
  toFun := toVertex
  invFun := ofVertex
  left_inv := ofVertex_toVertex
  right_inv := toVertex_ofVertex

@[simp] theorem vertexEquiv_row {m j k : ℕ} (x : CutVertex m j k) :
    (vertexEquiv m j k x).1 = Sum.elim Prod.fst (Sum.elim id Prod.fst) x := by
  rcases x with x | r | x <;> rfl

def prefixVertex {m : ℕ} (j k : ℕ) (x : Vertex m j ⊕ Fin m) :
    Vertex m (j + 1 + k) :=
  vertexEquiv m j k (CylinderFrontier.prefixEmbedding (Vertex m j) (Fin m) (Vertex m k) x)

def suffixVertex {m : ℕ} (j k : ℕ) (x : Vertex m k ⊕ Fin m) :
    Vertex m (j + 1 + k) :=
  vertexEquiv m j k (CylinderFrontier.suffixEmbedding (Vertex m j) (Fin m) (Vertex m k) x)

/-- The prefix is the full restriction to all processed columns. -/
def prefixPart {m : ℕ} (j k : ℕ) (H : SimpleGraph (Vertex m (j + 1 + k))) :
    SimpleGraph (Vertex m j ⊕ Fin m) :=
  H.comap (prefixVertex j k)

/-- The suffix restriction excludes every boundary-to-boundary edge. -/
def suffixPart {m : ℕ} (j k : ℕ) (H : SimpleGraph (Vertex m (j + 1 + k))) :
    SimpleGraph (Vertex m k ⊕ Fin m) where
  Adj x y := H.Adj (suffixVertex j k x) (suffixVertex j k y) ∧
    ∃ o : Vertex m k, x = Sum.inl o ∨ y = Sum.inl o
  symm _ _ h := by
    obtain ⟨hxy, o, ho⟩ := h
    exact ⟨hxy.symm, o, ho.symm⟩
  loopless x h := H.loopless _ h.1

@[simp] theorem suffixPart_no_boundary_edges {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r s : Fin m) :
    ¬ (suffixPart j k H).Adj (Sum.inr r) (Sum.inr s) := by
  rintro ⟨_, o, h | h⟩ <;> cases h

@[simp] theorem prefixPart_boundary_adj {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r s : Fin m) :
    (prefixPart j k H).Adj (Sum.inr r) (Sum.inr s) ↔
      H.Adj (vertexEquiv m j k (Sum.inr (Sum.inl r)))
        (vertexEquiv m j k (Sum.inr (Sum.inl s))) := Iff.rfl

/-- Every actual triangular-cylinder edge changes its column by at most one. -/
theorem adj_column_distance_le_one {m L : ℕ} (hm : 3 ≤ m)
    {x y : Vertex m L} (h : (graph m L hm).Adj x y) :
    x.2.val ≤ y.2.val + 1 ∧ y.2.val ≤ x.2.val + 1 := by
  rcases h with h | h
  · rcases h with ⟨hc, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · have hv := congrArg Fin.val hc
      constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
  · rcases h with ⟨hc, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · have hv := congrArg Fin.val hc
      constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega

/-- The intervening boundary column prevents every selected prefix-interior
to suffix-interior edge. This follows from the actual ambient edge families. -/
theorem no_interior_suffix_edge {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (x : Vertex m j) (y : Vertex m k) :
    ¬ H.Adj (vertexEquiv m j k (Sum.inl x))
      (vertexEquiv m j k (Sum.inr (Sum.inr y))) := by
  intro h
  have hd := adj_column_distance_le_one hm (hH h)
  change x.2.val ≤ (j + 1 + y.2.val) + 1 ∧
    j + 1 + y.2.val ≤ x.2.val + 1 at hd
  have hx := x.2.isLt
  omega

/-- The canonical glued restrictions recover exactly the entire selected graph
under the column-cut bijection. -/
theorem glue_parts_eq_comap {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) :
    CylinderFrontier.glue (prefixPart j k H) (suffixPart j k H) =
      H.comap (vertexEquiv m j k) := by
  have hsep := no_interior_suffix_edge hm hH
  have hsep' (y : Vertex m k) (x : Vertex m j) :
      ¬ H.Adj (vertexEquiv m j k (Sum.inr (Sum.inr y)))
        (vertexEquiv m j k (Sum.inl x)) := fun h => hsep x y h.symm
  ext x y
  rcases x with x | r | x <;> rcases y with y | s | y <;>
    simp [CylinderFrontier.glue, SimpleGraph.map_adj, Sum.exists,
      prefixPart, suffixPart, prefixVertex, suffixVertex,
      CylinderFrontier.prefixEmbedding, CylinderFrontier.suffixEmbedding, hsep, hsep']
  · intro _
    exact ⟨y.1, y.2, rfl⟩
  · intro _
    exact ⟨x.1, x.2, rfl⟩
  · intro _
    exact ⟨x.1, x.2, Or.inl rfl⟩

/-- The decomposition is an actual graph isomorphism, with the canonical
row-preserving vertex bijection. -/
def glueIso {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) :
    CylinderFrontier.glue (prefixPart j k H) (suffixPart j k H) ≃g H where
  toEquiv := vertexEquiv m j k
  map_rel_iff' := by
    intro x y
    rw [glue_parts_eq_comap hm hH]
    rfl

theorem glue_parts_connected {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (hconn : H.Connected) :
    (CylinderFrontier.glue (prefixPart j k H) (suffixPart j k H)).Connected :=
  hconn.map (glueIso hm hH).symm.toHom (glueIso hm hH).symm.toEquiv.surjective

/-- Connected selected graphs force attachment in the actual prefix restriction. -/
theorem prefixPart_touchesBoundary {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (hconn : H.Connected) :
    CylinderFrontier.TouchesBoundary (prefixPart j k H) :=
  CylinderFrontier.touchesBoundary_of_glue_connected_of_nonempty_boundary
    (prefixPart j k H) (suffixPart j k H) (glue_parts_connected hm hH hconn)
    ⟨⟨0, by omega⟩⟩

theorem both_parts_touchBoundary {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (hconn : H.Connected) :
    CylinderFrontier.TouchesBoundary (prefixPart j k H) ∧
      CylinderFrontier.TouchesBoundary (suffixPart j k H) :=
  CylinderFrontier.both_touchBoundary_of_glue_connected
    (prefixPart j k H) (suffixPart j k H) (glue_parts_connected hm hH hconn)
    ⟨⟨0, by omega⟩⟩

#print axioms ofVertex_toVertex
#print axioms toVertex_ofVertex
#print axioms vertexEquiv_row
#print axioms suffixPart_no_boundary_edges
#print axioms prefixPart_boundary_adj
#print axioms adj_column_distance_le_one
#print axioms no_interior_suffix_edge
#print axioms glue_parts_eq_comap
#print axioms glue_parts_connected
#print axioms prefixPart_touchesBoundary
#print axioms both_parts_touchBoundary

end TriangularCylinder.ColumnCut
