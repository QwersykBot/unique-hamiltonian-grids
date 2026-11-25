import BoundaryState
import Mathlib.Data.Set.Card

/-!
# Physical outgoing neighbors of a complete boundary column

The suffix contribution at a boundary row is exactly its selected horizontal
and forward-diagonal cut edges. The ambient cylinder adjacency supplies all
locality and orientation restrictions; no extra separation premise is used.
The two endpoints are distinct, so their two mask indicators give the exact
neighbor cardinality. No connectivity or degree-two hypothesis is needed.
-/

namespace TriangularCylinder.ColumnCut

open SimpleGraph TriangularEdgeEncoding BoundaryState

/-- The first suffix column exists at every nonterminal cut. -/
def firstSuffixCol {k : ℕ} (hk : 1 ≤ k) : Fin k := ⟨0, by omega⟩

@[simp] theorem suffixVertex_boundary {m j k : ℕ} (r : Fin m) :
    suffixVertex j k (Sum.inr r) = (r, boundaryCol j k) := rfl

@[simp] theorem suffixVertex_first {m j k : ℕ} (hk : 1 ≤ k) (r : Fin m) :
    suffixVertex j k (Sum.inl (r, firstSuffixCol hk)) = (r, nextCol hk) := rfl

/-- Actual cylinder edges from the boundary into the suffix must land in its
first column, at the same row or its forward cyclic successor. -/
theorem suffixPart_boundary_geometry {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (r : Fin m) (x : Vertex m k)
    (h : (suffixPart j k H).Adj (Sum.inr r) (Sum.inl x)) :
    x.2 = firstSuffixCol hk ∧ (x.1 = r ∨ x.1 = rowSucc hm r) := by
  have hambient := hH h.1
  rcases hambient with hf | hb
  · rcases hf with ⟨hc, _⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
    · have hval := congrArg Fin.val hc
      change j = j + 1 + x.2.val at hval
      omega
    · have hzero : x.2.val = 0 := by
        change j + 1 = j + 1 + x.2.val at hc
        omega
      exact ⟨Fin.ext hzero, Or.inl hr.symm⟩
    · have hzero : x.2.val = 0 := by
        change j + 1 = j + 1 + x.2.val at hc
        omega
      exact ⟨Fin.ext hzero, Or.inr (Fin.ext hr)⟩
  · have hcols := forward_col_le hb
    change j + 1 + x.2.val ≤ j at hcols
    omega

/-- Exact selected-edge alternatives for every possible suffix neighbor. -/
theorem suffixPart_boundary_adj_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (r : Fin m) (x : Vertex m k ⊕ Fin m) :
    (suffixPart j k H).Adj (Sum.inr r) x ↔
      (x = Sum.inl (r, firstSuffixCol hk) ∧
        H.Adj (r, boundaryCol j k) (r, nextCol hk)) ∨
      (x = Sum.inl (rowSucc hm r, firstSuffixCol hk) ∧
        H.Adj (r, boundaryCol j k) (rowSucc hm r, nextCol hk)) := by
  constructor
  · intro h
    cases x with
    | inl x =>
      obtain ⟨hc, hr | hr⟩ := suffixPart_boundary_geometry hm hk hH r x h
      · have hx : x = (r, firstSuffixCol hk) := Prod.ext hr hc
        subst x
        exact Or.inl ⟨rfl, h.1⟩
      · have hx : x = (rowSucc hm r, firstSuffixCol hk) := Prod.ext hr hc
        subst x
        exact Or.inr ⟨rfl, h.1⟩
    | inr s => exact False.elim (suffixPart_no_boundary_edges H r s h)
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨h, (r, firstSuffixCol hk), Or.inr rfl⟩
    · exact ⟨h, (rowSucc hm r, firstSuffixCol hk), Or.inr rfl⟩

/-- The exact adjacency alternatives expressed by the existing physical masks. -/
theorem suffixPart_boundary_adj_iff_masks {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (r : Fin m) (x : Vertex m k ⊕ Fin m) :
    (suffixPart j k H).Adj (Sum.inr r) x ↔
      (x = Sum.inl (r, firstSuffixCol hk) ∧ (stateAt hm hk H).horizontal r = true) ∨
      (x = Sum.inl (rowSucc hm r, firstSuffixCol hk) ∧ (stateAt hm hk H).diagonal r = true) := by
  rw [suffixPart_boundary_adj_iff hm hk hH r x,
    stateAt_horizontal_iff hm hk H r, stateAt_diagonal_iff hm hk H r]

/-- The two outgoing physical edge types have distinct suffix endpoints. -/
theorem firstSuffix_horizontal_ne_diagonal {m k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (r : Fin m) :
    (Sum.inl (r, firstSuffixCol hk) : Vertex m k ⊕ Fin m) ≠
      Sum.inl (rowSucc hm r, firstSuffixCol hk) := by
  intro h
  exact nextRow_ne hm (nextRow_rowSucc hm r) (congrArg Prod.fst (Sum.inl.inj h))

/-- The actual neighbor set is the union of its two selected physical endpoints. -/
theorem suffixPart_boundary_neighborSet {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (r : Fin m) :
    (suffixPart j k H).neighborSet (Sum.inr r) =
      (if (stateAt hm hk H).horizontal r = true then
        {Sum.inl (r, firstSuffixCol hk)} else ∅) ∪
      (if (stateAt hm hk H).diagonal r = true then
        {Sum.inl (rowSucc hm r, firstSuffixCol hk)} else ∅) := by
  ext x
  rw [mem_neighborSet, suffixPart_boundary_adj_iff_masks hm hk hH r x]
  by_cases hh : (stateAt hm hk H).horizontal r = true <;>
    by_cases hd : (stateAt hm hk H).diagonal r = true <;> simp [hh, hd, or_comm]

/-- The suffix degree contribution is the sum of the two Boolean mask indicators. -/
theorem suffixPart_boundary_neighbor_ncard {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (r : Fin m) :
    ((suffixPart j k H).neighborSet (Sum.inr r)).ncard =
      (if (stateAt hm hk H).horizontal r = true then 1 else 0) +
      (if (stateAt hm hk H).diagonal r = true then 1 else 0) := by
  have hne := firstSuffix_horizontal_ne_diagonal hm hk r
  rw [suffixPart_boundary_neighborSet hm hk hH r]
  by_cases hh : (stateAt hm hk H).horizontal r = true <;>
    by_cases hd : (stateAt hm hk H).diagonal r = true <;> simp [hh, hd, hne, hne.symm]

/-- Equal outgoing masks give equal suffix degree contributions, even when the
two selected graphs occur at different prefix and suffix lengths. -/
theorem suffixPart_boundary_neighbor_ncard_eq_of_masks_eq
    {m j k j' k' : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (hk' : 1 ≤ k')
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    {H' : SimpleGraph (Vertex m (j' + 1 + k'))}
    (hH : H ≤ graph m (j + 1 + k) hm) (hH' : H' ≤ graph m (j' + 1 + k') hm)
    (hhor : (stateAt hm hk H).horizontal = (stateAt hm hk' H').horizontal)
    (hdiag : (stateAt hm hk H).diagonal = (stateAt hm hk' H').diagonal)
    (r : Fin m) :
    ((suffixPart j k H).neighborSet (Sum.inr r)).ncard =
      ((suffixPart j' k' H').neighborSet (Sum.inr r)).ncard := by
  rw [suffixPart_boundary_neighbor_ncard hm hk hH r,
    suffixPart_boundary_neighbor_ncard hm hk' hH' r, hhor, hdiag]

#print axioms suffixPart_boundary_geometry
#print axioms suffixPart_boundary_adj_iff
#print axioms suffixPart_boundary_adj_iff_masks
#print axioms firstSuffix_horizontal_ne_diagonal
#print axioms suffixPart_boundary_neighborSet
#print axioms suffixPart_boundary_neighbor_ncard
#print axioms suffixPart_boundary_neighbor_ncard_eq_of_masks_eq

end TriangularCylinder.ColumnCut
