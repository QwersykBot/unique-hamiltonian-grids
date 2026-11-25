import ColumnGeometry
import MeridianClassifier
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
# Exact additive charging of column masks

All mask families are allowed. These identities charge each selected physical
edge once, with no degree, connectedness, frontier, or Hamiltonian premise.
The finite sums include the empty ranges at zero and one column.
-/

namespace TriangularEdgeEncoding

open TriangularCylinder
open scoped BigOperators

variable {m L : ℕ} {W : Type*} [AddCommMonoid W]

/-- Injectivity of physical endpoint pairs prevents any weight from being
lost when the selected identifier finset is mapped to concrete graph edges. -/
theorem sum_realizedEdges_eq_selectedIds (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (w : Sym2 (Vertex m L) → W) :
    (∑ e ∈ realizedEdges hm g, w e) =
      ∑ id ∈ idsOfGeometry g, w (toEdge hm id) := by
  unfold realizedEdges
  exact Finset.sum_image (fun a _ b _ h => toEdge_injective hm h)

/-- A selected-ID sum is a Boolean-masked sum over all physical IDs. -/
theorem sum_idsOfGeometry_eq_flagSum (g : ColumnGeometry m L)
    (f : EdgeId m L → W) :
    (∑ id ∈ idsOfGeometry g, f id) =
      ∑ id : EdgeId m L, if geometryFlag g id then f id else 0 := by
  simp only [idsOfGeometry, Finset.sum_filter]

/-- Split the disjoint V/H/D families, with column or cut before row in each
sum. The function on physical IDs is arbitrary. -/
theorem sum_idsOfGeometry_eq_vhd (g : ColumnGeometry m L)
    (f : EdgeId m L → W) :
    (∑ id ∈ idsOfGeometry g, f id) =
      (∑ c : Fin L, ∑ r : Fin m,
        if g.1 c r then f (.inl (r, c)) else 0) +
      ((∑ c : Fin (L - 1), ∑ r : Fin m,
        if g.2.1 c r then f (.inr (.inl (r, c))) else 0) +
       (∑ c : Fin (L - 1), ∑ r : Fin m,
        if g.2.2 c r then f (.inr (.inr (r, c))) else 0)) := by
  rw [sum_idsOfGeometry_eq_flagSum]
  simp only [EdgeId, Fintype.sum_sum_type, Fintype.sum_prod_type_right,
    geometryFlag]

/-- Combine the horizontal and diagonal contributions at each cut and row.
This is a local charging identity, without a transfer-state hypothesis. -/
theorem sum_idsOfGeometry_eq_column_cut (g : ColumnGeometry m L)
    (f : EdgeId m L → W) :
    (∑ id ∈ idsOfGeometry g, f id) =
      (∑ c : Fin L, ∑ r : Fin m,
        if g.1 c r then f (.inl (r, c)) else 0) +
      (∑ c : Fin (L - 1), ∑ r : Fin m,
        ((if g.2.1 c r then f (.inr (.inl (r, c))) else 0) +
         (if g.2.2 c r then f (.inr (.inr (r, c))) else 0))) := by
  simpa only [Finset.sum_add_distrib] using sum_idsOfGeometry_eq_vhd g f

/-- Exact concrete edge-weight decomposition into vertical column charges
and horizontal/diagonal cut charges. Valid for every number of columns. -/
theorem sum_realizedEdges_eq_column_cut (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (w : Sym2 (Vertex m L) → W) :
    (∑ e ∈ realizedEdges hm g, w e) =
      (∑ c : Fin L, ∑ r : Fin m,
        if g.1 c r then w (toEdge hm (.inl (r, c))) else 0) +
      (∑ c : Fin (L - 1), ∑ r : Fin m,
        ((if g.2.1 c r then w (toEdge hm (.inr (.inl (r, c)))) else 0) +
         (if g.2.2 c r then w (toEdge hm (.inr (.inr (r, c)))) else 0))) := by
  rw [sum_realizedEdges_eq_selectedIds]
  exact sum_idsOfGeometry_eq_column_cut g (fun id => w (toEdge hm id))

/-- Charge V at its column and H/D at their lower/source column. The filter
therefore includes outgoing H and D from column `j`. No prefix-parity object
or alternative charging convention is introduced. -/
theorem sum_idsOfGeometry_filter_le_eq_vhd (g : ColumnGeometry m L)
    (f : EdgeId m L → W) (j : ℕ) :
    (∑ id ∈ (idsOfGeometry g).filter (fun id => (sourceVertex id).2.val ≤ j), f id) =
      (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j),
        ∑ r : Fin m, if g.1 c r then f (.inl (r, c)) else 0) +
      ((∑ c ∈ (Finset.univ : Finset (Fin (L - 1))).filter (fun c => c.val ≤ j),
        ∑ r : Fin m, if g.2.1 c r then f (.inr (.inl (r, c))) else 0) +
       (∑ c ∈ (Finset.univ : Finset (Fin (L - 1))).filter (fun c => c.val ≤ j),
        ∑ r : Fin m, if g.2.2 c r then f (.inr (.inr (r, c))) else 0)) := by
  rw [Finset.sum_filter, sum_idsOfGeometry_eq_vhd]
  simp only [sourceVertex, lowerCol, Finset.sum_filter]
  congr 1
  · apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c.val ≤ j <;> simp [hc]
  · congr 1
    · apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c.val ≤ j <;> simp [hc]
    · apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c.val ≤ j <;> simp [hc]

/-- The same source-column filter with H/D grouped at each cut and row. -/
theorem sum_idsOfGeometry_filter_le_eq_column_cut (g : ColumnGeometry m L)
    (f : EdgeId m L → W) (j : ℕ) :
    (∑ id ∈ (idsOfGeometry g).filter (fun id => (sourceVertex id).2.val ≤ j), f id) =
      (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j),
        ∑ r : Fin m, if g.1 c r then f (.inl (r, c)) else 0) +
      (∑ c ∈ (Finset.univ : Finset (Fin (L - 1))).filter (fun c => c.val ≤ j),
        ∑ r : Fin m,
          ((if g.2.1 c r then f (.inr (.inl (r, c))) else 0) +
           (if g.2.2 c r then f (.inr (.inr (r, c))) else 0))) := by
  simpa only [Finset.sum_add_distrib] using sum_idsOfGeometry_filter_le_eq_vhd g f j

/-- Direct specialization of the owner's pinned row-step classifier. -/
theorem meridianWeight_toEdge_vertical (hm : 3 ≤ m) (r : Fin m) (c : Fin L) :
    meridianWeight hm (toEdge hm (.inl (r, c))) =
      if r = lastRow m hm then 1 else 0 := by
  exact meridianWeight_nextRow hm r (rowSucc hm r) (nextRow_rowSucc hm r) c c

/-- Horizontal edges have equal endpoint rows and hence zero weight. -/
theorem meridianWeight_toEdge_horizontal (hm : 3 ≤ m)
    (r : Fin m) (c : Fin (L - 1)) :
    meridianWeight hm (toEdge hm (.inr (.inl (r, c)))) = 0 := by
  exact meridianWeight_sameRow hm r (lowerCol c) (upperCol c)

/-- Diagonals use the same owner classifier, at their lower/source row. -/
theorem meridianWeight_toEdge_diagonal (hm : 3 ≤ m)
    (r : Fin m) (c : Fin (L - 1)) :
    meridianWeight hm (toEdge hm (.inr (.inr (r, c)))) =
      if r = lastRow m hm then 1 else 0 := by
  exact meridianWeight_nextRow hm r (rowSucc hm r) (nextRow_rowSucc hm r)
    (lowerCol c) (upperCol c)

/-- Finite-sum algebra for a mask applied to a weight supported at one row. -/
theorem sum_masked_singleton_row (bits : Fin m → Bool) (r₀ : Fin m) (x : W) :
    (∑ r : Fin m, if bits r then (if r = r₀ then x else 0) else 0) =
      if bits r₀ then x else 0 := by
  calc
    _ = if bits r₀ then (if r₀ = r₀ then x else 0) else 0 := by
      apply Finset.sum_eq_single r₀
      · intro r _ hr
        simp [hr]
      · simp
    _ = _ := by simp

/-- Full selected-ID meridian parity is exactly the V and D last-row bits.
This is a finite combinatorial identity, with no contractibility claim. -/
theorem sum_idsOfGeometry_meridian_eq_lastRow (hm : 3 ≤ m)
    (g : ColumnGeometry m L) :
    (∑ id ∈ idsOfGeometry g, meridianWeight hm (toEdge hm id)) =
      (∑ c : Fin L, if g.1 c (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ c : Fin (L - 1), if g.2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [sum_idsOfGeometry_eq_vhd]
  simp only [meridianWeight_toEdge_vertical, meridianWeight_toEdge_horizontal,
    meridianWeight_toEdge_diagonal, ite_self, Finset.sum_const_zero, zero_add,
    sum_masked_singleton_row]

/-- The same last-row formula for the actual unordered selected edge set. -/
theorem sum_realizedEdges_meridian_eq_lastRow (hm : 3 ≤ m)
    (g : ColumnGeometry m L) :
    (∑ e ∈ realizedEdges hm g, meridianWeight hm e) =
      (∑ c : Fin L, if g.1 c (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ c : Fin (L - 1), if g.2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [sum_realizedEdges_eq_selectedIds]
  exact sum_idsOfGeometry_meridian_eq_lastRow hm g

/-- Source-column charging through `j`, including outgoing D at `j`.
Outgoing H has zero weight. The statement remains valid for every `L,j`. -/
theorem sum_idsOfGeometry_filter_le_meridian_eq_lastRow (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (j : ℕ) :
    (∑ id ∈ (idsOfGeometry g).filter (fun id => (sourceVertex id).2.val ≤ j),
      meridianWeight hm (toEdge hm id)) =
      (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j),
        if g.1 c (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ c ∈ (Finset.univ : Finset (Fin (L - 1))).filter (fun c => c.val ≤ j),
        if g.2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [sum_idsOfGeometry_filter_le_eq_vhd]
  simp only [meridianWeight_toEdge_vertical, meridianWeight_toEdge_horizontal,
    meridianWeight_toEdge_diagonal, ite_self, Finset.sum_const_zero, zero_add,
    sum_masked_singleton_row]

end TriangularEdgeEncoding
