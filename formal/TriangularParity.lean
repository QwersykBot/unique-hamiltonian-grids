import TriangularCylinder
import Mathlib.Data.ZMod.Basic

/-!
# Mod-two meridian bookkeeping for the concrete join

The weight is the indicator that the unordered endpoint rows are the last
and first rows.  On the concrete cylinder edge families these are exactly
the wrap vertical and wrap diagonal edges.  This file proves the finite
combinatorial parity identity, not a theorem about annular contractibility.
-/

namespace TriangularCylinder

open SimpleGraph

def firstRow (m : ℕ) (hm : 3 ≤ m) : Fin m := ⟨0, by omega⟩

def lastRow (m : ℕ) (hm : 3 ≤ m) : Fin m := ⟨m - 1, by omega⟩

/-- The mod-two indicator for an undirected edge crossing the row meridian. -/
def meridianWeight {m L : ℕ} (hm : 3 ≤ m) (e : Sym2 (Vertex m L)) : ZMod 2 :=
  if Sym2.map Prod.fst e = s(lastRow m hm, firstRow m hm) then 1 else 0

theorem meridianWeight_pair {m L : ℕ} (hm : 3 ≤ m) (x y : Vertex m L) :
    meridianWeight hm s(x, y) =
      if s(x.1, y.1) = s(lastRow m hm, firstRow m hm) then 1 else 0 := rfl

theorem sameRow_ne_meridian {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    s(r, r) ≠ s(lastRow m hm, firstRow m hm) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · have hc := congrArg Fin.val (h₀.symm.trans h₁)
    simp only [lastRow, firstRow] at hc
    omega
  · have hc := congrArg Fin.val (h₀.symm.trans h₁)
    simp only [lastRow, firstRow] at hc
    omega

@[simp]
theorem meridianWeight_sameRow {m L : ℕ} (hm : 3 ≤ m)
    (r : Fin m) (c d : Fin L) : meridianWeight hm s((r, c), (r, d)) = 0 := by
  rw [meridianWeight_pair, if_neg (sameRow_ne_meridian hm r)]

@[simp]
theorem meridianWeight_map_left {m a b : ℕ} (hm : 3 ≤ m) (e : Sym2 (Vertex m a)) :
    meridianWeight hm (Sym2.map (leftVertex b) e) = meridianWeight hm e := by
  refine Sym2.ind (fun x y => ?_) e
  rfl

@[simp]
theorem meridianWeight_map_right {m a b : ℕ} (hm : 3 ≤ m) (e : Sym2 (Vertex m b)) :
    meridianWeight hm (Sym2.map (rightVertex a) e) = meridianWeight hm e := by
  refine Sym2.ind (fun x y => ?_) e
  rfl

/-- Sum of selected wrap-edge indicators.  It is called parity, not
contractibility: the topological correspondence is a separate obligation. -/
def typeParity {m L : ℕ} (hm : 3 ≤ m) {x y : Vertex m L}
    (p : (graph m L hm).Walk x y) : ZMod 2 :=
  CylinderSplice.edgeWeight (meridianWeight hm) p

@[simp]
theorem typeParity_map_left {m a b : ℕ} (hm : 3 ≤ m) {x y : Vertex m a}
    (p : (graph m a hm).Walk x y) :
    typeParity hm (p.map (leftHom (b := b) hm)) = typeParity hm p := by
  simp only [typeParity, CylinderSplice.edgeWeight, Walk.edges_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  exact meridianWeight_map_left hm e

@[simp]
theorem typeParity_map_right {m a b : ℕ} (hm : 3 ≤ m) {x y : Vertex m b}
    (p : (graph m b hm).Walk x y) :
    typeParity hm (p.map (rightHom (a := a) hm)) = typeParity hm p := by
  simp only [typeParity, CylinderSplice.edgeWeight, Walk.edges_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  exact meridianWeight_map_right hm e

/-- The two deleted vertical edges have equal meridian weight, hence cancel
modulo two; the two actual horizontal seams have zero meridian weight. -/
theorem splice_meridian_balance
    {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b) (r s : Fin m) :
    meridianWeight hm s(leftVertex b (r, lastCol a ha), leftVertex b (s, lastCol a ha)) +
      meridianWeight hm s(rightVertex a (s, firstCol b hb), rightVertex a (r, firstCol b hb)) =
    meridianWeight hm s(leftVertex b (r, lastCol a ha), rightVertex a (r, firstCol b hb)) +
      meridianWeight hm s(rightVertex a (s, firstCol b hb), leftVertex b (s, lastCol a ha)) := by
  simp only [leftVertex, rightVertex, meridianWeight_sameRow, zero_add]
  simp only [meridianWeight_pair]
  rw [Sym2.eq_swap (a := s) (b := r)]
  split_ifs <;> decide

/-- Concrete mod-two type addition under the cylinder splice, including the
last-to-first cyclic row gap.  Hamiltonicity is checked in the separate
`spliceAt_isHamiltonianCycle` theorem. -/
theorem spliceAt_typeParity
    {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (r s : Fin m) (hgap : NextRow r s)
    (p : (graph m a hm).Walk (s, lastCol a ha) (r, lastCol a ha))
    (q : (graph m b hm).Walk (r, firstCol b hb) (s, firstCol b hb)) :
    typeParity hm (spliceAt hm ha hb r s p q) =
      typeParity hm (Walk.cons (vertical_edge hm r s hgap (lastCol a ha)) p) +
      typeParity hm (Walk.cons (vertical_edge hm r s hgap (firstCol b hb)).symm q) := by
  have hjoin :
      typeParity hm (spliceAt hm ha hb r s p q) =
        typeParity hm ((Walk.cons (vertical_edge hm r s hgap (lastCol a ha)) p).map
          (leftHom (b := b) hm)) +
        typeParity hm ((Walk.cons (vertical_edge hm r s hgap (firstCol b hb)).symm q).map
          (rightHom (a := a) hm)) := by
    exact CylinderSplice.splice_edgeWeight (meridianWeight hm)
      (p.map (leftHom (b := b) hm)) (q.map (rightHom (a := a) hm))
      ((leftHom (b := b) hm).map_adj (vertical_edge hm r s hgap (lastCol a ha)))
      ((rightHom (a := a) hm).map_adj (vertical_edge hm r s hgap (firstCol b hb)).symm)
      (horizontal_seam hm ha hb r) (horizontal_seam hm ha hb s).symm
      (splice_meridian_balance hm ha hb r s)
  simpa only [typeParity_map_left, typeParity_map_right] using hjoin

#print axioms spliceAt_typeParity

end TriangularCylinder
