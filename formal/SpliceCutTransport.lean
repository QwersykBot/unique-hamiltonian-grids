import StateWidthTransport
import ColumnTailSums

/-!
# Indexed old cuts in a cylinder enlarged on the left

Cut and local-step indices shift by the inserted width.  The untouched right
tail has the same length.  The actual fixed-width cut encoder can therefore
be compared with the same split used by the frozen splice-state theorems.
-/

namespace TriangularCylinder.SpliceCutTransport

open SimpleGraph BoundaryState Transfer

def shiftCut (a : ℕ) {n : ℕ} (c : Fin (n + 1)) : Fin (a + n + 1) :=
  ⟨a + c.val, by have := c.isLt; omega⟩

def shiftStep (a : ℕ) {n : ℕ} (i : Fin n) : Fin (a + n) := Fin.natAdd a i

@[simp] theorem shiftCut_val (a : ℕ) {n : ℕ} (c : Fin (n + 1)) :
    (shiftCut a c).val = a + c.val := rfl

@[simp] theorem shiftStep_val (a : ℕ) {n : ℕ} (i : Fin n) :
    (shiftStep a i).val = a + i.val := rfl

@[simp] theorem shiftCut_castSucc (a : ℕ) {n : ℕ} (i : Fin n) :
    shiftCut a i.castSucc = (shiftStep a i).castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem shiftCut_succ (a : ℕ) {n : ℕ} (i : Fin n) :
    shiftCut a i.succ = (shiftStep a i).succ := by
  apply Fin.ext
  rfl

@[simp] theorem shiftCut_last (a n : ℕ) :
    shiftCut a (Fin.last n) = Fin.last (a + n) := by
  apply Fin.ext
  rfl

@[simp] theorem cutTail_shiftCut (a : ℕ) {n : ℕ} (c : Fin (n + 1)) :
    cutTail (shiftCut a c) = cutTail c := by
  unfold cutTail
  simp only [shiftCut_val]
  omega

private theorem comap_widthEquiv_trans {m L₀ L₁ L₂ : ℕ}
    (G : SimpleGraph (Vertex m L₂)) (h₀ : L₀ = L₁) (h₁ : L₁ = L₂) :
    (G.comap (widthEquiv h₁)).comap (widthEquiv h₀) =
      G.comap (widthEquiv (h₀.trans h₁)) := by
  cases h₀
  cases h₁
  rfl

private theorem stateAt_comap_widthEquiv_eq_of_tail_eq {m j k k' L : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hk' : 1 ≤ k') (hkk : k = k')
    (hL : j + 1 + k = L) (hL' : j + 1 + k' = L)
    (G : SimpleGraph (Vertex m L)) :
    stateAt hm hk (G.comap (widthEquiv hL)) =
      stateAt hm hk' (G.comap (widthEquiv hL')) := by
  subst k'
  rfl

/-- Fixed-width encoding at the shifted cut uses exactly the shifted old
column split and coordinate-preserving width map. -/
theorem cutState_shiftCut_eq_stateAt {m a n : ℕ} (hm : 3 ≤ m)
    (G : SimpleGraph (Vertex m (a + (n + 2)))) (c : Fin (n + 1)) :
    cutState hm (G.comap (widthEquiv (by omega : (a + n) + 2 = a + (n + 2)))) (shiftCut a c) =
      stateAt (j := a + c.val) hm (cutTail_pos c)
        (G.comap (widthEquiv (by have := cutWidth_eq c; omega :
          (a + c.val) + 1 + cutTail c = a + (n + 2)))) := by
  unfold cutState cutGraph
  rw [comap_widthEquiv_trans]
  exact stateAt_comap_widthEquiv_eq_of_tail_eq hm _ _ (cutTail_shiftCut a c) _ _ G

/-- The column used by a shifted local step is the old column shifted by `a`. -/
theorem shiftStep_column (a : ℕ) {n : ℕ} (i : Fin n) :
    (shiftStep a i).succ.castSucc =
      ColumnTailSums.shiftCol a (by omega : (a + n) + 2 = a + (n + 2)) i.succ.castSucc := by
  apply Fin.ext
  rfl

/-- The final column is shifted by the same inserted width. -/
theorem shift_last_column (a n : ℕ) :
    Fin.last (a + n + 1) =
      ColumnTailSums.shiftCol a (by omega : (a + n) + 2 = a + (n + 2)) (Fin.last (n + 1)) := by
  apply Fin.ext
  rfl

/-- Shifted-column width transport agrees with the physical right embedding. -/
theorem widthEquiv_shiftCol {m a n : ℕ} (r : Fin m) (c : Fin (n + 2)) :
    widthEquiv (by omega : (a + n) + 2 = a + (n + 2))
        (r, ColumnTailSums.shiftCol a (by omega : (a + n) + 2 = a + (n + 2)) c) =
      rightVertex a (r, c) := by
  apply Prod.ext rfl
  apply Fin.ext
  rfl

#print axioms shiftCut_castSucc
#print axioms shiftCut_succ
#print axioms shiftCut_last
#print axioms cutTail_shiftCut
#print axioms cutState_shiftCut_eq_stateAt
#print axioms shiftStep_column
#print axioms shift_last_column
#print axioms widthEquiv_shiftCol

end TriangularCylinder.SpliceCutTransport
