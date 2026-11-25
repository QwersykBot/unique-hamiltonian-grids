import AuxiliaryCycle

/-!
# The two-column unrolled perimeter witness

The circumference is `n + 1`, with `n ≥ 2`. The enumerated cycle uses no
row-wrap edge. All parity conclusions concern the existing finite meridian
indicator, not an unformalized annular contractibility correspondence.
-/

namespace TriangularCylinder

open SimpleGraph

/-- Ascend the left column, then descend the right column. -/
def perimeterVertex (n : ℕ) (_hn : 2 ≤ n) (i : Fin (2 * n + 2)) : Vertex (n + 1) 2 :=
  if h : i.val < n + 1 then
    (⟨i.val, h⟩, 0)
  else
    (⟨2 * n + 1 - i.val, by have := i.isLt; omega⟩, 1)

theorem perimeterVertex_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (perimeterVertex n hn) := by
  intro i j h
  apply Fin.ext
  have hr := congrArg (fun x : Vertex (n + 1) 2 => x.1.val) h
  have hc := congrArg (fun x : Vertex (n + 1) 2 => x.2.val) h
  have hi := i.isLt
  have hj := j.isLt
  unfold perimeterVertex at hr hc
  split_ifs at hr hc
  all_goals simp_all
  all_goals omega

theorem perimeterVertex_bijective (n : ℕ) (hn : 2 ≤ n) :
    Function.Bijective (perimeterVertex n hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨perimeterVertex_injective n hn, ?_⟩
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin]
  omega

theorem perimeterVertex_squareStep (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 1)) :
    SquareStep (perimeterVertex n hn i.castSucc) (perimeterVertex n hn i.succ) := by
  have hi := i.isLt
  unfold SquareStep perimeterVertex
  simp only [Fin.coe_castSucc, Fin.val_succ]
  split_ifs
  all_goals simp_all
  all_goals omega

theorem perimeterVertex_adj (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 1)) :
    (graph (n + 1) 2 (by omega)).Adj
      (perimeterVertex n hn i.castSucc) (perimeterVertex n hn i.succ) :=
  squareStep_adj (by omega) (perimeterVertex_squareStep n hn i)

theorem perimeterVertex_edgeWeight_zero (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 1)) :
    meridianWeight (show 3 ≤ n + 1 by omega)
      s(perimeterVertex n hn i.castSucc, perimeterVertex n hn i.succ) = 0 := by
  have hstep := perimeterVertex_squareStep n hn i
  unfold SquareStep at hstep
  apply meridianWeight_zero_of_close_rows <;> omega

theorem perimeterVertex_first (n : ℕ) (hn : 2 ≤ n) :
    perimeterVertex n hn 0 = (firstRow (n + 1) (by omega), 0) := by
  simp [perimeterVertex, firstRow]

theorem perimeterVertex_last (n : ℕ) (hn : 2 ≤ n) :
    perimeterVertex n hn (Fin.last (2 * n + 1)) =
      (firstRow (n + 1) (by omega), 1) := by
  have h : ¬2 * n + 1 < n + 1 := by omega
  simp [perimeterVertex, h, firstRow]

theorem perimeter_closing_adj (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 2 (by omega)).Adj
      (perimeterVertex n hn (Fin.last (2 * n + 1))) (perimeterVertex n hn 0) := by
  rw [perimeterVertex_first, perimeterVertex_last]
  apply squareStep_adj
  simp [SquareStep]

theorem perimeter_closing_weight (n : ℕ) (hn : 2 ≤ n) :
    meridianWeight (show 3 ≤ n + 1 by omega)
      s(perimeterVertex n hn (Fin.last (2 * n + 1)), perimeterVertex n hn 0) = 0 := by
  rw [perimeterVertex_first, perimeterVertex_last]
  exact meridianWeight_sameRow _ _ _ _

def perimeterCycle (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 2 (by omega)).Walk
      (perimeterVertex n hn (Fin.last (2 * n + 1)))
      (perimeterVertex n hn (Fin.last (2 * n + 1))) :=
  EnumeratedWalk.ofFnCycle (perimeterVertex n hn)
    (perimeterVertex_adj n hn) (perimeter_closing_adj n hn)

theorem perimeterCycle_isHamiltonianCycle (n : ℕ) (hn : 2 ≤ n) :
    (perimeterCycle n hn).IsHamiltonianCycle := by
  apply EnumeratedWalk.ofFnCycle_isHamiltonianCycle
  · omega
  · exact perimeterVertex_bijective n hn

theorem perimeterCycle_typeParity (n : ℕ) (hn : 2 ≤ n) :
    typeParity (show 3 ≤ n + 1 by omega) (perimeterCycle n hn) = 0 := by
  simp only [typeParity, CylinderSplice.edgeWeight, perimeterCycle,
    EnumeratedWalk.ofFnCycle_edges, List.map_cons, List.sum_cons,
    List.map_ofFn, Function.comp_def, perimeterVertex_edgeWeight_zero, perimeter_closing_weight]
  simp

theorem mem_perimeterCycle_edges (n : ℕ) (hn : 2 ≤ n) (e : Sym2 (Vertex (n + 1) 2)) :
    e ∈ (perimeterCycle n hn).edges ↔
      e = s(perimeterVertex n hn (Fin.last (2 * n + 1)), perimeterVertex n hn 0) ∨
        ∃ i : Fin (2 * n + 1), s(perimeterVertex n hn i.castSucc, perimeterVertex n hn i.succ) = e :=
  EnumeratedWalk.mem_ofFnCycle_edges _ _ _ e

end TriangularCylinder
