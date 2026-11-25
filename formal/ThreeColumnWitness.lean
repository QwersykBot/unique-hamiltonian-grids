import TwoColumnWitness

/-!
# The three-column unrolled witness

The left/middle prefix follows the paired insertions in the manuscript.
Its final four vertices are middle(n-1), left(n-1), left(n), middle(n).
For odd circumference the entry to this tail is the prescribed diagonal.
The right column is then traversed downward, with a horizontal closing edge.
-/

namespace TriangularCylinder

open SimpleGraph

/-- Nonwrap square steps and the consistently oriented nonwrap diagonals. -/
def UnrolledStep {m L : ℕ} (x y : Vertex m L) : Prop :=
  SquareStep x y ∨
    (x.1.val + 1 = y.1.val ∧ x.2.val + 1 = y.2.val) ∨
    (y.1.val + 1 = x.1.val ∧ y.2.val + 1 = x.2.val)

theorem unrolledStep_adj {m L : ℕ} (hm : 3 ≤ m) {x y : Vertex m L}
    (h : UnrolledStep x y) : (graph m L hm).Adj x y := by
  rcases h with hsq | ⟨hr, hc⟩ | ⟨hr, hc⟩
  · exact squareStep_adj hm hsq
  · apply Or.inl
    apply Or.inr
    apply Or.inr
    refine ⟨?_, hc⟩
    unfold NextRow
    rw [hr, Nat.mod_eq_of_lt y.1.isLt]
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    refine ⟨?_, hc⟩
    unfold NextRow
    rw [hr, Nat.mod_eq_of_lt x.1.isLt]

/-- Columns along the left/middle prefix. The final two row pairs are fixed
as middle-left and left-middle, for both parities of the circumference. -/
def threePrefixColumn (n i : ℕ) : Fin 3 :=
  if i < 2 * n - 2 then
    if i % 4 = 0 ∨ i % 4 = 3 then 1 else 0
  else if i = 2 * n - 2 ∨ i = 2 * n + 1 then 1 else 0

theorem threePrefixColumn_le_one (n i : ℕ) : (threePrefixColumn n i).val ≤ 1 := by
  unfold threePrefixColumn
  split_ifs <;> decide

/-- Enumerate the left/middle spanning path, then descend the right column. -/
def threeWitnessVertex (n : ℕ) (_hn : 2 ≤ n) (i : Fin (3 * n + 3)) : Vertex (n + 1) 3 :=
  if h : i.val < 2 * n + 2 then
    (⟨i.val / 2, by omega⟩, threePrefixColumn n i.val)
  else
    (⟨3 * n + 2 - i.val, by have := i.isLt; omega⟩, 2)

set_option maxHeartbeats 1000000 in
theorem threeWitnessVertex_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (threeWitnessVertex n hn) := by
  intro i j h
  apply Fin.ext
  have hr := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h
  have hc := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h
  have hi := i.isLt
  have hj := j.isLt
  by_cases hiP : i.val < 2 * n + 2
  · by_cases hjP : j.val < 2 * n + 2
    · simp only [threeWitnessVertex, dif_pos hiP, dif_pos hjP] at hr hc
      unfold threePrefixColumn at hc
      split_ifs at hc
      all_goals simp_all
      all_goals omega
    · simp only [threeWitnessVertex, dif_pos hiP, dif_neg hjP] at hc
      have hle := threePrefixColumn_le_one n i.val
      omega
  · by_cases hjP : j.val < 2 * n + 2
    · simp only [threeWitnessVertex, dif_neg hiP, dif_pos hjP] at hc
      have hle := threePrefixColumn_le_one n j.val
      omega
    · simp only [threeWitnessVertex, dif_neg hiP, dif_neg hjP] at hr
      omega

theorem threeWitnessVertex_bijective (n : ℕ) (hn : 2 ≤ n) :
    Function.Bijective (threeWitnessVertex n hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨threeWitnessVertex_injective n hn, ?_⟩
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin]
  omega

set_option maxHeartbeats 1000000 in
theorem threeWitnessVertex_unrolledStep (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 2)) :
    UnrolledStep (threeWitnessVertex n hn i.castSucc) (threeWitnessVertex n hn i.succ) := by
  have hi := i.isLt
  unfold UnrolledStep SquareStep threeWitnessVertex
  simp only [Fin.coe_castSucc, Fin.val_succ]
  split_ifs
  all_goals simp only [threePrefixColumn]
  all_goals try split_ifs
  all_goals simp_all
  all_goals omega

theorem threeWitnessVertex_adj (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 2)) :
    (graph (n + 1) 3 (by omega)).Adj
      (threeWitnessVertex n hn i.castSucc) (threeWitnessVertex n hn i.succ) :=
  unrolledStep_adj (by omega) (threeWitnessVertex_unrolledStep n hn i)

theorem threeWitnessVertex_edgeWeight_zero (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 2)) :
    meridianWeight (show 3 ≤ n + 1 by omega)
      s(threeWitnessVertex n hn i.castSucc, threeWitnessVertex n hn i.succ) = 0 := by
  have hstep := threeWitnessVertex_unrolledStep n hn i
  unfold UnrolledStep SquareStep at hstep
  apply meridianWeight_zero_of_close_rows <;> omega

theorem threeWitnessVertex_first (n : ℕ) (hn : 2 ≤ n) :
    threeWitnessVertex n hn 0 = (firstRow (n + 1) (by omega), 1) := by
  have h : 0 < 2 * n - 2 := by omega
  simp [threeWitnessVertex, threePrefixColumn, h, firstRow]

theorem threeWitnessVertex_last (n : ℕ) (hn : 2 ≤ n) :
    threeWitnessVertex n hn (Fin.last (3 * n + 2)) =
      (firstRow (n + 1) (by omega), 2) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [threeWitnessVertex, Fin.val_last] <;>
    split_ifs <;> simp_all [firstRow] <;> omega

theorem threeWitness_closing_adj (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 3 (by omega)).Adj
      (threeWitnessVertex n hn (Fin.last (3 * n + 2))) (threeWitnessVertex n hn 0) := by
  rw [threeWitnessVertex_first, threeWitnessVertex_last]
  apply squareStep_adj
  simp [SquareStep]

theorem threeWitness_closing_weight (n : ℕ) (hn : 2 ≤ n) :
    meridianWeight (show 3 ≤ n + 1 by omega)
      s(threeWitnessVertex n hn (Fin.last (3 * n + 2)), threeWitnessVertex n hn 0) = 0 := by
  rw [threeWitnessVertex_first, threeWitnessVertex_last]
  exact meridianWeight_sameRow _ _ _ _

def threeWitnessCycle (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 3 (by omega)).Walk
      (threeWitnessVertex n hn (Fin.last (3 * n + 2)))
      (threeWitnessVertex n hn (Fin.last (3 * n + 2))) :=
  EnumeratedWalk.ofFnCycle (threeWitnessVertex n hn)
    (threeWitnessVertex_adj n hn) (threeWitness_closing_adj n hn)

theorem threeWitnessCycle_isHamiltonianCycle (n : ℕ) (hn : 2 ≤ n) :
    (threeWitnessCycle n hn).IsHamiltonianCycle := by
  apply EnumeratedWalk.ofFnCycle_isHamiltonianCycle
  · omega
  · exact threeWitnessVertex_bijective n hn

theorem threeWitnessCycle_typeParity (n : ℕ) (hn : 2 ≤ n) :
    typeParity (show 3 ≤ n + 1 by omega) (threeWitnessCycle n hn) = 0 := by
  simp only [typeParity, CylinderSplice.edgeWeight, threeWitnessCycle,
    EnumeratedWalk.ofFnCycle_edges, List.map_cons, List.sum_cons,
    List.map_ofFn, Function.comp_def, threeWitnessVertex_edgeWeight_zero,
    threeWitness_closing_weight]
  simp

theorem mem_threeWitnessCycle_edges (n : ℕ) (hn : 2 ≤ n) (e : Sym2 (Vertex (n + 1) 3)) :
    e ∈ (threeWitnessCycle n hn).edges ↔
      e = s(threeWitnessVertex n hn (Fin.last (3 * n + 2)), threeWitnessVertex n hn 0) ∨
        ∃ i : Fin (3 * n + 2),
          s(threeWitnessVertex n hn i.castSucc, threeWitnessVertex n hn i.succ) = e :=
  EnumeratedWalk.mem_ofFnCycle_edges _ _ _ e

end TriangularCylinder
