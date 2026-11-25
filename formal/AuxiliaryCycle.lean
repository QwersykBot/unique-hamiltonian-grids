import TriangularParity
import EnumeratedWalk
import MeridianClassifier
import Mathlib.Data.Fintype.EquivFin

/-!
# The all-width three-column auxiliary

The circumference is written `n + 1`, with `n ≥ 2`.  This is exactly the
range of circumferences at least three.  The tail enumeration follows the
released traversal after its initial wrap edge.
-/

namespace TriangularCylinder

open SimpleGraph

/-- The tail of the auxiliary traversal: rows `n,...,1` in column 0,
rows `1,...,n` in column 1, rows `n,...,0` in column 2, then `(0,1),(0,0)`. -/
def auxVertex (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 3)) : Vertex (n + 1) 3 :=
  if hA : i.val < n then
    (⟨n - i.val, by omega⟩, 0)
  else if hB : i.val < 2 * n then
    (⟨i.val - n + 1, by omega⟩, 1)
  else if hC : i.val < 3 * n + 1 then
    (⟨3 * n - i.val, by omega⟩, 2)
  else if hD : i.val = 3 * n + 1 then
    (⟨0, by omega⟩, 1)
  else
    (⟨0, by omega⟩, 0)

theorem auxVertex_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (auxVertex n hn) := by
  intro i j h
  apply Fin.ext
  have hr := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h
  have hc := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h
  have hi := i.isLt
  have hj := j.isLt
  unfold auxVertex at hr hc
  split_ifs at hr hc <;> simp_all <;> omega

theorem auxVertex_bijective (n : ℕ) (hn : 2 ≤ n) :
    Function.Bijective (auxVertex n hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨auxVertex_injective n hn, ?_⟩
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin]
  omega

/-- An ordinary nonwrap square-grid step, specified solely by coordinates. -/
def SquareStep {m L : ℕ} (x y : Vertex m L) : Prop :=
  (x.2.val = y.2.val ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val)) ∨
  (x.1.val = y.1.val ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val))

theorem squareStep_adj {m L : ℕ} (hm : 3 ≤ m) {x y : Vertex m L}
    (h : SquareStep x y) : (graph m L hm).Adj x y := by
  rcases h with ⟨hc, hr | hr⟩ | ⟨hr, hc | hc⟩
  · apply Or.inl
    apply Or.inl
    refine ⟨Fin.ext hc, ?_⟩
    unfold NextRow
    rw [hr, Nat.mod_eq_of_lt y.1.isLt]
  · apply Or.inr
    apply Or.inl
    refine ⟨Fin.ext hc.symm, ?_⟩
    unfold NextRow
    rw [hr, Nat.mod_eq_of_lt x.1.isLt]
  · exact Or.inl (Or.inr (Or.inl ⟨Fin.ext hr, hc⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨Fin.ext hr.symm, hc⟩))

theorem auxVertex_squareStep (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 2)) :
    SquareStep (auxVertex n hn i.castSucc) (auxVertex n hn i.succ) := by
  have hi := i.isLt
  unfold SquareStep auxVertex
  simp only [Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem auxVertex_adj (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 2)) :
    (graph (n + 1) 3 (by omega)).Adj
      (auxVertex n hn i.castSucc) (auxVertex n hn i.succ) :=
  squareStep_adj (by omega) (auxVertex_squareStep n hn i)

theorem meridianWeight_zero_of_close_rows {m L : ℕ} (hm : 3 ≤ m)
    (x y : Vertex m L)
    (hxy : x.1.val ≤ y.1.val + 1) (hyx : y.1.val ≤ x.1.val + 1) :
    meridianWeight hm s(x, y) = 0 := by
  rw [meridianWeight_pair]
  apply if_neg
  intro h
  rcases Sym2.eq_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hrx := congrArg Fin.val hx
    have hry := congrArg Fin.val hy
    simp only [lastRow, firstRow] at hrx hry
    omega
  · have hrx := congrArg Fin.val hx
    have hry := congrArg Fin.val hy
    simp only [lastRow, firstRow] at hrx hry
    omega

theorem auxVertex_edgeWeight_zero (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 2)) :
    meridianWeight (show 3 ≤ n + 1 by omega)
      s(auxVertex n hn i.castSucc, auxVertex n hn i.succ) = 0 := by
  have hstep := auxVertex_squareStep n hn i
  unfold SquareStep at hstep
  apply meridianWeight_zero_of_close_rows
  · omega
  · omega

theorem auxVertex_first (n : ℕ) (hn : 2 ≤ n) :
    auxVertex n hn 0 = (lastRow (n + 1) (by omega), 0) := by
  have hn0 : 0 < n := by omega
  simp [auxVertex, hn0, lastRow]

theorem auxVertex_last (n : ℕ) (hn : 2 ≤ n) :
    auxVertex n hn (Fin.last (3 * n + 2)) = (firstRow (n + 1) (by omega), 0) := by
  have hA : ¬3 * n + 2 < n := by omega
  have hB : ¬3 * n + 2 < 2 * n := by omega
  have hC : ¬3 * n + 2 < 3 * n + 1 := by omega
  have hD : ¬3 * n + 2 = 3 * n + 1 := by omega
  simp [auxVertex, hA, hB, hC, hD, firstRow]

theorem aux_closing_adj (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 3 (by omega)).Adj
      (auxVertex n hn (Fin.last (3 * n + 2))) (auxVertex n hn 0) := by
  rw [auxVertex_first, auxVertex_last]
  apply SimpleGraph.Adj.symm
  apply vertical_edge
  simp [NextRow, lastRow, firstRow]

theorem aux_closing_weight (n : ℕ) (hn : 2 ≤ n) :
    meridianWeight (show 3 ≤ n + 1 by omega)
      s(auxVertex n hn (Fin.last (3 * n + 2)), auxVertex n hn 0) = 1 := by
  rw [auxVertex_first, auxVertex_last]
  simp [meridianWeight, Sym2.eq_swap]

/-- The explicit complete auxiliary cycle, with its only wrap edge first. -/
def auxiliaryCycle (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 3 (by omega)).Walk
      (auxVertex n hn (Fin.last (3 * n + 2)))
      (auxVertex n hn (Fin.last (3 * n + 2))) :=
  EnumeratedWalk.ofFnCycle (auxVertex n hn) (auxVertex_adj n hn) (aux_closing_adj n hn)

theorem auxiliaryCycle_isHamiltonianCycle (n : ℕ) (hn : 2 ≤ n) :
    (auxiliaryCycle n hn).IsHamiltonianCycle := by
  apply EnumeratedWalk.ofFnCycle_isHamiltonianCycle
  · omega
  · exact auxVertex_bijective n hn

theorem auxiliaryCycle_typeParity (n : ℕ) (hn : 2 ≤ n) :
    typeParity (show 3 ≤ n + 1 by omega) (auxiliaryCycle n hn) = 1 := by
  simp only [typeParity, CylinderSplice.edgeWeight, auxiliaryCycle,
    EnumeratedWalk.ofFnCycle_edges, List.map_cons, List.sum_cons,
    List.map_ofFn, Function.comp_def, auxVertex_edgeWeight_zero, aux_closing_weight]
  simp

theorem mem_auxiliaryCycle_edges (n : ℕ) (hn : 2 ≤ n) (e : Sym2 (Vertex (n + 1) 3)) :
    e ∈ (auxiliaryCycle n hn).edges ↔
      e = s(auxVertex n hn (Fin.last (3 * n + 2)), auxVertex n hn 0) ∨
        ∃ i : Fin (3 * n + 2), s(auxVertex n hn i.castSucc, auxVertex n hn i.succ) = e :=
  EnumeratedWalk.mem_ofFnCycle_edges _ _ _ e

theorem auxiliaryCycle_right_wrap_absent (n : ℕ) (hn : 2 ≤ n) :
    s((lastRow (n + 1) (by omega), (2 : Fin 3)),
      (firstRow (n + 1) (by omega), (2 : Fin 3))) ∉ (auxiliaryCycle n hn).edges := by
  rw [mem_auxiliaryCycle_edges]
  rintro (hc | ⟨i, hi⟩)
  · rw [auxVertex_first, auxVertex_last] at hc
    simp [Sym2.eq_iff, Prod.mk.injEq] at hc
  · have hw := auxVertex_edgeWeight_zero n hn i
    rw [hi, meridianWeight_last_first] at hw
    exact one_ne_zero hw

theorem auxiliaryCycle_left_zero_absent (n : ℕ) (hn : 2 ≤ n) :
    s((firstRow (n + 1) (by omega), (0 : Fin 3)),
      ((⟨1, by omega⟩ : Fin (n + 1)), (0 : Fin 3))) ∉ (auxiliaryCycle n hn).edges := by
  rw [mem_auxiliaryCycle_edges]
  rintro (hc | ⟨i, hi⟩)
  · rw [auxVertex_first, auxVertex_last] at hc
    rcases Sym2.eq_iff.mp hc with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · have hr := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h₁
      simp only [lastRow] at hr
      omega
    · have hr := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h₁
      simp only [firstRow] at hr
      omega
  · have hiLt := i.isLt
    rcases Sym2.eq_iff.mp hi with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;>
      have hr₀ := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h₀ <;>
      have hr₁ := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h₁ <;>
      have hc₀ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₀ <;>
      have hc₁ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₁ <;>
      unfold auxVertex at hr₀ hr₁ hc₀ hc₁ <;>
      simp only [Fin.coe_castSucc, Fin.val_succ] at hr₀ hr₁ hc₀ hc₁ <;>
      split_ifs at hr₀ hr₁ hc₀ hc₁ <;> simp_all [firstRow] <;> omega

theorem auxiliaryCycle_left_edge_of_nonzero (n : ℕ) (hn : 2 ≤ n)
    (r s : Fin (n + 1)) (hgap : NextRow r s)
    (hne : r ≠ firstRow (n + 1) (by omega)) :
    s((r, (0 : Fin 3)), (s, (0 : Fin 3))) ∈ (auxiliaryCycle n hn).edges := by
  rw [mem_auxiliaryCycle_edges]
  have hr := r.isLt
  have hs := s.isLt
  have hr0 : 0 < r.val := by
    have hneval : r.val ≠ 0 := fun h => hne (Fin.ext h)
    omega
  rcases nextRow_cases hgap with hstep | ⟨hwrap, hs0⟩
  · right
    refine ⟨⟨n - r.val - 1, by omega⟩, ?_⟩
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext <;>
      simp only [auxVertex, Fin.coe_castSucc, Fin.val_succ] <;>
      split_ifs <;> simp_all <;> omega
  · left
    rw [auxVertex_first, auxVertex_last]
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext
    · apply Fin.ext
      exact hwrap
    · rfl
    · apply Fin.ext
      exact hs0
    · rfl

theorem auxiliaryCycle_right_edge_of_not_last (n : ℕ) (hn : 2 ≤ n)
    (r s : Fin (n + 1)) (hgap : NextRow r s)
    (hne : r ≠ lastRow (n + 1) (by omega)) :
    s((r, (2 : Fin 3)), (s, (2 : Fin 3))) ∈ (auxiliaryCycle n hn).edges := by
  rw [mem_auxiliaryCycle_edges]
  have hr := r.isLt
  have hs := s.isLt
  have hrn : r.val < n := by
    have hneval : r.val ≠ n := fun h => hne (Fin.ext h)
    omega
  have hstep : r.val + 1 = s.val := by
    rcases nextRow_cases hgap with h | ⟨h, _⟩
    · exact h
    · omega
  right
  refine ⟨⟨3 * n - r.val - 1, by omega⟩, ?_⟩
  apply Sym2.eq_iff.mpr
  right
  constructor <;> apply Prod.ext <;> apply Fin.ext <;>
    simp only [auxVertex, Fin.coe_castSucc, Fin.val_succ] <;>
    split_ifs <;> simp_all <;> omega

/-- The left boundary selects every vertical gap except the first gap. -/
theorem auxiliaryCycle_left_edges_iff (n : ℕ) (hn : 2 ≤ n)
    (r s : Fin (n + 1)) (hgap : NextRow r s) :
    s((r, (0 : Fin 3)), (s, (0 : Fin 3))) ∈ (auxiliaryCycle n hn).edges ↔
      r ≠ firstRow (n + 1) (by omega) := by
  constructor
  · intro hmem hfirst
    have hr0 : r.val = 0 := congrArg Fin.val hfirst
    have hs1 : s.val = 1 := by
      rcases nextRow_cases hgap with h | ⟨h, _⟩ <;> omega
    have hs : s = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext hs1
    rw [hfirst, hs] at hmem
    exact auxiliaryCycle_left_zero_absent n hn hmem
  · exact auxiliaryCycle_left_edge_of_nonzero n hn r s hgap

/-- The right boundary selects every vertical gap except the wrap gap. -/
theorem auxiliaryCycle_right_edges_iff (n : ℕ) (hn : 2 ≤ n)
    (r s : Fin (n + 1)) (hgap : NextRow r s) :
    s((r, (2 : Fin 3)), (s, (2 : Fin 3))) ∈ (auxiliaryCycle n hn).edges ↔
      r ≠ lastRow (n + 1) (by omega) := by
  constructor
  · intro hmem hlast
    have hs := nextRow_target_first_of_source_last (show 3 ≤ n + 1 by omega) hgap hlast
    rw [hlast, hs] at hmem
    exact auxiliaryCycle_right_wrap_absent n hn hmem
  · exact auxiliaryCycle_right_edge_of_not_last n hn r s hgap

/-- Every circumference at least three has the actual three-column auxiliary
with parity one and the two exact boundary-gap properties.  The conclusion is
combinatorial and does not assume the annular parity/contractibility theorem. -/
theorem exists_three_column_auxiliary (m : ℕ) (hm : 3 ≤ m) :
    ∃ v : Vertex m 3, ∃ C : (graph m 3 hm).Walk v v,
      C.IsHamiltonianCycle ∧ typeParity hm C = 1 ∧
      (∀ r s : Fin m, NextRow r s →
        (s((r, (0 : Fin 3)), (s, (0 : Fin 3))) ∈ C.edges ↔ r ≠ firstRow m hm)) ∧
      (∀ r s : Fin m, NextRow r s →
        (s((r, (2 : Fin 3)), (s, (2 : Fin 3))) ∈ C.edges ↔ r ≠ lastRow m hm)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  refine ⟨_, auxiliaryCycle n hn, auxiliaryCycle_isHamiltonianCycle n hn,
    auxiliaryCycle_typeParity n hn, ?_, ?_⟩
  · intro r s hgap
    exact auxiliaryCycle_left_edges_iff n hn r s hgap
  · intro r s hgap
    exact auxiliaryCycle_right_edges_iff n hn r s hgap

#print axioms auxiliaryCycle_isHamiltonianCycle
#print axioms auxiliaryCycle_typeParity
#print axioms auxiliaryCycle_left_edges_iff
#print axioms auxiliaryCycle_right_edges_iff
#print axioms exists_three_column_auxiliary

end TriangularCylinder
