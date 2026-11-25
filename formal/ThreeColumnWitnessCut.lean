import ThreeColumnWitness
import TwoColumnWitnessCut

/-! # Exact boundary and last-cut data for the three-column witness -/

namespace TriangularCylinder

open SimpleGraph

theorem threeWitnessVertex_prefix_iff (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 3)) :
    (threeWitnessVertex n hn i).2.val < 2 ↔ i.val < 2 * n + 2 := by
  have hcol := threePrefixColumn_le_one n i.val
  unfold threeWitnessVertex
  split_ifs
  all_goals simp_all
  all_goals omega

theorem threeWitnessVertex_right_iff (n : ℕ) (hn : 2 ≤ n) (i : Fin (3 * n + 3)) :
    (threeWitnessVertex n hn i).2.val = 2 ↔ 2 * n + 2 ≤ i.val := by
  have hcol := threePrefixColumn_le_one n i.val
  unfold threeWitnessVertex
  split_ifs
  all_goals simp_all
  all_goals omega

theorem threeWitnessCycle_left_join_edge (n : ℕ) (hn : 2 ≤ n) :
    s((beforeLastRow (n + 1) (by omega), (0 : Fin 3)),
      (lastRow (n + 1) (by omega), (0 : Fin 3))) ∈ (threeWitnessCycle n hn).edges := by
  rw [mem_threeWitnessCycle_edges]
  right
  refine ⟨⟨2 * n - 1, by omega⟩, ?_⟩
  apply Sym2.eq_iff.mpr
  left
  constructor <;> apply Prod.ext <;> apply Fin.ext
  all_goals simp only [threeWitnessVertex, threePrefixColumn, Fin.coe_castSucc, Fin.val_succ]
  all_goals split_ifs
  all_goals simp_all [beforeLastRow, lastRow]
  all_goals omega

theorem threeWitnessCycle_right_join_edge (n : ℕ) (hn : 2 ≤ n) :
    s((beforeLastRow (n + 1) (by omega), (2 : Fin 3)),
      (lastRow (n + 1) (by omega), (2 : Fin 3))) ∈ (threeWitnessCycle n hn).edges := by
  rw [mem_threeWitnessCycle_edges]
  right
  refine ⟨⟨2 * n + 2, by omega⟩, ?_⟩
  apply Sym2.eq_iff.mpr
  right
  constructor <;> apply Prod.ext <;> apply Fin.ext
  all_goals simp only [threeWitnessVertex, threePrefixColumn, Fin.coe_castSucc, Fin.val_succ]
  all_goals split_ifs
  all_goals simp_all [beforeLastRow, lastRow]
  all_goals omega

theorem threeWitnessVertex_crossing_rows (n : ℕ) (hn : 2 ≤ n)
    (i : Fin (3 * n + 2)) (r s : Fin (n + 1))
    (he : s(threeWitnessVertex n hn i.castSucc, threeWitnessVertex n hn i.succ) =
      s((r, (1 : Fin 3)), (s, (2 : Fin 3)))) : r.val = n ∧ s.val = n := by
  have hi := i.isLt
  rcases Sym2.eq_iff.mp he with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · have hc₀ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₀
    have hc₁ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₁
    have hleft : i.val < 2 * n + 2 :=
      (threeWitnessVertex_prefix_iff n hn i.castSucc).mp (by simpa only [hc₀] using (by decide : (1 : ℕ) < 2))
    have hright : 2 * n + 2 ≤ i.val + 1 :=
      (threeWitnessVertex_right_iff n hn i.succ).mp hc₁
    have hright' : ¬ i.val + 1 < 2 * n + 2 := by omega
    have hr₀ := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h₀
    have hr₁ := congrArg (fun x : Vertex (n + 1) 3 => x.1.val) h₁
    simp only [threeWitnessVertex, Fin.coe_castSucc, Fin.val_succ,
      dif_pos hleft, dif_neg hright'] at hr₀ hr₁
    omega
  · have hc₀ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₀
    have hc₁ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₁
    have hright : 2 * n + 2 ≤ i.val :=
      (threeWitnessVertex_right_iff n hn i.castSucc).mp hc₀
    have hleft : i.val + 1 < 2 * n + 2 :=
      (threeWitnessVertex_prefix_iff n hn i.succ).mp (by simpa only [hc₁] using (by decide : (1 : ℕ) < 2))
    omega

/-- The last cut has exactly the first- and last-row horizontal edges.
In particular it has no selected diagonal crossing. -/
theorem threeWitnessCycle_lastCut_edges_iff (n : ℕ) (hn : 2 ≤ n)
    (r s : Fin (n + 1)) :
    s((r, (1 : Fin 3)), (s, (2 : Fin 3))) ∈ (threeWitnessCycle n hn).edges ↔
      r = s ∧ (r = firstRow (n + 1) (by omega) ∨ r = lastRow (n + 1) (by omega)) := by
  rw [mem_threeWitnessCycle_edges]
  constructor
  · rintro (hc | ⟨i, hi⟩)
    · rw [threeWitnessVertex_first, threeWitnessVertex_last] at hc
      rcases Sym2.eq_iff.mp hc with ⟨h₀, _⟩ | ⟨h₀, h₁⟩
      · have hc₀ := congrArg (fun x : Vertex (n + 1) 3 => x.2.val) h₀
        simp at hc₀
      · have hr := congrArg Prod.fst h₀
        have hs := congrArg Prod.fst h₁
        exact ⟨hr.trans hs.symm, Or.inl hr⟩
    · obtain ⟨hr, hs⟩ := threeWitnessVertex_crossing_rows n hn i r s hi
      refine ⟨Fin.ext (hr.trans hs.symm), Or.inr ?_⟩
      apply Fin.ext
      simpa [lastRow] using hr
  · rintro ⟨hrs, hr | hr⟩
    · subst s
      left
      rw [hr, threeWitnessVertex_first, threeWitnessVertex_last]
      exact Sym2.eq_swap
    · subst s
      right
      refine ⟨⟨2 * n + 1, by omega⟩, ?_⟩
      rw [hr]
      apply Sym2.eq_iff.mpr
      left
      constructor <;> apply Prod.ext <;> apply Fin.ext
      all_goals simp only [threeWitnessVertex, threePrefixColumn, Fin.coe_castSucc, Fin.val_succ]
      all_goals split_ifs
      all_goals simp_all [lastRow]
      all_goals omega

/-- The first `2(n+1)` entries are the processed left/middle path. -/
def threePrefixVertex (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 2)) : Vertex (n + 1) 3 :=
  threeWitnessVertex n hn ⟨i.val, by have := i.isLt; omega⟩

theorem threePrefixVertex_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (threePrefixVertex n hn) := by
  intro i j h
  have heq := threeWitnessVertex_injective n hn h
  apply Fin.ext
  exact congrArg (fun k : Fin (3 * n + 3) => k.val) heq

theorem threePrefixVertex_adj (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 1)) :
    (graph (n + 1) 3 (by omega)).Adj
      (threePrefixVertex n hn i.castSucc) (threePrefixVertex n hn i.succ) :=
  threeWitnessVertex_adj n hn ⟨i.val, by have := i.isLt; omega⟩

theorem threePrefixVertex_first (n : ℕ) (hn : 2 ≤ n) :
    threePrefixVertex n hn 0 = (firstRow (n + 1) (by omega), 1) :=
  threeWitnessVertex_first n hn

theorem threePrefixVertex_last (n : ℕ) (hn : 2 ≤ n) :
    threePrefixVertex n hn (Fin.last (2 * n + 1)) =
      (lastRow (n + 1) (by omega), 1) := by
  apply Prod.ext <;> apply Fin.ext
  all_goals simp only [threePrefixVertex, threeWitnessVertex, threePrefixColumn, Fin.val_last]
  all_goals split_ifs
  all_goals simp_all [lastRow]
  all_goals omega

def threePrefixWalk (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 3 (by omega)).Walk
      (threePrefixVertex n hn 0) (threePrefixVertex n hn (Fin.last (2 * n + 1))) :=
  EnumeratedWalk.ofFnWalk (threePrefixVertex n hn) (threePrefixVertex_adj n hn)

theorem threePrefixWalk_isPath (n : ℕ) (hn : 2 ≤ n) :
    (threePrefixWalk n hn).IsPath :=
  EnumeratedWalk.ofFnWalk_isPath _ _ (threePrefixVertex_injective n hn)

theorem threePrefixWalk_support_iff (n : ℕ) (hn : 2 ≤ n) (x : Vertex (n + 1) 3) :
    x ∈ (threePrefixWalk n hn).support ↔ x.2.val < 2 := by
  rw [threePrefixWalk, EnumeratedWalk.mem_ofFnWalk_support]
  constructor
  · rintro ⟨i, hi⟩
    rw [← hi]
    exact (threeWitnessVertex_prefix_iff n hn _).mpr i.isLt
  · intro hx
    obtain ⟨j, hj⟩ := (threeWitnessVertex_bijective n hn).surjective x
    have hjlt : j.val < 2 * n + 2 :=
      (threeWitnessVertex_prefix_iff n hn j).mp (by simpa only [hj] using hx)
    exact ⟨⟨j.val, hjlt⟩, hj⟩

theorem threePrefixWalk_edges (n : ℕ) (hn : 2 ≤ n) :
    (threePrefixWalk n hn).edges = List.ofFn (fun i : Fin (2 * n + 1) =>
      s(threePrefixVertex n hn i.castSucc, threePrefixVertex n hn i.succ)) :=
  EnumeratedWalk.ofFnWalk_edges _ _

theorem threePrefixWalk_edges_in_cycle (n : ℕ) (hn : 2 ≤ n)
    (e : Sym2 (Vertex (n + 1) 3)) (he : e ∈ (threePrefixWalk n hn).edges) :
    e ∈ (threeWitnessCycle n hn).edges := by
  rw [threePrefixWalk, EnumeratedWalk.mem_ofFnWalk_edges] at he
  obtain ⟨i, hi⟩ := he
  rw [mem_threeWitnessCycle_edges]
  right
  exact ⟨⟨i.val, by have := i.isLt; omega⟩, hi⟩

theorem threePrefixWalk_typeParity (n : ℕ) (hn : 2 ≤ n) :
    typeParity (show 3 ≤ n + 1 by omega) (threePrefixWalk n hn) = 0 := by
  have hzero : ∀ i : Fin (2 * n + 1), meridianWeight (show 3 ≤ n + 1 by omega)
      s(threePrefixVertex n hn i.castSucc, threePrefixVertex n hn i.succ) = 0 := by
    intro i
    exact threeWitnessVertex_edgeWeight_zero n hn ⟨i.val, by have := i.isLt; omega⟩
  simp only [typeParity, CylinderSplice.edgeWeight, threePrefixWalk_edges,
    List.map_ofFn, Function.comp_def, hzero]
  simp

/-- Within the processed left/middle columns, the selected cycle edges are
exactly the edges of the displayed spanning prefix path. -/
theorem threePrefixWalk_pair_edges_iff (n : ℕ) (hn : 2 ≤ n)
    (x y : Vertex (n + 1) 3) (hx : x.2.val < 2) (hy : y.2.val < 2) :
    s(x, y) ∈ (threePrefixWalk n hn).edges ↔ s(x, y) ∈ (threeWitnessCycle n hn).edges := by
  constructor
  · exact threePrefixWalk_edges_in_cycle n hn _
  · intro he
    rw [mem_threeWitnessCycle_edges] at he
    rcases he with hclose | ⟨i, hi⟩
    · rw [threeWitnessVertex_first, threeWitnessVertex_last] at hclose
      rcases Sym2.eq_iff.mp hclose with ⟨h₀, _⟩ | ⟨_, h₁⟩
      · have hc := congrArg (fun z : Vertex (n + 1) 3 => z.2.val) h₀
        simp only at hc
        omega
      · have hc := congrArg (fun z : Vertex (n + 1) 3 => z.2.val) h₁
        simp only at hc
        omega
    · have hleft : (threeWitnessVertex n hn i.succ).2.val < 2 := by
        rcases Sym2.eq_iff.mp hi with ⟨_, h₁⟩ | ⟨_, h₁⟩
        · simpa only [h₁] using hy
        · simpa only [h₁] using hx
      have hlt := (threeWitnessVertex_prefix_iff n hn i.succ).mp hleft
      have hiLt : i.val < 2 * n + 1 := by simp only [Fin.val_succ] at hlt; omega
      rw [threePrefixWalk, EnumeratedWalk.mem_ofFnWalk_edges]
      exact ⟨⟨i.val, hiLt⟩, hi⟩

/-- An actual all-width witness with parity zero, the common joining gap,
and exactly the two required last-cut crossings. -/
theorem exists_three_column_zero_witness (m : ℕ) (hm : 3 ≤ m) :
    ∃ v : Vertex m 3, ∃ C : (graph m 3 hm).Walk v v,
      C.IsHamiltonianCycle ∧ typeParity hm C = 0 ∧
      s((beforeLastRow m hm, (0 : Fin 3)), (lastRow m hm, (0 : Fin 3))) ∈ C.edges ∧
      s((beforeLastRow m hm, (2 : Fin 3)), (lastRow m hm, (2 : Fin 3))) ∈ C.edges ∧
      (∀ r s : Fin m,
        s((r, (1 : Fin 3)), (s, (2 : Fin 3))) ∈ C.edges ↔
          r = s ∧ (r = firstRow m hm ∨ r = lastRow m hm)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  exact ⟨_, threeWitnessCycle n hn, threeWitnessCycle_isHamiltonianCycle n hn,
    threeWitnessCycle_typeParity n hn, threeWitnessCycle_left_join_edge n hn,
    threeWitnessCycle_right_join_edge n hn, threeWitnessCycle_lastCut_edges_iff n hn⟩

end TriangularCylinder
