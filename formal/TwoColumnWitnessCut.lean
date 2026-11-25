import TwoColumnWitness

/-! # Exact boundary and sole-cut data for the two-column perimeter -/

namespace TriangularCylinder

open SimpleGraph

def beforeLastRow (m : ℕ) (hm : 3 ≤ m) : Fin m := ⟨m - 2, by omega⟩

theorem nextRow_beforeLast_last {m : ℕ} (hm : 3 ≤ m) :
    NextRow (beforeLastRow m hm) (lastRow m hm) := by
  change m - 1 = (m - 2 + 1) % m
  have heq : m - 2 + 1 = m - 1 := by omega
  rw [heq, Nat.mod_eq_of_lt (by omega : m - 1 < m)]

theorem perimeterCycle_left_join_edge (n : ℕ) (hn : 2 ≤ n) :
    s((beforeLastRow (n + 1) (by omega), (0 : Fin 2)),
      (lastRow (n + 1) (by omega), (0 : Fin 2))) ∈ (perimeterCycle n hn).edges := by
  rw [mem_perimeterCycle_edges]
  right
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  apply Sym2.eq_iff.mpr
  left
  constructor <;> apply Prod.ext <;> apply Fin.ext
  all_goals simp only [perimeterVertex, Fin.coe_castSucc, Fin.val_succ]
  all_goals split_ifs
  all_goals simp_all [beforeLastRow, lastRow]
  all_goals omega

theorem perimeterCycle_right_join_edge (n : ℕ) (hn : 2 ≤ n) :
    s((beforeLastRow (n + 1) (by omega), (1 : Fin 2)),
      (lastRow (n + 1) (by omega), (1 : Fin 2))) ∈ (perimeterCycle n hn).edges := by
  rw [mem_perimeterCycle_edges]
  right
  refine ⟨⟨n + 1, by omega⟩, ?_⟩
  apply Sym2.eq_iff.mpr
  right
  constructor <;> apply Prod.ext <;> apply Fin.ext
  all_goals simp only [perimeterVertex, Fin.coe_castSucc, Fin.val_succ]
  all_goals split_ifs
  all_goals simp_all [beforeLastRow, lastRow]
  all_goals omega

theorem perimeterVertex_crossing_rows (n : ℕ) (hn : 2 ≤ n)
    (i : Fin (2 * n + 1)) (r s : Fin (n + 1))
    (he : s(perimeterVertex n hn i.castSucc, perimeterVertex n hn i.succ) =
      s((r, (0 : Fin 2)), (s, (1 : Fin 2)))) : r.val = n ∧ s.val = n := by
  have hi := i.isLt
  rcases Sym2.eq_iff.mp he with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  all_goals
    have hr₀ := congrArg (fun x : Vertex (n + 1) 2 => x.1.val) h₀
    have hr₁ := congrArg (fun x : Vertex (n + 1) 2 => x.1.val) h₁
    have hc₀ := congrArg (fun x : Vertex (n + 1) 2 => x.2.val) h₀
    have hc₁ := congrArg (fun x : Vertex (n + 1) 2 => x.2.val) h₁
    unfold perimeterVertex at hr₀ hr₁ hc₀ hc₁
    simp only [Fin.coe_castSucc, Fin.val_succ] at hr₀ hr₁ hc₀ hc₁
    split_ifs at hr₀ hr₁ hc₀ hc₁
    all_goals simp_all
    all_goals omega

/-- The sole cut has exactly the first- and last-row horizontal edges. -/
theorem perimeterCycle_lastCut_edges_iff (n : ℕ) (hn : 2 ≤ n)
    (r s : Fin (n + 1)) :
    s((r, (0 : Fin 2)), (s, (1 : Fin 2))) ∈ (perimeterCycle n hn).edges ↔
      r = s ∧ (r = firstRow (n + 1) (by omega) ∨ r = lastRow (n + 1) (by omega)) := by
  rw [mem_perimeterCycle_edges]
  constructor
  · rintro (hc | ⟨i, hi⟩)
    · rw [perimeterVertex_first, perimeterVertex_last] at hc
      rcases Sym2.eq_iff.mp hc with ⟨h₀, _⟩ | ⟨h₀, h₁⟩
      · have hc₀ := congrArg (fun x : Vertex (n + 1) 2 => x.2.val) h₀
        simp at hc₀
      · have hr := congrArg Prod.fst h₀
        have hs := congrArg Prod.fst h₁
        exact ⟨hr.trans hs.symm, Or.inl hr⟩
    · obtain ⟨hr, hs⟩ := perimeterVertex_crossing_rows n hn i r s hi
      refine ⟨Fin.ext (hr.trans hs.symm), Or.inr ?_⟩
      apply Fin.ext
      simpa [lastRow] using hr
  · rintro ⟨hrs, hr | hr⟩
    · subst s
      left
      rw [hr, perimeterVertex_first, perimeterVertex_last]
      exact Sym2.eq_swap
    · subst s
      right
      refine ⟨⟨n, by omega⟩, ?_⟩
      rw [hr]
      apply Sym2.eq_iff.mpr
      left
      constructor <;> apply Prod.ext <;> apply Fin.ext
      all_goals simp only [perimeterVertex, Fin.coe_castSucc, Fin.val_succ]
      all_goals split_ifs
      all_goals simp_all [lastRow]
      all_goals omega

theorem perimeterPrefix_adj (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (graph (n + 1) 2 (by omega)).Adj (i.castSucc, 0) (i.succ, 0) := by
  apply vertical_edge
  change i.val + 1 = (i.val + 1) % (n + 1)
  exact (Nat.mod_eq_of_lt i.succ.isLt).symm

/-- The processed first-column vertices form this single selected path. -/
def perimeterPrefixWalk (n : ℕ) (hn : 2 ≤ n) :
    (graph (n + 1) 2 (by omega)).Walk ((0 : Fin (n + 1)), 0) (Fin.last n, 0) :=
  EnumeratedWalk.ofFnWalk (fun i : Fin (n + 1) => (i, (0 : Fin 2))) (perimeterPrefix_adj n hn)

theorem perimeterPrefixWalk_isPath (n : ℕ) (hn : 2 ≤ n) :
    (perimeterPrefixWalk n hn).IsPath := by
  apply EnumeratedWalk.ofFnWalk_isPath
  intro i j h
  exact congrArg Prod.fst h

theorem perimeterPrefixWalk_support_iff (n : ℕ) (hn : 2 ≤ n) (x : Vertex (n + 1) 2) :
    x ∈ (perimeterPrefixWalk n hn).support ↔ x.2 = 0 := by
  rw [perimeterPrefixWalk, EnumeratedWalk.mem_ofFnWalk_support]
  constructor
  · rintro ⟨i, hi⟩
    exact (congrArg Prod.snd hi).symm
  · intro hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩

theorem perimeterPrefixWalk_edges (n : ℕ) (hn : 2 ≤ n) :
    (perimeterPrefixWalk n hn).edges =
      List.ofFn (fun i : Fin n => s((i.castSucc, (0 : Fin 2)), (i.succ, (0 : Fin 2)))) :=
  EnumeratedWalk.ofFnWalk_edges _ _

theorem perimeterPrefixWalk_edges_in_cycle (n : ℕ) (hn : 2 ≤ n)
    (e : Sym2 (Vertex (n + 1) 2)) (he : e ∈ (perimeterPrefixWalk n hn).edges) :
    e ∈ (perimeterCycle n hn).edges := by
  rw [perimeterPrefixWalk, EnumeratedWalk.mem_ofFnWalk_edges] at he
  obtain ⟨i, hi⟩ := he
  rw [mem_perimeterCycle_edges]
  right
  refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
  have h₀ : i.val < n + 1 := by have := i.isLt; omega
  have h₁ : i.val + 1 < n + 1 := by have := i.isLt; omega
  simpa only [perimeterVertex, Fin.coe_castSucc, Fin.val_succ, dif_pos h₀, dif_pos h₁] using hi

theorem perimeterPrefixWalk_typeParity (n : ℕ) (hn : 2 ≤ n) :
    typeParity (show 3 ≤ n + 1 by omega) (perimeterPrefixWalk n hn) = 0 := by
  have hzero : ∀ i : Fin n, meridianWeight (show 3 ≤ n + 1 by omega)
      s((i.castSucc, (0 : Fin 2)), (i.succ, (0 : Fin 2))) = 0 := by
    intro i
    apply meridianWeight_zero_of_close_rows <;> simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega
  simp only [typeParity, CylinderSplice.edgeWeight, perimeterPrefixWalk_edges,
    List.map_ofFn, Function.comp_def, hzero]
  simp

theorem perimeterVertex_left_iff (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n + 2)) :
    (perimeterVertex n hn i).2 = 0 ↔ i.val < n + 1 := by
  unfold perimeterVertex
  split_ifs <;> simp_all

/-- Within the processed column, the selected cycle edges are exactly the
edges of the displayed prefix path. -/
theorem perimeterPrefixWalk_pair_edges_iff (n : ℕ) (hn : 2 ≤ n)
    (x y : Vertex (n + 1) 2) (hx : x.2 = 0) (hy : y.2 = 0) :
    s(x, y) ∈ (perimeterPrefixWalk n hn).edges ↔ s(x, y) ∈ (perimeterCycle n hn).edges := by
  constructor
  · exact perimeterPrefixWalk_edges_in_cycle n hn _
  · intro he
    rw [mem_perimeterCycle_edges] at he
    rcases he with hclose | ⟨i, hi⟩
    · rw [perimeterVertex_first, perimeterVertex_last] at hclose
      rcases Sym2.eq_iff.mp hclose with ⟨h₀, _⟩ | ⟨_, h₁⟩
      · have hc := congrArg Prod.snd h₀
        rw [hx] at hc
        exact False.elim (by cases hc)
      · have hc := congrArg Prod.snd h₁
        rw [hy] at hc
        exact False.elim (by cases hc)
    · have hleft : (perimeterVertex n hn i.succ).2 = 0 := by
        rcases Sym2.eq_iff.mp hi with ⟨_, h₁⟩ | ⟨_, h₁⟩
        · exact (congrArg Prod.snd h₁).trans hy
        · exact (congrArg Prod.snd h₁).trans hx
      have hlt := (perimeterVertex_left_iff n hn i.succ).mp hleft
      have hiLt : i.val < n := by simp only [Fin.val_succ] at hlt; omega
      rw [perimeterPrefixWalk, EnumeratedWalk.mem_ofFnWalk_edges]
      refine ⟨⟨i.val, hiLt⟩, ?_⟩
      have h₀ : i.val < n + 1 := by omega
      have h₁ : i.val + 1 < n + 1 := by omega
      simpa only [perimeterVertex, Fin.coe_castSucc, Fin.val_succ, dif_pos h₀, dif_pos h₁] using hi

/-- An actual all-width witness with parity zero, the common joining gap,
and exactly the two required frontier crossings. -/
theorem exists_two_column_zero_witness (m : ℕ) (hm : 3 ≤ m) :
    ∃ v : Vertex m 2, ∃ C : (graph m 2 hm).Walk v v,
      C.IsHamiltonianCycle ∧ typeParity hm C = 0 ∧
      s((beforeLastRow m hm, (0 : Fin 2)), (lastRow m hm, (0 : Fin 2))) ∈ C.edges ∧
      s((beforeLastRow m hm, (1 : Fin 2)), (lastRow m hm, (1 : Fin 2))) ∈ C.edges ∧
      (∀ r s : Fin m,
        s((r, (0 : Fin 2)), (s, (1 : Fin 2))) ∈ C.edges ↔
          r = s ∧ (r = firstRow m hm ∨ r = lastRow m hm)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  exact ⟨_, perimeterCycle n hn, perimeterCycle_isHamiltonianCycle n hn,
    perimeterCycle_typeParity n hn, perimeterCycle_left_join_edge n hn,
    perimeterCycle_right_join_edge n hn, perimeterCycle_lastCut_edges_iff n hn⟩

end TriangularCylinder
