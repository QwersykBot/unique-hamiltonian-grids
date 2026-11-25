import RowRotation
import SelectedCylinderSplice

/-!
# Aligned actual auxiliary cycles in either meridian parity class

Parity one uses the frozen rotated three-column auxiliary. Parity zero
splices two such auxiliaries at the same fixed internal cyclic gap. The
exact splice edge-set formula proves that both prescribed outer edges
survive, since they are in columns different from the two deleted edges.
No boundary-state, support-connectivity, or return claim is made here.
-/

namespace TriangularCylinder

open SimpleGraph

private theorem vertical_pairs_ne_of_columns_ne {m L : ℕ}
    (r s q t : Fin m) (c d : Fin L) (hcd : c ≠ d) :
    s((r, c), (s, c)) ≠ s((q, d), (t, d)) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨hfirst, _⟩ | ⟨hfirst, _⟩
  · exact hcd (congrArg Prod.snd hfirst)
  · exact hcd (congrArg Prod.snd hfirst)

/-- Two aligned parity-one auxiliaries give an actual width-six parity-zero
cycle retaining any prescribed cyclic gaps at its two outer columns. -/
theorem exists_aligned_six_column_zero_auxiliary (m : ℕ) (hm : 3 ≤ m)
    (r s q t : Fin m) (hleftGap : NextRow r s) (hrightGap : NextRow q t) :
    ∃ v : Vertex m 6, ∃ C : (graph m 6 hm).Walk v v,
      C.IsHamiltonianCycle ∧ typeParity hm C = 0 ∧
      s((r, (0 : Fin 6)), (s, (0 : Fin 6))) ∈ C.edges ∧
      s((q, (5 : Fin 6)), (t, (5 : Fin 6))) ∈ C.edges := by
  let x := lastRow m hm
  let y := firstRow m hm
  have hxy : NextRow x y := nextRow_last_first hm
  obtain ⟨u, A, hA, hAp, hAleft, hAinner⟩ :=
    exists_aligned_three_column_auxiliary m hm r s x y hleftGap hxy
  obtain ⟨v, B, hB, hBp, hBinner, hBright⟩ :=
    exists_aligned_three_column_auxiliary m hm x y q t hxy hrightGap
  obtain ⟨J, hJ, hJp, hJedges⟩ := exists_splice_of_selected_edges hm
    (by decide : 2 ≤ 3) (by decide : 2 ≤ 3) x y hxy A B hA hB hAinner hBinner
  have hleftMap : s((r, (0 : Fin 6)), (s, (0 : Fin 6))) ∈
      (A.map (leftHom (a := 3) (b := 3) hm)).edgeSet := by
    rw [Walk.edgeSet_map]
    refine ⟨s((r, (0 : Fin 3)), (s, (0 : Fin 3))), hAleft, ?_⟩
    rw [Sym2.map_pair_eq]
    rfl
  have hrightMap : s((q, (5 : Fin 6)), (t, (5 : Fin 6))) ∈
      (B.map (rightHom (a := 3) (b := 3) hm)).edgeSet := by
    rw [Walk.edgeSet_map]
    refine ⟨s((q, (2 : Fin 3)), (t, (2 : Fin 3))), hBright, ?_⟩
    rw [Sym2.map_pair_eq]
    rfl
  have hleftNe : s((r, (0 : Fin 6)), (s, (0 : Fin 6))) ≠
      s(leftVertex 3 (x, lastCol 3 (by decide)), leftVertex 3 (y, lastCol 3 (by decide))) := by
    change s((r, (0 : Fin 6)), (s, (0 : Fin 6))) ≠ s((x, (2 : Fin 6)), (y, (2 : Fin 6)))
    exact vertical_pairs_ne_of_columns_ne r s x y 0 2 (by decide)
  have hrightNe : s((q, (5 : Fin 6)), (t, (5 : Fin 6))) ≠
      s(rightVertex 3 (y, firstCol 3 (by decide)), rightVertex 3 (x, firstCol 3 (by decide))) := by
    change s((q, (5 : Fin 6)), (t, (5 : Fin 6))) ≠ s((y, (3 : Fin 6)), (x, (3 : Fin 6)))
    exact vertical_pairs_ne_of_columns_ne q t y x 5 3 (by decide)
  refine ⟨_, J, hJ, ?_, ?_, ?_⟩
  · simpa only [hAp, hBp, ZModModule.add_self] using hJp
  · change s((r, (0 : Fin 6)), (s, (0 : Fin 6))) ∈ J.edgeSet
    rw [hJedges]
    exact Or.inr (Or.inr (Or.inl ⟨hleftMap, hleftNe⟩))
  · change s((q, (5 : Fin 6)), (t, (5 : Fin 6))) ∈ J.edgeSet
    rw [hJedges]
    exact Or.inr (Or.inr (Or.inr ⟨hrightMap, hrightNe⟩))

private theorem parity_two_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by
  have hfin : ∀ q : Fin 2, q = 0 ∨ q = 1 := by
    intro q
    by_cases hq : q.val = 0
    · exact Or.inl (Fin.ext hq)
    · right
      apply Fin.ext
      change q.val = 1
      have hq_lt : q.val < 2 := q.isLt
      omega
  exact hfin p

/-- Either existing meridian parity class has an actual aligned auxiliary
selecting both prescribed outer cyclic gaps. The proof uses width six for
parity zero and width three for parity one. -/
theorem exists_aligned_auxiliary_of_parity (m : ℕ) (hm : 3 ≤ m) (p : ZMod 2)
    (r s q t : Fin m) (hleftGap : NextRow r s) (hrightGap : NextRow q t) :
    ∃ a : ℕ, ∃ ha : 2 ≤ a, ∃ v : Vertex m a, ∃ C : (graph m a hm).Walk v v,
      C.IsHamiltonianCycle ∧ typeParity hm C = p ∧
      s((r, firstCol a ha), (s, firstCol a ha)) ∈ C.edges ∧
      s((q, lastCol a ha), (t, lastCol a ha)) ∈ C.edges := by
  rcases parity_two_cases p with rfl | rfl
  · obtain ⟨v, C, hC, hp, hl, hr⟩ :=
      exists_aligned_six_column_zero_auxiliary m hm r s q t hleftGap hrightGap
    exact ⟨6, by decide, v, C, hC, hp, hl, hr⟩
  · obtain ⟨v, C, hC, hp, hl, hr⟩ :=
      exists_aligned_three_column_auxiliary m hm r s q t hleftGap hrightGap
    exact ⟨3, by decide, v, C, hC, hp, hl, hr⟩

end TriangularCylinder
