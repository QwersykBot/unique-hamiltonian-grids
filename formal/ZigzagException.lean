import ColumnHamiltonian
import ColumnWeights

/-!
# The all-crossing two-column triangular zigzag

This file constructs the exact geometry with no vertical edges and all
horizontal and diagonal edges. It proves connectedness, two neighbors at
every vertex, a counted Hamiltonian selection, and meridian parity one.
It makes no transfer-state or state-isolation claim.
-/

namespace TriangularZigzag

open SimpleGraph TriangularCylinder TriangularEdgeEncoding CountedHamiltonian
open scoped BigOperators

def geometry (m : ℕ) : ColumnGeometry m 2 :=
  (fun _ _ => false, (fun _ _ => true, fun _ _ => true))

def selectedGraph {m : ℕ} (hm : 3 ≤ m) : SimpleGraph (Vertex m 2) :=
  fromEdgeSet (realizedEdges hm (geometry m) : Set (Sym2 (Vertex m 2)))

def left {m : ℕ} (r : Fin m) : Vertex m 2 := (r, 0)
def right {m : ℕ} (r : Fin m) : Vertex m 2 := (r, 1)

theorem horizontal_toEdge {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    toEdge hm (.inr (.inl (r, (0 : Fin (2 - 1))))) = s(left r, right r) := rfl

theorem diagonal_toEdge {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    toEdge hm (.inr (.inr (r, (0 : Fin (2 - 1))))) =
      s(left r, right (rowSucc hm r)) := rfl

theorem mem_realizedEdges {m : ℕ} (hm : 3 ≤ m) (e : Sym2 (Vertex m 2)) :
    e ∈ realizedEdges hm (geometry m) ↔
      (∃ r, e = s(left r, right r)) ∨
      (∃ r, e = s(left r, right (rowSucc hm r))) := by
  constructor
  · intro he
    obtain ⟨id, hid, heq⟩ := Finset.mem_image.mp he
    rcases id with ⟨r, c⟩ | (⟨r, c⟩ | ⟨r, c⟩)
    · simp [mem_idsOfGeometry, geometryFlag, geometry] at hid
    · have hc : c = (0 : Fin (2 - 1)) := by
        apply Fin.ext
        have hlt := c.isLt
        omega
      subst c
      exact Or.inl ⟨r, heq.symm.trans (horizontal_toEdge hm r)⟩
    · have hc : c = (0 : Fin (2 - 1)) := by
        apply Fin.ext
        have hlt := c.isLt
        omega
      subst c
      exact Or.inr ⟨r, heq.symm.trans (diagonal_toEdge hm r)⟩
  · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · apply Finset.mem_image.mpr
      exact ⟨.inr (.inl (r, 0)), by simp [mem_idsOfGeometry, geometryFlag, geometry],
        horizontal_toEdge hm r⟩
    · apply Finset.mem_image.mpr
      exact ⟨.inr (.inr (r, 0)), by simp [mem_idsOfGeometry, geometryFlag, geometry],
        diagonal_toEdge hm r⟩

theorem selectedGraph_adj {m : ℕ} (hm : 3 ≤ m) (x y : Vertex m 2) :
    (selectedGraph hm).Adj x y ↔
      (∃ r, s(x, y) = s(left r, right r)) ∨
      (∃ r, s(x, y) = s(left r, right (rowSucc hm r))) := by
  constructor
  · intro h
    exact (mem_realizedEdges hm _).mp h.1
  · intro h
    have he := (mem_realizedEdges hm _).mpr h
    exact ⟨he, ((SimpleGraph.mem_edgeSet (graph m 2 hm)).mp
      (realizedEdges_mem hm (geometry m) he)).ne⟩

theorem adj_left {m : ℕ} (hm : 3 ≤ m) (r : Fin m) (v : Vertex m 2) :
    (selectedGraph hm).Adj (left r) v ↔
      v = right r ∨ v = right (rowSucc hm r) := by
  rcases v with ⟨s, c⟩
  rw [selectedGraph_adj]
  simp [Sym2.eq_iff, left, right, Prod.mk.injEq, eq_comm, and_left_comm]

theorem adj_right {m : ℕ} (hm : 3 ≤ m) (r : Fin m) (v : Vertex m 2) :
    (selectedGraph hm).Adj (right r) v ↔
      v = left r ∨ ∃ s, rowSucc hm s = r ∧ v = left s := by
  rcases v with ⟨s, c⟩
  rw [selectedGraph_adj]
  simp [Sym2.eq_iff, left, right, Prod.mk.injEq, eq_comm, and_left_comm]

theorem rowSucc_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (rowSucc hm) := by
  intro r s h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (r.val + 1) % m = (s.val + 1) % m at hv
  have hr := r.isLt
  have hs := s.isLt
  by_cases hrl : r.val + 1 < m
  · rw [Nat.mod_eq_of_lt hrl] at hv
    by_cases hsl : s.val + 1 < m
    · rw [Nat.mod_eq_of_lt hsl] at hv
      omega
    · have heq : s.val + 1 = m := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  · have heq : r.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at hv
    by_cases hsl : s.val + 1 < m
    · rw [Nat.mod_eq_of_lt hsl] at hv
      omega
    · omega

theorem neighborSet_left {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    (selectedGraph hm).neighborSet (left r) =
      {right r, right (rowSucc hm r)} := by
  ext v
  simp only [mem_neighborSet, adj_left, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem neighborSet_right {m : ℕ} (hm : 3 ≤ m) (r s : Fin m)
    (hs : rowSucc hm s = r) :
    (selectedGraph hm).neighborSet (right r) = {left r, left s} := by
  ext v
  rw [mem_neighborSet, adj_right]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | ⟨t, ht, hv⟩)
    · exact Or.inl h
    · have hts : t = s := rowSucc_injective hm (ht.trans hs.symm)
      exact Or.inr (hts ▸ hv)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, h⟩

theorem neighborSet_ncard_two {m : ℕ} (hm : 3 ≤ m) (v : Vertex m 2) :
    ((selectedGraph hm).neighborSet v).ncard = 2 := by
  rcases v with ⟨r, c⟩
  have hc : c.val = 0 ∨ c.val = 1 := by have h := c.isLt; omega
  rcases hc with hc | hc
  · have hzero : c = (0 : Fin 2) := Fin.ext hc
    subst c
    rw [show (r, (0 : Fin 2)) = left r from rfl, neighborSet_left]
    apply Set.ncard_pair
    intro h
    exact nextRow_ne hm (nextRow_rowSucc hm r) (congrArg Prod.fst h)
  · have hone : c = (1 : Fin 2) := Fin.ext hc
    subst c
    obtain ⟨s, hs⟩ := Finite.surjective_of_injective (rowSucc_injective hm) r
    rw [show (r, (1 : Fin 2)) = right r from rfl, neighborSet_right hm r s hs]
    apply Set.ncard_pair
    intro h
    have hrs : r = s := congrArg Prod.fst h
    exact nextRow_ne hm (nextRow_rowSucc hm s) (hrs.symm.trans hs.symm)

theorem reachable_left {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    (selectedGraph hm).Reachable (left ⟨0, by omega⟩) (left r) := by
  suffices ∀ k (hk : k < m),
      (selectedGraph hm).Reachable (left ⟨0, by omega⟩) (left ⟨k, hk⟩) from
    this r.val r.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    exact Reachable.rfl
  | succ k ih =>
    intro hk
    have hkm : k < m := by omega
    have hsucc : rowSucc hm (⟨k, hkm⟩ : Fin m) = ⟨k + 1, hk⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hk
    have hd := (adj_left hm (⟨k, hkm⟩ : Fin m) (right (rowSucc hm ⟨k, hkm⟩))).mpr
      (Or.inr rfl)
    have hh := (adj_left hm (rowSucc hm ⟨k, hkm⟩) (right (rowSucc hm ⟨k, hkm⟩))).mpr
      (Or.inl rfl)
    have hpath := (ih hkm).trans (hd.reachable.trans hh.reachable.symm)
    simpa only [hsucc] using hpath

theorem connected {m : ℕ} (hm : 3 ≤ m) : (selectedGraph hm).Connected := by
  apply (connected_iff_exists_forall_reachable (selectedGraph hm)).mpr
  refine ⟨left ⟨0, by omega⟩, ?_⟩
  rintro ⟨r, c⟩
  have hc : c.val = 0 ∨ c.val = 1 := by have h := c.isLt; omega
  rcases hc with hc | hc
  · have hzero : c = (0 : Fin 2) := Fin.ext hc
    subst c
    exact reachable_left hm r
  · have hone : c = (1 : Fin 2) := Fin.ext hc
    subst c
    exact (reachable_left hm r).trans ((adj_left hm r (right r)).mpr (Or.inl rfl)).reachable

theorem isHamiltonianGeometry {m : ℕ} (hm : 3 ≤ m) :
    IsHamiltonianGeometry hm (geometry m) :=
  ⟨connected hm, neighborSet_ncard_two hm⟩

theorem exists_selectedGraph_isHamiltonianCycle {m : ℕ} (hm : 3 ≤ m) :
    ∃ v : Vertex m 2, ∃ p : (selectedGraph hm).Walk v v, p.IsHamiltonianCycle :=
  ConnectedTwoRegular.exists_isHamiltonianCycle_of_neighbor_ncard_two
    (connected hm) (neighborSet_ncard_two hm)

theorem hasHamiltonianRealization {m : ℕ} (hm : 3 ≤ m) :
    HasHamiltonianRealization (graph m 2 hm) (realizedEdges hm (geometry m)) :=
  (geometry_realization_iff hm (geometry m)).mpr (isHamiltonianGeometry hm)

noncomputable def selection {m : ℕ} (hm : 3 ≤ m) : Selection (graph m 2 hm) :=
  hamiltonianSelectionEquiv hm ⟨geometry m, isHamiltonianGeometry hm⟩

theorem selection_val {m : ℕ} (hm : 3 ≤ m) :
    (selection hm).val = realizedEdges hm (geometry m) :=
  hamiltonianSelectionEquiv_val hm ⟨geometry m, isHamiltonianGeometry hm⟩

theorem geometryParity_eq_one {m : ℕ} (hm : 3 ≤ m) :
    geometryParity hm (geometry m) = 1 := by
  unfold geometryParity geometryWeight
  rw [sum_idsOfGeometry_meridian_eq_lastRow]
  simp [geometry]

theorem selectionParity_eq_one {m : ℕ} (hm : 3 ≤ m) :
    selectionParity hm (selection hm) = 1 := by
  rw [selection, selectionParity_hamiltonianSelectionEquiv]
  exact geometryParity_eq_one hm

end TriangularZigzag
