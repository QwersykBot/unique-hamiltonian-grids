import BoundaryParity

/-!
# Initial, consecutive, and terminal boundary parity identities

The only state parity is the frozen `cutState` field. Concrete V/D charges
come from existing physical masks, and total parity is the existing walk or
counted-selection parity. Label consequences use their actual realization
witnesses only inside proofs.
-/

namespace TriangularCylinder.BoundaryParity

open SimpleGraph TriangularEdgeEncoding BoundaryState Transfer CountedHamiltonian
open scoped BigOperators

/-- The prefix through column zero contains exactly the first column. -/
private theorem sum_prefix_zero {W : Type*} [AddCommMonoid W] {L : ℕ}
    (hL : 0 < L) (f : Fin L → W) :
    (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ 0), f c) =
      f ⟨0, hL⟩ := by
  have hfilter : (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ 0) =
      {⟨0, hL⟩} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [hfilter, Finset.sum_singleton]

/-- Extending the prefix by one column adds exactly its value. -/
private theorem sum_prefix_step {W : Type*} [AddCommMonoid W] {L : ℕ}
    (f : Fin L → W) (j : ℕ) (hj : j + 1 < L) :
    (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j + 1), f c) =
      (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j), f c) +
        f ⟨j + 1, hj⟩ := by
  have hfilter : (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j + 1) =
      insert ⟨j + 1, hj⟩ ((Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨j + 1, hj⟩ : Fin L) ∉
      (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hfilter, Finset.sum_insert hnot, add_comm]

/-- Every column lies at or before the last natural-number column bound.
This statement also covers `L = 0`, when both finsets are empty. -/
private theorem filter_last_eq_univ (L : ℕ) :
    (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ L - 1) = Finset.univ := by
  apply Finset.filter_true_of_mem
  intro c _
  have hc := c.isLt
  omega

/-- The prefix through the last column is the full finite sum. -/
private theorem sum_prefix_last {W : Type*} [AddCommMonoid W] {L : ℕ} (f : Fin L → W) :
    (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ L - 1), f c) =
      ∑ c : Fin L, f c := by
  rw [filter_last_eq_univ]

/-- The initial cut charges its first-column V and outgoing D, with H charge zero. -/
theorem cutState_parity_initial {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) :
    (cutState hm H 0).parity =
      (if verticalMask hm H 0 (lastRow m hm) then (1 : ZMod 2) else 0) +
      (if (cutState hm H 0).diagonal (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [cutState_parity_eq_lastRow]
  simp only [Fin.val_zero]
  rw [sum_prefix_zero (by omega : 0 < n + 2), sum_prefix_zero (by omega : 0 < n + 1)]
  rfl

/-- Advancing one cut adds exactly the new-column V and new outgoing D charges. -/
theorem cutState_parity_succ {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) :
    (cutState hm H i.succ).parity = (cutState hm H i.castSucc).parity +
      (if verticalMask hm H i.succ.castSucc (lastRow m hm) then (1 : ZMod 2) else 0) +
      (if (cutState hm H i.succ).diagonal (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [cutState_parity_eq_lastRow hm H i.succ,
    cutState_parity_eq_lastRow hm H i.castSucc]
  simp only [Fin.val_succ, Fin.coe_castSucc]
  have hi := i.isLt
  rw [sum_prefix_step (fun c => if verticalMask hm H c (lastRow m hm) then (1 : ZMod 2) else 0)
      i.val (by omega),
    sum_prefix_step (fun c => if (cutState hm H c).diagonal (lastRow m hm) then (1 : ZMod 2) else 0)
      i.val (by omega)]
  ac_rfl

/-- The full selected physical-ID sum is the full V/D last-row charge. -/
theorem sum_selectedPhysicalIds_eq_lastRow {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) :
    (∑ id ∈ selectedPhysicalIds hm H, meridianWeight hm (toEdge hm id)) =
      (∑ c : Fin (n + 2), if verticalMask hm H c (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ c : Fin (n + 1),
        if (cutState hm H c).diagonal (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [← idsOfGeometry_selectedGeometry hm H, sum_idsOfGeometry_meridian_eq_lastRow]
  simp only [selectedGeometry_vertical, selectedGeometry_diagonal_cutState]
  rfl

/-- After the last cut, only the final-column V charge remains to be assigned. -/
theorem selectedPhysicalIds_sum_terminal {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) :
    (∑ id ∈ selectedPhysicalIds hm H, meridianWeight hm (toEdge hm id)) =
      (cutState hm H (Fin.last n)).parity +
        (if verticalMask hm H (Fin.last (n + 1)) (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [sum_selectedPhysicalIds_eq_lastRow, cutState_parity_eq_lastRow]
  simp only [Fin.val_last]
  have hV := sum_prefix_step
    (fun c : Fin (n + 2) => if verticalMask hm H c (lastRow m hm) then (1 : ZMod 2) else 0)
    n (by omega)
  rw [show (Finset.univ : Finset (Fin (n + 2))).filter (fun c => c.val ≤ n + 1) =
    Finset.univ from filter_last_eq_univ (n + 2)] at hV
  rw [hV,
    show (Finset.univ : Finset (Fin (n + 1))).filter (fun c => c.val ≤ n) =
      Finset.univ from filter_last_eq_univ (n + 1)]
  ac_rfl

/-- Every actual trail's existing walk parity is the selected physical-ID sum. -/
theorem typeParity_eq_selectedPhysicalIds {m L : ℕ} (hm : 3 ≤ m)
    {x y : Vertex m L} (C : (graph m L hm).Walk x y) (hC : C.IsTrail) :
    typeParity hm C =
      ∑ id ∈ selectedPhysicalIds hm (SimpleGraph.fromEdgeSet C.edgeSet),
        meridianWeight hm (toEdge hm id) := by
  obtain ⟨g, hg⟩ := exists_geometry_of_edges hm (selectedEdges C)
    (fun _ he => C.edges_subset_edgeSet (List.mem_toFinset.mp he))
  have hgraph : SimpleGraph.fromEdgeSet C.edgeSet =
      SimpleGraph.fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L))) := by
    rw [hg, coe_selectedEdges]
  rw [typeParity, edgeWeight_eq_sum_selectedEdges (meridianWeight hm) C hC,
    ← hg, hgraph, selectedPhysicalIds_realizedEdges]
  exact sum_realizedEdges_eq_selectedIds hm g (meridianWeight hm)

/-- Total trail parity is last-cut parity plus the final-column V contribution. -/
theorem typeParity_terminal {m n : ℕ} (hm : 3 ≤ m)
    {x y : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk x y) (hC : C.IsTrail) :
    typeParity hm C = (cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last n)).parity +
      (if verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet)
        (Fin.last (n + 1)) (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [typeParity_eq_selectedPhysicalIds hm C hC, selectedPhysicalIds_sum_terminal]

/-- The same terminal identity for the existing counted undirected selection parity. -/
theorem selectionParity_terminal {m n : ℕ} (hm : 3 ≤ m)
    (s : Selection (graph m (n + 2) hm)) :
    selectionParity hm s =
      (cutState hm (SimpleGraph.fromEdgeSet (s.val : Set _)) (Fin.last n)).parity +
      (if verticalMask hm (SimpleGraph.fromEdgeSet (s.val : Set _))
        (Fin.last (n + 1)) (lastRow m hm) then (1 : ZMod 2) else 0) := by
  obtain ⟨v, C, hC, hE⟩ := s.property
  have hs : ofCycle (graph m (n + 2) hm) C hC = s := Subtype.ext hE
  rw [← hs, selectionParity_ofCycle]
  simpa only [ofCycle, coe_selectedEdges] using typeParity_terminal hm C hC.isCycle.isTrail

/-- An actual initial label fixes the first state's parity charge. -/
theorem initialLabel_parity {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm)
    (a : InitialLabel hm s) :
    s.val.parity = (if a.val (lastRow m hm) then (1 : ZMod 2) else 0) +
      (if s.val.diagonal (lastRow m hm) then (1 : ZMod 2) else 0) := by
  obtain ⟨n, v, C, _hC, hs, ha⟩ := a.property
  have h := cutState_parity_initial hm (SimpleGraph.fromEdgeSet C.edgeSet)
  rw [hs, ha] at h
  exact h

/-- An actual local label fixes the target parity from source parity and its V/D charges. -/
theorem localLabel_parity {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm)
    (a : LocalLabel hm s t) :
    t.val.parity = s.val.parity + (if a.val (lastRow m hm) then (1 : ZMod 2) else 0) +
      (if t.val.diagonal (lastRow m hm) then (1 : ZMod 2) else 0) := by
  obtain ⟨n, i, v, C, _hC, hs, ht, ha⟩ := a.property
  have h := cutState_parity_succ hm (SimpleGraph.fromEdgeSet C.edgeSet) i
  rw [hs, ht, ha] at h
  exact h

/-- An actual terminal label identifies total parity with last-state parity plus final V. -/
theorem terminalLabel_parity {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm)
    (a : TerminalLabel hm p s) :
    p = s.val.parity + (if a.val (lastRow m hm) then (1 : ZMod 2) else 0) := by
  obtain ⟨n, v, C, hC, hs, ha, hp⟩ := a.property
  have h := typeParity_terminal hm C hC.isCycle.isTrail
  rw [hs, ha, hp] at h
  exact h

end TriangularCylinder.BoundaryParity
