import BoundaryState
import MeridianClassifier
import ZigzagException

/-!
# Raw state of the exceptional all-horizontal/all-diagonal selection

The state fields are derived from exact physical-edge selection data. The
geometric zigzag construction is supplied separately by its owning module.
-/

namespace TriangularCylinder

open SimpleGraph TriangularEdgeEncoding BoundaryState

/-- Both outgoing physical masks are full, with isolated prefix rows and parity one. -/
def exceptionalRawState (m : ℕ) : RawBoundaryState m where
  horizontal := fun _ => true
  diagonal := fun _ => true
  reach := fun r s => decide (r = s)
  parity := 1

private theorem no_same_column_of_no_vertical {m : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m 2)} (hH : H ≤ graph m 2 hm)
    (hV : ∀ r c, toEdge hm (Sum.inl (r, c)) ∉ H.edgeSet)
    (r s : Fin m) (c : Fin 2) : ¬ H.Adj (r, c) (s, c) := by
  intro h
  rcases hH h with hf | hb
  · rcases hf with ⟨_, hrs⟩ | ⟨_, hcols⟩ | ⟨_, hcols⟩
    · have hs : rowSucc hm r = s := Fin.ext hrs.symm
      apply hV r c
      simpa only [toEdge, sourceVertex, targetVertex, hs] using
        (SimpleGraph.mem_edgeSet H).mpr h
    · change c.val + 1 = c.val at hcols
      omega
    · change c.val + 1 = c.val at hcols
      omega
  · rcases hb with ⟨_, hsr⟩ | ⟨_, hcols⟩ | ⟨_, hcols⟩
    · have hr : rowSucc hm s = r := Fin.ext hsr.symm
      apply hV s c
      simpa only [toEdge, sourceVertex, targetVertex, hr] using
        (SimpleGraph.mem_edgeSet H).mpr h.symm
    · change c.val + 1 = c.val at hcols
      omega
    · change c.val + 1 = c.val at hcols
      omega

/-- With no selected vertical edge, the processed first column has no edge. -/
theorem exceptional_prefixPart_eq_bot_of_no_vertical {m : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m 2)} (hH : H ≤ graph m 2 hm)
    (hV : ∀ r c, toEdge hm (Sum.inl (r, c)) ∉ H.edgeSet) :
    ColumnCut.prefixPart 0 1 H = ⊥ := by
  ext x y
  cases x with
  | inl x => exact Fin.elim0 x.2
  | inr r =>
    cases y with
    | inl y => exact Fin.elim0 y.2
    | inr s =>
      change H.Adj (r, 0) (s, 0) ↔ False
      exact iff_false_intro (no_same_column_of_no_vertical hm hH hV r s 0)

/-- The assigned physical-ID sum has exactly one nonzero term: the wrap diagonal. -/
theorem exceptional_assignedParity_of_no_vertical {m : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m 2))
    (hD : ∀ r, toEdge hm (diagonalId (j := 0) (k := 1) (by decide) r) ∈ H.edgeSet)
    (hV : ∀ r c, toEdge hm (Sum.inl (r, c)) ∉ H.edgeSet) :
    assignedParity (j := 0) (k := 1) hm H = 1 := by
  classical
  let wrapId : EdgeId m 2 := diagonalId (j := 0) (k := 1) (by decide) (lastRow m hm)
  change ∑ e ∈ assignedIds (j := 0) (k := 1) hm H, meridianWeight hm (toEdge hm e) = 1
  rw [Finset.sum_eq_single wrapId]
  · change meridianWeight hm s((lastRow m hm, (0 : Fin 2)),
      (rowSucc hm (lastRow m hm), (1 : Fin 2))) = 1
    rw [meridianWeight_nextRow hm _ _ (nextRow_rowSucc hm _)]
    simp
  · intro e he hne
    rcases e with ⟨r, c⟩ | ⟨r, c⟩ | ⟨r, c⟩
    · exact False.elim (hV r c ((mem_assignedIds (j := 0) (k := 1) hm H _).mp he).1)
    · exact meridianWeight_sameRow hm r (lowerCol c) (upperCol c)
    · have hr : r ≠ lastRow m hm := by
        intro hr
        apply hne
        subst r
        have hc : c = 0 := by
          apply Fin.ext
          have hc := c.isLt
          change c.val = 0
          omega
        subst c
        rfl
      change meridianWeight hm s((r, lowerCol c), (rowSucc hm r, upperCol c)) = 0
      rw [meridianWeight_nextRow hm _ _ (nextRow_rowSucc hm _), if_neg hr]
  · intro hn
    apply False.elim
    apply hn
    exact (diagonalId_assigned_iff (j := 0) (k := 1) hm (by decide) H (lastRow m hm)).mpr (hD _)

/-- Exact physical all-H/all-D selection data determine the exceptional raw state. -/
theorem stateAt_eq_exceptional_of_physical_selection {m : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m 2)) (hH : H ≤ graph m 2 hm)
    (hHor : ∀ r, toEdge hm (horizontalId (j := 0) (k := 1) (by decide) r) ∈ H.edgeSet)
    (hDiag : ∀ r, toEdge hm (diagonalId (j := 0) (k := 1) (by decide) r) ∈ H.edgeSet)
    (hVert : ∀ r c, toEdge hm (Sum.inl (r, c)) ∉ H.edgeSet) :
    stateAt (j := 0) (k := 1) hm (by decide) H = exceptionalRawState m := by
  apply RawBoundaryState.ext
  · funext r
    exact (stateAt_horizontal_physical_iff (j := 0) (k := 1) hm (by decide) H r).mpr (hHor r)
  · funext r
    exact (stateAt_diagonal_physical_iff (j := 0) (k := 1) hm (by decide) H r).mpr (hDiag r)
  · funext r s
    change (stateAt (j := 0) (k := 1) hm (by decide) H).reach r s = decide (r = s)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, stateAt_reach_iff,
      exceptional_prefixPart_eq_bot_of_no_vertical hm hH hVert, reachable_bot, Sum.inr.injEq]
  · exact exceptional_assignedParity_of_no_vertical hm H hDiag hVert

/-- The frozen zigzag selects exactly the physical identifiers marked by its geometry. -/
theorem zigzag_physical_mem_iff {m : ℕ} (hm : 3 ≤ m) (e : EdgeId m 2) :
    toEdge hm e ∈ (TriangularZigzag.selectedGraph hm).edgeSet ↔
      geometryFlag (TriangularZigzag.geometry m) e = true := by
  have hset : (TriangularZigzag.selectedGraph hm).edgeSet =
      (realizedEdges hm (TriangularZigzag.geometry m) : Set (Sym2 (Vertex m 2))) :=
    CountedHamiltonian.selectedGraph_edgeSet
      (fun _ he => realizedEdges_mem hm (TriangularZigzag.geometry m) he)
  rw [hset]
  change toEdge hm e ∈ (idsOfGeometry (TriangularZigzag.geometry m)).image (toEdge hm) ↔ _
  simp only [Finset.mem_image, (toEdge_injective hm).eq_iff, exists_eq_right,
    mem_idsOfGeometry]

private theorem zigzag_selectedGraph_le {m : ℕ} (hm : 3 ≤ m) :
    TriangularZigzag.selectedGraph hm ≤ graph m 2 hm :=
  CountedHamiltonian.selectedGraph_le
    (fun _ he => realizedEdges_mem hm (TriangularZigzag.geometry m) he)

private theorem zigzag_no_vertical {m : ℕ} (hm : 3 ≤ m) (r : Fin m) (c : Fin 2) :
    toEdge hm (Sum.inl (r, c)) ∉ (TriangularZigzag.selectedGraph hm).edgeSet := by
  intro h
  have hflag := (zigzag_physical_mem_iff hm (Sum.inl (r, c))).mp h
  cases hflag

/-- The actual first-column restriction of the zigzag is the empty graph. -/
theorem zigzag_prefixPart_eq_bot {m : ℕ} (hm : 3 ≤ m) :
    ColumnCut.prefixPart 0 1 (TriangularZigzag.selectedGraph hm) = ⊥ :=
  exceptional_prefixPart_eq_bot_of_no_vertical hm (zigzag_selectedGraph_le hm)
    (zigzag_no_vertical hm)

/-- The exact encoded raw state of the frozen geometric zigzag. -/
theorem zigzag_stateAt_exceptional {m : ℕ} (hm : 3 ≤ m) :
    stateAt (j := 0) (k := 1) hm (by decide) (TriangularZigzag.selectedGraph hm) =
      exceptionalRawState m := by
  apply stateAt_eq_exceptional_of_physical_selection hm _ (zigzag_selectedGraph_le hm)
  · intro r
    exact (zigzag_physical_mem_iff hm _).mpr rfl
  · intro r
    exact (zigzag_physical_mem_iff hm _).mpr rfl
  · exact zigzag_no_vertical hm

theorem zigzag_state_horizontal {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    (stateAt (j := 0) (k := 1) hm (by decide)
      (TriangularZigzag.selectedGraph hm)).horizontal r = true := by
  rw [zigzag_stateAt_exceptional]
  rfl

theorem zigzag_state_diagonal {m : ℕ} (hm : 3 ≤ m) (r : Fin m) :
    (stateAt (j := 0) (k := 1) hm (by decide)
      (TriangularZigzag.selectedGraph hm)).diagonal r = true := by
  rw [zigzag_stateAt_exceptional]
  rfl

theorem zigzag_state_reach {m : ℕ} (hm : 3 ≤ m) (r s : Fin m) :
    (stateAt (j := 0) (k := 1) hm (by decide)
      (TriangularZigzag.selectedGraph hm)).reach r s = decide (r = s) := by
  rw [zigzag_stateAt_exceptional]
  rfl

theorem zigzag_state_parity {m : ℕ} (hm : 3 ≤ m) :
    (stateAt (j := 0) (k := 1) hm (by decide)
      (TriangularZigzag.selectedGraph hm)).parity = 1 := by
  rw [zigzag_stateAt_exceptional]
  rfl

/-- The exceptional state occurs in a genuine Hamiltonian cycle for every width. -/
theorem exceptionalRawState_occurs (m : ℕ) (hm : 3 ≤ m) :
    Occurs hm (exceptionalRawState m) := by
  obtain ⟨v, C, hC, hEdges⟩ := TriangularZigzag.hasHamiltonianRealization hm
  have hgraph : fromEdgeSet C.edgeSet = TriangularZigzag.selectedGraph hm := by
    rw [← CountedHamiltonian.coe_selectedEdges, hEdges]
    rfl
  refine ⟨0, 1, by decide, v, C, hC, ?_⟩
  rw [hgraph]
  exact zigzag_stateAt_exceptional hm

end TriangularCylinder
