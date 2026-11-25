import CycleAccepted

/-!
# Physical reconstruction and the counted-selection forward map

An arbitrary accepted object determines a finite set of ambient physical
edges. The canonical encoding of an actual Hamiltonian selection recovers
that selection exactly. This gives a forward injection only: no Hamiltonian
realization of arbitrary accepted objects is asserted.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding CountedHamiltonian

/-- Read the complete physical V/H/D masks of an accepted object. -/
def acceptedGeometry {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : ColumnGeometry m (n + 2) :=
  (acceptedVerticalMasks w,
    (fun c r => (acceptedCutStates w c).val.horizontal r,
     fun c r => (acceptedCutStates w c).val.diagonal r))

/-- Reconstruct only the physical edge finset, without asserting a cycle. -/
def acceptedEdges {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : Finset (Sym2 (Vertex m (n + 2))) :=
  realizedEdges hm (acceptedGeometry w)

/-- Every reconstructed edge is an edge of the actual ambient cylinder. -/
theorem acceptedEdges_mem {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) {e : Sym2 (Vertex m (n + 2))}
    (he : e ∈ acceptedEdges w) : e ∈ (graph m (n + 2) hm).edgeSet :=
  realizedEdges_mem hm (acceptedGeometry w) he

private theorem realizedEdges_eq_of_flag_iff {m L : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (E : Finset (Sym2 (Vertex m L)))
    (hE : ∀ e ∈ E, e ∈ (graph m L hm).edgeSet)
    (hflag : ∀ id, geometryFlag g id = true ↔ toEdge hm id ∈ E) :
    realizedEdges hm g = E := by
  ext e
  constructor
  · intro he
    obtain ⟨id, hid, rfl⟩ := Finset.mem_image.mp he
    exact (hflag id).mp ((mem_idsOfGeometry g id).mp hid)
  · intro he
    obtain ⟨id, rfl⟩ := exists_toEdge hm e (hE e he)
    exact Finset.mem_image.mpr ⟨id, (mem_idsOfGeometry g id).mpr ((hflag id).mpr he), rfl⟩

/-- The reconstructed geometry of an encoded cycle has exactly its selected physical IDs. -/
theorem acceptedGeometry_cycleAccepted_flag_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (id : EdgeId m (n + 2)) :
    geometryFlag (acceptedGeometry (cycleAccepted hm hn C hC)) id = true ↔
      toEdge hm id ∈ C.edgeSet := by
  rcases id with ⟨r, c⟩ | ⟨r, c⟩ | ⟨r, c⟩
  · exact cycleAccepted_vertical_physical_iff hm hn C hC c r
  · exact cycleAccepted_horizontal_physical_iff hm hn C hC c r
  · exact cycleAccepted_diagonal_physical_iff hm hn C hC c r

/-- Physical reconstruction is exact on every actual cycle encoding. -/
theorem acceptedEdges_cycleAccepted {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    acceptedEdges (cycleAccepted hm hn C hC) = selectedEdges C := by
  apply realizedEdges_eq_of_flag_iff hm
  · intro e he
    exact C.edges_subset_edgeSet (List.mem_toFinset.mp he)
  · intro id
    simpa only [← coe_selectedEdges C] using acceptedGeometry_cycleAccepted_flag_iff hm hn C hC id

/-- The existing counted edge-set selections restricted to the existing parity. -/
abbrev ParitySelection {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (L : ℕ) :=
  {s : Selection (graph m L hm) // selectionParity hm s = p}

/-- The selected graph is determined by the counted edge finset, with no chosen traversal. -/
def selectionGraph {m L : ℕ} (hm : 3 ≤ m) (s : Selection (graph m L hm)) :
    SimpleGraph (Vertex m L) := SimpleGraph.fromEdgeSet (s.val : Set (Sym2 (Vertex m L)))

theorem selectionGraph_edgeSet {m L : ℕ} (hm : 3 ≤ m)
    (s : Selection (graph m L hm)) :
    (selectionGraph hm s).edgeSet = (s.val : Set (Sym2 (Vertex m L))) :=
  selectedGraph_edgeSet (fun _ he => selection_edge_mem (graph m L hm) s he)

private theorem selectionGraph_of_presentation {m L : ℕ} (hm : 3 ≤ m)
    (s : Selection (graph m L hm)) {v : Vertex m L}
    (C : (graph m L hm).Walk v v) (hE : selectedEdges C = s.val) :
    SimpleGraph.fromEdgeSet C.edgeSet = selectionGraph hm s := by
  rw [← coe_selectedEdges C, hE]
  rfl

private theorem selection_cut_is_core {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (s : Selection (graph m (n + 2) hm)) (c : Fin (n + 1)) :
    BoundaryState.Occurs hm (cutState hm (selectionGraph hm s) c) ∧
      ¬ FullOutgoing (cutState hm (selectionGraph hm s) c) := by
  obtain ⟨v, C, hC, hE⟩ := s.property
  rw [← selectionGraph_of_presentation hm s C hE]
  exact ⟨cutState_occurs hm C hC c, cutState_not_full hm hn C hC c⟩

/-- Core cut data are computed from the selected edge set; witnesses occur only in its proof. -/
noncomputable def selectionCoreAtCut {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (s : Selection (graph m (n + 2) hm)) (c : Fin (n + 1)) : CoreState hm :=
  ⟨cutState hm (selectionGraph hm s) c, selection_cut_is_core hm hn s c⟩

@[simp] theorem selectionCoreAtCut_val {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (s : Selection (graph m (n + 2) hm)) (c : Fin (n + 1)) :
    (selectionCoreAtCut hm hn s c).val = cutState hm (selectionGraph hm s) c := rfl

private theorem selection_initial_realized {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (s : Selection (graph m (n + 2) hm)) :
    InitialRealized hm (selectionCoreAtCut hm hn s 0)
      (verticalMask hm (selectionGraph hm s) 0) := by
  obtain ⟨v, C, hC, hE⟩ := s.property
  refine ⟨n, v, C, hC, ?_, ?_⟩
  · change cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) 0 = _
    rw [selectionGraph_of_presentation hm s C hE]
    rfl
  · rw [selectionGraph_of_presentation hm s C hE]

private theorem selection_local_realized {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (s : Selection (graph m (n + 2) hm)) (i : Fin n) :
    LocalRealized hm (selectionCoreAtCut hm hn s i.castSucc)
      (selectionCoreAtCut hm hn s i.succ)
      (verticalMask hm (selectionGraph hm s) i.succ.castSucc) := by
  obtain ⟨v, C, hC, hE⟩ := s.property
  refine ⟨n, i, v, C, hC, ?_, ?_, ?_⟩
  · change cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) i.castSucc = _
    rw [selectionGraph_of_presentation hm s C hE]
    rfl
  · change cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) i.succ = _
    rw [selectionGraph_of_presentation hm s C hE]
    rfl
  · rw [selectionGraph_of_presentation hm s C hE]

/-- The existing selected-edge parity equals the total parity of every actual presentation. -/
theorem presentation_typeParity_eq {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (s : ParitySelection hm p L) {v : Vertex m L}
    (C : (graph m L hm).Walk v v) (hC : C.IsHamiltonianCycle)
    (hE : selectedEdges C = s.val.val) : typeParity hm C = p := by
  have hs : CountedHamiltonian.ofCycle (graph m L hm) C hC = s.val := Subtype.ext hE
  exact (selectionParity_ofCycle hm C hC).symm.trans
    ((congrArg (selectionParity hm) hs).trans s.property)

private theorem selection_terminal_realized {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) :
    TerminalRealized hm p (selectionCoreAtCut hm hn s.val (Fin.last n))
      (verticalMask hm (selectionGraph hm s.val) (Fin.last (n + 1))) := by
  obtain ⟨v, C, hC, hE⟩ := s.val.property
  refine ⟨n, v, C, hC, ?_, ?_, presentation_typeParity_eq hm p s C hC hE⟩
  · change cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last n) = _
    rw [selectionGraph_of_presentation hm s.val C hE]
    rfl
  · rw [selectionGraph_of_presentation hm s.val C hE]

/-- The canonical forward map depends on the selected edge set alone.
All Hamiltonian presentations are used only to establish the label properties. -/
noncomputable def selectionAccepted {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) : AcceptedObject hm p n :=
  ⟨selectionCoreAtCut hm hn s.val 0,
    ⟨verticalMask hm (selectionGraph hm s.val) 0, selection_initial_realized hm hn s.val⟩,
    selectionCoreAtCut hm hn s.val (Fin.last n),
    CylinderTransfer.LabelledPath.ofSequence (LocalLabel hm) n
      (selectionCoreAtCut hm hn s.val)
      (fun i => ⟨verticalMask hm (selectionGraph hm s.val) i.succ.castSucc,
        selection_local_realized hm hn s.val i⟩),
    ⟨verticalMask hm (selectionGraph hm s.val) (Fin.last (n + 1)),
      selection_terminal_realized hm hn p s⟩⟩

/-- The local observations are exactly the edge-set-defined vertical masks. -/
theorem selectionAccepted_localMasks {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) :
    acceptedLocalMasks (selectionAccepted hm hn p s) =
      fun i => verticalMask hm (selectionGraph hm s.val) i.succ.castSucc := by
  simp only [acceptedLocalMasks, selectionAccepted,
    CylinderTransfer.LabelledPath.observe_ofSequence]

/-- Every observed cut is computed directly from the counted selected graph. -/
theorem selectionAccepted_cutStates {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) :
    acceptedCutStates (selectionAccepted hm hn p s) = selectionCoreAtCut hm hn s.val := by
  funext c
  refine Fin.cases ?_ (fun i => ?_) c
  · rfl
  · simp only [acceptedCutStates, selectionAccepted,
      CylinderTransfer.LabelledPath.observe_ofSequence, Fin.cases_succ]

/-- Every observed column mask is computed directly from the counted selected graph. -/
theorem selectionAccepted_verticalMasks {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) :
    acceptedVerticalMasks (selectionAccepted hm hn p s) =
      verticalMask hm (selectionGraph hm s.val) := by
  funext c
  refine Fin.cases ?_ (fun d => ?_) c
  · rfl
  · refine Fin.lastCases ?_ (fun i => ?_) d
    · simp only [acceptedVerticalMasks, Fin.cases_succ, Fin.lastCases_last]
      rfl
    · simpa only [acceptedVerticalMasks, Fin.cases_succ, Fin.lastCases_castSucc] using
        congrFun (selectionAccepted_localMasks hm hn p s) i

/-- Every reconstructed physical-ID flag is exactly membership in the original selection. -/
theorem acceptedGeometry_selectionAccepted_flag_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) (id : EdgeId m (n + 2)) :
    geometryFlag (acceptedGeometry (selectionAccepted hm hn p s)) id = true ↔
      toEdge hm id ∈ s.val.val := by
  rcases id with ⟨r, c⟩ | ⟨r, c⟩ | ⟨r, c⟩
  · change acceptedVerticalMasks (selectionAccepted hm hn p s) c r = true ↔ _
    rw [selectionAccepted_verticalMasks, verticalMask_physical_iff, selectionGraph_edgeSet]
    rfl
  · change (acceptedCutStates (selectionAccepted hm hn p s) c).val.horizontal r = true ↔ _
    rw [selectionAccepted_cutStates, selectionCoreAtCut_val,
      cutState_horizontal_physical_iff, selectionGraph_edgeSet]
    rfl
  · change (acceptedCutStates (selectionAccepted hm hn p s) c).val.diagonal r = true ↔ _
    rw [selectionAccepted_cutStates, selectionCoreAtCut_val,
      cutState_diagonal_physical_iff, selectionGraph_edgeSet]
    rfl

/-- Physical reconstruction recovers the exact counted selected edge finset.
It is an inverse identity on the forward image, not a Hamiltonian assertion
about arbitrary accepted objects. -/
theorem acceptedEdges_selectionAccepted {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) :
    acceptedEdges (selectionAccepted hm hn p s) = s.val.val :=
  realizedEdges_eq_of_flag_iff hm _ _
    (fun _ he => selection_edge_mem (graph m (n + 2) hm) s.val he)
    (acceptedGeometry_selectionAccepted_flag_iff hm hn p s)

/-- Distinct counted undirected selections have distinct accepted encodings. -/
theorem selectionAccepted_injective {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) : Function.Injective (selectionAccepted (n := n) hm hn p) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg acceptedEdges h
  simpa only [acceptedEdges_selectionAccepted] using he

/-- The canonical counted-object forward injection, with the parity class fixed. -/
noncomputable def selectionAcceptedEmbedding {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) : ParitySelection hm p (n + 2) ↪ AcceptedObject hm p n where
  toFun := selectionAccepted hm hn p
  inj' := selectionAccepted_injective hm hn p

end TriangularCylinder.Transfer
