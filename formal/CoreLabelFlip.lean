import SpliceIndexedState
import ParityOneSplice
import IndexedEndVertical

/-!
# Parity flip preserves the counted local and terminal labels

A single three-column left splice of an actual witness realizes both
flipped local states at consecutive cuts. Its old positive-column vertical
masks are unchanged. The same construction flips terminal cycle parity.
Since masks are the only label data, these constructions induce identity-on-
mask equivalences of the actual counted label types.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph BoundaryState SpliceCutTransport

/-- Both flipped states co-occur in one actual joined cycle, with exactly
the original local vertical mask. -/
theorem localRealized_flip {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm)
    (mask : RowMask m) (h : LocalRealized hm s t mask) :
    LocalRealized hm (coreFlip hm s) (coreFlip hm t) mask := by
  classical
  rcases h with ⟨n, i, v, B, hB, hs, ht, hV⟩
  have hnonfull : ¬ FullOutgoing (cutState hm (fromEdgeSet B.edgeSet) i.castSucc) := by
    rw [hs]
    exact s.property.2
  obtain ⟨⟨r, u, hrs, hfirst⟩, _⟩ :=
    IndexedEndVertical.exists_selected_end_edges_of_nonfull_cutState
      hm B hB i.castSucc hnonfull
  obtain ⟨w, J, GA, a₀, a₁, hJ, hparity, hGA, hxy, hsplice⟩ :=
    ParityOneSplice.exists_parity_one_left_splice hm (by omega) r u hrs B hB hfirst
  have hwidth : 3 + (n + 2) = (3 + n) + 2 := by omega
  refine ⟨3 + n, shiftStep 3 i, _, J.map (CycleWidthTransport.widthHom hm hwidth),
    CycleWidthTransport.map_isHamiltonianCycle hm hwidth J hJ, ?_, ?_, ?_⟩
  · rw [CycleWidthTransport.selectedGraph_map]
    simpa only [shiftCut_castSucc, hs, coreFlip_val] using
      SpliceIndexedState.cutState_flip_of_splice hm GA B J
        hB.isCycle.isTrail hJ.isCycle.isTrail a₀ a₁ r u hGA hxy hsplice hparity i.castSucc
  · rw [CycleWidthTransport.selectedGraph_map]
    simpa only [shiftCut_succ, ht, coreFlip_val] using
      SpliceIndexedState.cutState_flip_of_splice hm GA B J
        hB.isCycle.isTrail hJ.isCycle.isTrail a₀ a₁ r u hGA hxy hsplice hparity i.succ
  · rw [CycleWidthTransport.selectedGraph_map, shiftStep_column]
    exact (SpliceIndexedState.verticalMask_shift_of_splice hm GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r u hsplice
      i.succ.castSucc (Nat.succ_pos i.val)).trans hV

/-- The final cut and its mask remain in the same joined actual cycle,
whose total parity is the old total parity plus one. -/
theorem terminalRealized_flip {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (s : CoreState hm) (mask : RowMask m) (h : TerminalRealized hm p s mask) :
    TerminalRealized hm (p + 1) (coreFlip hm s) mask := by
  classical
  rcases h with ⟨n, v, B, hB, hs, hV, hP⟩
  have hnonfull : ¬ FullOutgoing (cutState hm (fromEdgeSet B.edgeSet) (Fin.last n)) := by
    rw [hs]
    exact s.property.2
  obtain ⟨⟨r, u, hrs, hfirst⟩, _⟩ :=
    IndexedEndVertical.exists_selected_end_edges_of_nonfull_cutState
      hm B hB (Fin.last n) hnonfull
  obtain ⟨w, J, GA, a₀, a₁, hJ, hparity, hGA, hxy, hsplice⟩ :=
    ParityOneSplice.exists_parity_one_left_splice hm (by omega) r u hrs B hB hfirst
  have hwidth : 3 + (n + 2) = (3 + n) + 2 := by omega
  refine ⟨3 + n, _, J.map (CycleWidthTransport.widthHom hm hwidth),
    CycleWidthTransport.map_isHamiltonianCycle hm hwidth J hJ, ?_, ?_, ?_⟩
  · rw [CycleWidthTransport.selectedGraph_map]
    simpa only [shiftCut_last, hs, coreFlip_val] using
      SpliceIndexedState.cutState_flip_of_splice hm GA B J
        hB.isCycle.isTrail hJ.isCycle.isTrail a₀ a₁ r u hGA hxy hsplice hparity (Fin.last n)
  · rw [CycleWidthTransport.selectedGraph_map, shift_last_column]
    exact (SpliceIndexedState.verticalMask_shift_of_splice hm GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r u hsplice
      (Fin.last (n + 1)) (Nat.succ_pos n)).trans hV
  · rw [CycleWidthTransport.typeParity_map, hparity, hP]
    exact add_comm 1 p

theorem localRealized_flip_iff {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm)
    (mask : RowMask m) :
    LocalRealized hm (coreFlip hm s) (coreFlip hm t) mask ↔
      LocalRealized hm s t mask := by
  constructor
  · intro h
    simpa only [coreFlip_involutive hm s, coreFlip_involutive hm t] using
      localRealized_flip hm (coreFlip hm s) (coreFlip hm t) mask h
  · exact localRealized_flip hm s t mask

theorem terminalRealized_flip_iff {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (s : CoreState hm) (mask : RowMask m) :
    TerminalRealized hm (p + 1) (coreFlip hm s) mask ↔
      TerminalRealized hm p s mask := by
  constructor
  · intro h
    have hparity : p + 1 + 1 = p := by
      have htwo : (1 : ZMod 2) + 1 = 0 := by decide
      rw [add_assoc, htwo, add_zero]
    simpa only [coreFlip_involutive hm s, hparity] using
      terminalRealized_flip hm (p + 1) (coreFlip hm s) mask h
  · exact terminalRealized_flip hm p s mask

/-- The local-label equivalence keeps the vertical mask exactly unchanged. -/
def localLabelFlipEquiv {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) :
    LocalLabel hm s t ≃ LocalLabel hm (coreFlip hm s) (coreFlip hm t) where
  toFun a := ⟨a.val, localRealized_flip hm s t a.val a.property⟩
  invFun a := ⟨a.val, (localRealized_flip_iff hm s t a.val).mp a.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The terminal-label equivalence keeps the mask and flips total parity. -/
def terminalLabelFlipEquiv {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm) :
    TerminalLabel hm p s ≃ TerminalLabel hm (p + 1) (coreFlip hm s) where
  toFun a := ⟨a.val, terminalRealized_flip hm p s a.val a.property⟩
  invFun a := ⟨a.val, (terminalRealized_flip_iff hm p s a.val).mp a.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem localLabelFlipEquiv_val {m : ℕ} (hm : 3 ≤ m)
    (s t : CoreState hm) (a : LocalLabel hm s t) :
    (localLabelFlipEquiv hm s t a).val = a.val := rfl

@[simp] theorem terminalLabelFlipEquiv_val {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (s : CoreState hm) (a : TerminalLabel hm p s) :
    (terminalLabelFlipEquiv hm p s a).val = a.val := rfl

theorem localLabel_card_flip {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) :
    Fintype.card (LocalLabel hm (coreFlip hm s) (coreFlip hm t)) =
      Fintype.card (LocalLabel hm s t) :=
  (Fintype.card_congr (localLabelFlipEquiv hm s t)).symm

theorem terminalLabel_card_flip {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm) :
    Fintype.card (TerminalLabel hm (p + 1) (coreFlip hm s)) =
      Fintype.card (TerminalLabel hm p s) :=
  (Fintype.card_congr (terminalLabelFlipEquiv hm p s)).symm

#print axioms localRealized_flip
#print axioms terminalRealized_flip
#print axioms localRealized_flip_iff
#print axioms terminalRealized_flip_iff
#print axioms localLabelFlipEquiv
#print axioms terminalLabelFlipEquiv
#print axioms localLabelFlipEquiv_val
#print axioms terminalLabelFlipEquiv_val
#print axioms localLabel_card_flip
#print axioms terminalLabel_card_flip

end TriangularCylinder.Transfer
