import ActualTransfer
import FiniteTransferPaths

/-!
# Encoding an actual Hamiltonian cycle as an accepted labelled object

The forward map uses the complete sequence of actual cut states and the
physical vertical masks of the selected graph. Its observations recover
all vertical, horizontal, and forward-diagonal selections exactly. A
simultaneous realization of arbitrary accepted objects, a converse, and
any injectivity or counting equivalence remain separate obligations.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding

/-- The existing accepted-object type specialized to the actual-occurrence labels. -/
abbrev AcceptedObject {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (n : ℕ) :=
  CylinderTransfer.Accepted (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p) n

/-- Observe the first column's vertical mask. -/
def acceptedInitialMask {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : RowMask m := w.2.1.val

/-- Observe the local vertical masks in their exact path order. -/
def acceptedLocalMasks {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : Fin n → RowMask m :=
  CylinderTransfer.LabelledPath.observe (fun _ _ e => e.val) w.2.2.2.1

/-- Observe the final column's vertical mask. -/
def acceptedTerminalMask {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : RowMask m := w.2.2.2.2.val

/-- The initial state followed by each local edge's target state. -/
def acceptedCutStates {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : Fin (n + 1) → CoreState hm :=
  Fin.cases w.1 (CylinderTransfer.LabelledPath.observe (fun _ t _ => t) w.2.2.2.1)

/-- Combine the initial, local, and terminal masks into their physical column order. -/
def acceptedVerticalMasks {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : Fin (n + 2) → RowMask m :=
  Fin.cases (acceptedInitialMask w)
    (Fin.lastCases (acceptedTerminalMask w) (acceptedLocalMasks w))

/-- All consecutive cuts of one actual cycle supply its exact labelled path. -/
noncomputable def cyclePath {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    CylinderTransfer.LabelledPath (LocalLabel hm) n
      (coreAtCut hm hn C hC 0) (coreAtCut hm hn C hC (Fin.last n)) :=
  CylinderTransfer.LabelledPath.ofSequence (LocalLabel hm) n
    (coreAtCut hm hn C hC) (localLabelOfCycle hm hn C hC)

/-- Canonical forward encoding of a Hamiltonian cycle of width at least three. -/
noncomputable def cycleAccepted {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) : AcceptedObject hm (typeParity hm C) n :=
  ⟨coreAtCut hm hn C hC 0, initialLabelOfCycle hm hn C hC,
    coreAtCut hm hn C hC (Fin.last n), cyclePath hm hn C hC,
    terminalLabelOfCycle hm hn C hC⟩

@[simp] theorem cycleAccepted_initialState {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    (cycleAccepted hm hn C hC).1 = coreAtCut hm hn C hC 0 := rfl

@[simp] theorem cycleAccepted_terminalState {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    (cycleAccepted hm hn C hC).2.2.1 = coreAtCut hm hn C hC (Fin.last n) := rfl

@[simp] theorem cycleAccepted_initialMask {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    acceptedInitialMask (cycleAccepted hm hn C hC) =
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) 0 := rfl

@[simp] theorem cycleAccepted_terminalMask {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    acceptedTerminalMask (cycleAccepted hm hn C hC) =
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last (n + 1)) := rfl

/-- The generic observer recovers every actual local vertical mask. -/
theorem cycleAccepted_localMasks {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    acceptedLocalMasks (cycleAccepted hm hn C hC) =
      fun i => verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) i.succ.castSucc := by
  change CylinderTransfer.LabelledPath.observe (fun _ _ e => e.val)
    (cyclePath hm hn C hC) = _
  unfold cyclePath
  rw [CylinderTransfer.LabelledPath.observe_ofSequence]
  rfl

/-- Observing the initial state and successive targets recovers all actual cut states. -/
theorem cycleAccepted_cutStates {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    acceptedCutStates (cycleAccepted hm hn C hC) = coreAtCut hm hn C hC := by
  funext c
  refine Fin.cases ?_ (fun i => ?_) c
  · rfl
  · change CylinderTransfer.LabelledPath.observe (fun _ t _ => t)
      (cyclePath hm hn C hC) i = coreAtCut hm hn C hC i.succ
    unfold cyclePath
    rw [CylinderTransfer.LabelledPath.observe_ofSequence]

/-- Every column's observed vertical mask is the actual selected mask in that column. -/
theorem cycleAccepted_verticalMasks {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    acceptedVerticalMasks (cycleAccepted hm hn C hC) =
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) := by
  funext c
  refine Fin.cases ?_ (fun d => ?_) c
  · rfl
  · refine Fin.lastCases ?_ (fun i => ?_) d
    · simpa only [acceptedVerticalMasks, Fin.cases_succ, Fin.lastCases_last] using
        cycleAccepted_terminalMask hm hn C hC
    · simpa only [acceptedVerticalMasks, Fin.cases_succ, Fin.lastCases_castSucc] using
        congrFun (cycleAccepted_localMasks hm hn C hC) i

private theorem selectedCycleGraph_edgeSet {m L : ℕ} (hm : 3 ≤ m)
    {v : Vertex m L} (C : (graph m L hm).Walk v v) :
    (SimpleGraph.fromEdgeSet C.edgeSet).edgeSet = C.edgeSet := by
  rw [← CountedHamiltonian.walk_spanningCoe_edgeSet C, SimpleGraph.fromEdgeSet_edgeSet]

/-- The encoded object recovers membership of every physical vertical edge. -/
theorem cycleAccepted_vertical_physical_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 2)) (r : Fin m) :
    acceptedVerticalMasks (cycleAccepted hm hn C hC) c r = true ↔
      toEdge hm (Sum.inl (r, c)) ∈ C.edgeSet := by
  rw [cycleAccepted_verticalMasks, verticalMask_physical_iff, selectedCycleGraph_edgeSet]

/-- The encoded cut sequence recovers membership of every physical horizontal edge. -/
theorem cycleAccepted_horizontal_physical_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 1)) (r : Fin m) :
    (acceptedCutStates (cycleAccepted hm hn C hC) c).val.horizontal r = true ↔
      toEdge hm (Sum.inr (Sum.inl (r, cutEdgeIndex c))) ∈ C.edgeSet := by
  rw [cycleAccepted_cutStates, coreAtCut_val, cutState_horizontal_physical_iff,
    selectedCycleGraph_edgeSet]

/-- The encoded cut sequence recovers membership of every physical forward diagonal. -/
theorem cycleAccepted_diagonal_physical_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 1)) (r : Fin m) :
    (acceptedCutStates (cycleAccepted hm hn C hC) c).val.diagonal r = true ↔
      toEdge hm (Sum.inr (Sum.inr (r, cutEdgeIndex c))) ∈ C.edgeSet := by
  rw [cycleAccepted_cutStates, coreAtCut_val, cutState_diagonal_physical_iff,
    selectedCycleGraph_edgeSet]

/-- An actual cycle supplies an accepted object in its actual total parity class. -/
theorem nonempty_accepted_of_cycle {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) : Nonempty (AcceptedObject hm (typeParity hm C) n) :=
  ⟨cycleAccepted hm hn C hC⟩

end TriangularCylinder.Transfer
