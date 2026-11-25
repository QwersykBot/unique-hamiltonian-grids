import ExceptionalState
import FullCrossing

/-!
# Finite labels realized by actual Hamiltonian cycles

States are occurring raw boundary states whose outgoing horizontal and
forward-diagonal masks are not both full. Every label is only one Boolean
vertical-row mask. Its Hamiltonian witnesses and all state equalities live
in a proposition, so neither a walk traversal nor a witness width adds
counted data. No completion, transition sufficiency, or counting equivalence
is asserted here.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding BoundaryState

/-- The physical vertical-edge choices in one column. -/
abbrev RowMask (m : ℕ) := Fin m → Bool

/-- Both outgoing physical masks are full. -/
def FullOutgoing {m : ℕ} (s : RawBoundaryState m) : Prop :=
  ∀ r, s.horizontal r = true ∧ s.diagonal r = true

/-- An actual occurring state with the full H/D case removed. -/
def CoreState {m : ℕ} (hm : 3 ≤ m) :=
  {s : RawBoundaryState m // Occurs hm s ∧ ¬ FullOutgoing s}

instance {m : ℕ} (hm : 3 ≤ m) : Finite (CoreState hm) := by
  unfold CoreState
  infer_instance

noncomputable instance {m : ℕ} (hm : 3 ≤ m) : Fintype (CoreState hm) :=
  Fintype.ofFinite _

theorem coreState_finite {m : ℕ} (hm : 3 ≤ m) : Finite (CoreState hm) :=
  inferInstance

theorem coreState_ne_exceptional {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm) :
    s.val ≠ exceptionalRawState m := by
  intro hs
  apply s.property.2
  rw [hs]
  exact fun _ => ⟨rfl, rfl⟩

/-- Width equality transports column types while preserving both coordinates. -/
def widthEquiv {m a b : ℕ} (h : a = b) : Vertex m a ≃ Vertex m b :=
  Equiv.prodCongr (Equiv.refl _) (finCongr h)

@[simp] theorem widthEquiv_row {m a b : ℕ} (h : a = b) (x : Vertex m a) :
    (widthEquiv h x).1 = x.1 := rfl

@[simp] theorem widthEquiv_col_val {m a b : ℕ} (h : a = b) (x : Vertex m a) :
    (widthEquiv h x).2.val = x.2.val := rfl

@[simp] theorem widthEquiv_refl {m L : ℕ} :
    widthEquiv (m := m) (rfl : L = L) = Equiv.refl _ := rfl

/-- The unprocessed width strictly to the right of a cut. -/
def cutTail {n : ℕ} (c : Fin (n + 1)) : ℕ := n + 1 - c.val

theorem cutTail_pos {n : ℕ} (c : Fin (n + 1)) : 1 ≤ cutTail c := by
  have hc := c.isLt
  unfold cutTail
  omega

theorem cutWidth_eq {n : ℕ} (c : Fin (n + 1)) :
    c.val + 1 + cutTail c = n + 2 := by
  have hc := c.isLt
  unfold cutTail
  omega

/-- The original selected graph in the exact split expected by `stateAt`. -/
def cutGraph {m n : ℕ} (H : SimpleGraph (Vertex m (n + 2)))
    (c : Fin (n + 1)) : SimpleGraph (Vertex m (c.val + 1 + cutTail c)) :=
  H.comap (widthEquiv (cutWidth_eq c))

/-- A single-cut wrapper for arbitrary fixed-width selected graphs. -/
noncomputable def cutState {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) : RawBoundaryState m :=
  stateAt hm (cutTail_pos c) (cutGraph H c)

/-- Exact correspondence with the frozen boundary encoder, including its
actual prefix reachability and selected-physical-ID parity fields. -/
theorem cutState_eq_stateAt {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) :
    cutState hm H c = stateAt hm (cutTail_pos c)
      (H.comap (widthEquiv (cutWidth_eq c))) := rfl

private theorem widthEquiv_boundaryCol {m n : ℕ} (c : Fin (n + 1)) (r : Fin m) :
    widthEquiv (cutWidth_eq c) (r, boundaryCol c.val (cutTail c)) =
      (r, c.castSucc) := by
  apply Prod.ext rfl
  apply Fin.ext
  rfl

private theorem widthEquiv_nextCol {m n : ℕ} (c : Fin (n + 1)) (r : Fin m) :
    widthEquiv (cutWidth_eq c) (r, nextCol (cutTail_pos c)) = (r, c.succ) := by
  apply Prod.ext rfl
  apply Fin.ext
  rfl

theorem cutState_horizontal_iff {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) (r : Fin m) :
    (cutState hm H c).horizontal r = true ↔ H.Adj (r, c.castSucc) (r, c.succ) := by
  rw [cutState, stateAt_horizontal_iff]
  change H.Adj (widthEquiv (cutWidth_eq c) (r, boundaryCol c.val (cutTail c)))
    (widthEquiv (cutWidth_eq c) (r, nextCol (cutTail_pos c))) ↔ _
  rw [widthEquiv_boundaryCol, widthEquiv_nextCol]

theorem cutState_diagonal_iff {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) (r : Fin m) :
    (cutState hm H c).diagonal r = true ↔
      H.Adj (r, c.castSucc) (rowSucc hm r, c.succ) := by
  rw [cutState, stateAt_diagonal_iff]
  change H.Adj (widthEquiv (cutWidth_eq c) (r, boundaryCol c.val (cutTail c)))
    (widthEquiv (cutWidth_eq c) (rowSucc hm r, nextCol (cutTail_pos c))) ↔ _
  rw [widthEquiv_boundaryCol, widthEquiv_nextCol]

theorem cutState_reach_iff {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) (r s : Fin m) :
    (cutState hm H c).reach r s = true ↔
      (ColumnCut.prefixPart c.val (cutTail c) (cutGraph H c)).Reachable
        (Sum.inr r) (Sum.inr s) :=
  stateAt_reach_iff hm (cutTail_pos c) (cutGraph H c) r s

theorem cutState_parity {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) :
    (cutState hm H c).parity = assignedParity hm (cutGraph H c) := rfl

/-- The selected physical vertical mask in one column. -/
noncomputable def verticalMask {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin L) : RowMask m := by
  classical
  exact fun r => decide (toEdge hm (Sum.inl (r, c)) ∈ H.edgeSet)

theorem verticalMask_physical_iff {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin L) (r : Fin m) :
    verticalMask hm H c r = true ↔ toEdge hm (Sum.inl (r, c)) ∈ H.edgeSet := by
  classical
  simp only [verticalMask, decide_eq_true_eq]

theorem verticalMask_iff {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin L) (r : Fin m) :
    verticalMask hm H c r = true ↔ H.Adj (r, c) (rowSucc hm r, c) := by
  rw [verticalMask_physical_iff]
  exact SimpleGraph.mem_edgeSet H

private theorem occurs_stateAt_comap {m j k L : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (h : j + 1 + k = L) {v : Vertex m L}
    (C : (graph m L hm).Walk v v) (hC : C.IsHamiltonianCycle) :
    Occurs hm (stateAt hm hk ((SimpleGraph.fromEdgeSet C.edgeSet).comap (widthEquiv h))) := by
  subst L
  simpa only [widthEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id] using
    occurs_stateAt hm hk C hC

theorem cutState_occurs {m n : ℕ} (hm : 3 ≤ m) {v : Vertex m (n + 2)}
    (C : (graph m (n + 2) hm).Walk v v) (hC : C.IsHamiltonianCycle)
    (c : Fin (n + 1)) : Occurs hm (cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) c) :=
  occurs_stateAt_comap hm (cutTail_pos c) (cutWidth_eq c) C hC

/-- The same cut as an index for the physical H/D edge identifiers. -/
def cutEdgeIndex {n : ℕ} (c : Fin (n + 1)) : Fin (n + 2 - 1) :=
  ⟨c.val, by have hc := c.isLt; omega⟩

@[simp] theorem lowerCol_cutEdgeIndex {n : ℕ} (c : Fin (n + 1)) :
    lowerCol (cutEdgeIndex c) = c.castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem upperCol_cutEdgeIndex {n : ℕ} (c : Fin (n + 1)) :
    upperCol (cutEdgeIndex c) = c.succ := by
  apply Fin.ext
  rfl

theorem cutState_horizontal_physical_iff {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) (r : Fin m) :
    (cutState hm H c).horizontal r = true ↔
      toEdge hm (Sum.inr (Sum.inl (r, cutEdgeIndex c))) ∈ H.edgeSet := by
  rw [cutState_horizontal_iff]
  simp only [toEdge, sourceVertex, targetVertex, lowerCol_cutEdgeIndex,
    upperCol_cutEdgeIndex, SimpleGraph.mem_edgeSet]

theorem cutState_diagonal_physical_iff {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) (r : Fin m) :
    (cutState hm H c).diagonal r = true ↔
      toEdge hm (Sum.inr (Sum.inr (r, cutEdgeIndex c))) ∈ H.edgeSet := by
  rw [cutState_diagonal_iff]
  simp only [toEdge, sourceVertex, targetVertex, lowerCol_cutEdgeIndex,
    upperCol_cutEdgeIndex, SimpleGraph.mem_edgeSet]

/-- A full outgoing cut of an actual Hamiltonian cycle forces width two. -/
theorem width_two_of_cutState_full {m n : ℕ} (hm : 3 ≤ m)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 1))
    (hfull : FullOutgoing (cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) c)) :
    n + 2 = 2 := by
  apply TriangularCutSaturation.length_two_of_fullCrossingAt hm
    (SimpleGraph.fromEdgeSet C.edgeSet) (cutEdgeIndex c)
  · simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_connected hC
  · intro x
    simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_ncard hC x
  · intro r
    simpa only [lowerCol_cutEdgeIndex, upperCol_cutEdgeIndex] using
      And.intro ((cutState_horizontal_iff hm _ c r).mp (hfull r).1)
        ((cutState_diagonal_iff hm _ c r).mp (hfull r).2)

/-- Every cut in an actual Hamiltonian cycle of width at least three is nonfull. -/
theorem cutState_not_full {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 1)) :
    ¬ FullOutgoing (cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) c) := by
  intro hfull
  have h := width_two_of_cutState_full hm C hC c hfull
  omega

/-- Actual occurrence and the full-crossing exclusion place every such cut in the core. -/
noncomputable def coreAtCut {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 1)) : CoreState hm :=
  ⟨cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) c,
    cutState_occurs hm C hC c, cutState_not_full hm hn C hC c⟩

@[simp] theorem coreAtCut_val {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (c : Fin (n + 1)) :
    (coreAtCut hm hn C hC c).val = cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) c := rfl

/-- A first-column mask realized by an actual cycle whose first cut is `s`. -/
def InitialRealized {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm) (a : RowMask m) : Prop :=
  ∃ n : ℕ, ∃ v : Vertex m (n + 2), ∃ C : (graph m (n + 2) hm).Walk v v,
    C.IsHamiltonianCycle ∧
      cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) 0 = s.val ∧
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) 0 = a

/-- A new-column mask realized between two consecutive nonterminal cuts.
For a width `n+2` witness, `i : Fin n` indexes exactly the `n` local steps. -/
def LocalRealized {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) (a : RowMask m) : Prop :=
  ∃ n : ℕ, ∃ i : Fin n, ∃ v : Vertex m (n + 2),
    ∃ C : (graph m (n + 2) hm).Walk v v,
      C.IsHamiltonianCycle ∧
        cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) i.castSucc = s.val ∧
        cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) i.succ = t.val ∧
        verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) i.succ.castSucc = a

/-- A final-column mask realized at last cut `s` by a cycle of total parity `p`. -/
def TerminalRealized {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (s : CoreState hm) (a : RowMask m) : Prop :=
  ∃ n : ℕ, ∃ v : Vertex m (n + 2), ∃ C : (graph m (n + 2) hm).Walk v v,
    C.IsHamiltonianCycle ∧
      cutState hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last n) = s.val ∧
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last (n + 1)) = a ∧
      typeParity hm C = p

/-- Only the vertical mask is data; all actual witnesses lie in its property. -/
def InitialLabel {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm) :=
  {a : RowMask m // InitialRealized hm s a}

/-- Only the vertical mask is data; the two cuts must co-occur in one actual cycle. -/
def LocalLabel {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) :=
  {a : RowMask m // LocalRealized hm s t a}

/-- Only the vertical mask is data; the terminal class uses actual cycle parity. -/
def TerminalLabel {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm) :=
  {a : RowMask m // TerminalRealized hm p s a}

instance {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm) : Finite (InitialLabel hm s) := by
  unfold InitialLabel
  infer_instance

instance {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) : Finite (LocalLabel hm s t) := by
  unfold LocalLabel
  infer_instance

instance {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm) :
    Finite (TerminalLabel hm p s) := by
  unfold TerminalLabel
  infer_instance

noncomputable instance {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm) :
    Fintype (InitialLabel hm s) := Fintype.ofFinite _

noncomputable instance {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) :
    Fintype (LocalLabel hm s t) := Fintype.ofFinite _

noncomputable instance {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm) :
    Fintype (TerminalLabel hm p s) := Fintype.ofFinite _

theorem initialLabel_finite {m : ℕ} (hm : 3 ≤ m) (s : CoreState hm) :
    Finite (InitialLabel hm s) := inferInstance

theorem localLabel_finite {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) :
    Finite (LocalLabel hm s t) := inferInstance

theorem terminalLabel_finite {m : ℕ} (hm : 3 ≤ m) (p : ZMod 2) (s : CoreState hm) :
    Finite (TerminalLabel hm p s) := inferInstance

/-- A genuine cycle supplies the initial mask label at its first core cut. -/
noncomputable def initialLabelOfCycle {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) : InitialLabel hm (coreAtCut hm hn C hC 0) :=
  ⟨verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) 0, n, v, C, hC, rfl, rfl⟩

/-- A genuine cycle supplies every consecutive-cut local mask label. -/
noncomputable def localLabelOfCycle {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (i : Fin n) :
    LocalLabel hm (coreAtCut hm hn C hC i.castSucc) (coreAtCut hm hn C hC i.succ) :=
  ⟨verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) i.succ.castSucc,
    n, i, v, C, hC, rfl, rfl, rfl⟩

/-- A genuine cycle supplies the terminal mask label in its actual parity class. -/
noncomputable def terminalLabelOfCycle {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    TerminalLabel hm (typeParity hm C) (coreAtCut hm hn C hC (Fin.last n)) :=
  ⟨verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last (n + 1)),
    n, v, C, hC, rfl, rfl, rfl⟩

@[simp] theorem initialLabelOfCycle_val {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    (initialLabelOfCycle hm hn C hC).val =
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) 0 := rfl

@[simp] theorem localLabelOfCycle_val {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (i : Fin n) :
    (localLabelOfCycle hm hn C hC i).val =
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) i.succ.castSucc := rfl

@[simp] theorem terminalLabelOfCycle_val {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    (terminalLabelOfCycle hm hn C hC).val =
      verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet) (Fin.last (n + 1)) := rfl

end TriangularCylinder.Transfer
