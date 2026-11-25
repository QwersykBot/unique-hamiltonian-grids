import ColumnCut
import PhysicalEdges
import TriangularParity
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi

/-!
# Raw states at a complete boundary column

Outgoing horizontal and diagonal masks record physical selected edges.
The Boolean relation records reachability inside the actual prefix graph.
Parity sums selected physical identifiers assigned to their source column,
including outgoing diagonals at the cut. Relation entries are never treated
as physical edges. Actual occurrence is defined separately using a standard
Hamiltonian cycle in the actual ambient graph. No transition, sufficiency,
counting, or closure of actual states under parity flip is asserted.
-/

namespace TriangularCylinder

/-- Finite raw data at the complete last processed column. -/
structure RawBoundaryState (m : ℕ) where
  horizontal : Fin m → Bool
  diagonal : Fin m → Bool
  reach : Fin m → Fin m → Bool
  parity : ZMod 2

namespace RawBoundaryState

def toTuple {m : ℕ} (s : RawBoundaryState m) :
    (Fin m → Bool) × (Fin m → Bool) × (Fin m → Fin m → Bool) × ZMod 2 :=
  (s.horizontal, s.diagonal, s.reach, s.parity)

theorem toTuple_injective {m : ℕ} : Function.Injective (toTuple (m := m)) := by
  intro s t h
  cases s
  cases t
  simp only [toTuple, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

@[ext] theorem ext {m : ℕ} {s t : RawBoundaryState m}
    (hH : s.horizontal = t.horizontal) (hD : s.diagonal = t.diagonal)
    (hR : s.reach = t.reach) (hP : s.parity = t.parity) : s = t := by
  apply toTuple_injective
  exact Prod.ext hH (Prod.ext hD (Prod.ext hR hP))

noncomputable instance (m : ℕ) : Fintype (RawBoundaryState m) :=
  Fintype.ofInjective toTuple toTuple_injective

theorem finite (m : ℕ) : Finite (RawBoundaryState m) := inferInstance

/-- Flip only the raw parity coordinate. -/
def flip {m : ℕ} (s : RawBoundaryState m) : RawBoundaryState m :=
  { s with parity := s.parity + 1 }

@[simp] theorem flip_horizontal {m : ℕ} (s : RawBoundaryState m) :
    (flip s).horizontal = s.horizontal := rfl

@[simp] theorem flip_diagonal {m : ℕ} (s : RawBoundaryState m) :
    (flip s).diagonal = s.diagonal := rfl

@[simp] theorem flip_reach {m : ℕ} (s : RawBoundaryState m) :
    (flip s).reach = s.reach := rfl

@[simp] theorem flip_parity {m : ℕ} (s : RawBoundaryState m) :
    (flip s).parity = s.parity + 1 := rfl

theorem flip_involutive {m : ℕ} : Function.Involutive (flip (m := m)) := by
  intro s
  cases s
  simp only [flip, add_assoc, ZModModule.add_self, add_zero]

theorem flip_ne {m : ℕ} (s : RawBoundaryState m) : flip s ≠ s := by
  intro h
  have hp := congrArg RawBoundaryState.parity h
  change s.parity + 1 = s.parity at hp
  have h10 : (1 : ZMod 2) = 0 := add_left_cancel (hp.trans (add_zero s.parity).symm)
  exact one_ne_zero h10

end RawBoundaryState

namespace BoundaryState

open SimpleGraph TriangularEdgeEncoding
open scoped BigOperators

def boundaryCol (j k : ℕ) : Fin (j + 1 + k) := ⟨j, by omega⟩

def nextCol {j k : ℕ} (hk : 1 ≤ k) : Fin (j + 1 + k) := ⟨j + 1, by omega⟩

def horizontalId {m j k : ℕ} (hk : 1 ≤ k) (r : Fin m) : EdgeId m (j + 1 + k) :=
  Sum.inr (Sum.inl (r, ⟨j, by omega⟩))

def diagonalId {m j k : ℕ} (hk : 1 ≤ k) (r : Fin m) : EdgeId m (j + 1 + k) :=
  Sum.inr (Sum.inr (r, ⟨j, by omega⟩))

@[simp] theorem horizontalId_edge {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (r : Fin m) :
    toEdge hm (horizontalId (j := j) hk r) =
      s((r, boundaryCol j k), (r, nextCol hk)) := rfl

@[simp] theorem diagonalId_edge {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (r : Fin m) :
    toEdge hm (diagonalId (j := j) hk r) =
      s((r, boundaryCol j k), (rowSucc hm r, nextCol hk)) := rfl

/-- Exactly the selected physical identifiers assigned by the current cut. -/
noncomputable def assignedIds {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + k))) : Finset (EdgeId m (j + 1 + k)) := by
  classical
  exact Finset.univ.filter fun e => toEdge hm e ∈ H.edgeSet ∧ (sourceVertex e).2.val ≤ j

@[simp] theorem mem_assignedIds {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (e : EdgeId m (j + 1 + k)) :
    e ∈ assignedIds hm H ↔ toEdge hm e ∈ H.edgeSet ∧ (sourceVertex e).2.val ≤ j := by
  classical
  simp [assignedIds]

noncomputable def assignedParity {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + k))) : ZMod 2 :=
  ∑ e ∈ assignedIds hm H, meridianWeight hm (toEdge hm e)

/-- Encode an actual selected graph at the complete last processed column.
The outgoing edge masks and assigned parity include cut-j outgoing edges;
the reachability matrix uses only the prefix restriction. -/
noncomputable def stateAt {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) : RawBoundaryState m := by
  classical
  exact {
    horizontal := fun r => decide (toEdge hm (horizontalId (j := j) hk r) ∈ H.edgeSet)
    diagonal := fun r => decide (toEdge hm (diagonalId (j := j) hk r) ∈ H.edgeSet)
    reach := fun r s => decide ((ColumnCut.prefixPart j k H).Reachable (Sum.inr r) (Sum.inr s))
    parity := assignedParity hm H
  }

theorem stateAt_horizontal_physical_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    (stateAt hm hk H).horizontal r = true ↔
      toEdge hm (horizontalId (j := j) hk r) ∈ H.edgeSet := by
  classical
  simp only [stateAt, decide_eq_true_eq]

theorem stateAt_diagonal_physical_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    (stateAt hm hk H).diagonal r = true ↔
      toEdge hm (diagonalId (j := j) hk r) ∈ H.edgeSet := by
  classical
  simp only [stateAt, decide_eq_true_eq]

/-- The horizontal mask tests the actual row-r physical edge across cut j. -/
theorem stateAt_horizontal_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    (stateAt hm hk H).horizontal r = true ↔
      H.Adj (r, boundaryCol j k) (r, nextCol hk) := by
  rw [stateAt_horizontal_physical_iff, horizontalId_edge, SimpleGraph.mem_edgeSet]

/-- The diagonal mask tests the consistently oriented physical edge across cut j. -/
theorem stateAt_diagonal_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    (stateAt hm hk H).diagonal r = true ↔
      H.Adj (r, boundaryCol j k) (rowSucc hm r, nextCol hk) := by
  rw [stateAt_diagonal_physical_iff, diagonalId_edge, SimpleGraph.mem_edgeSet]

theorem stateAt_reach_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r s : Fin m) :
    (stateAt hm hk H).reach r s = true ↔
      (ColumnCut.prefixPart j k H).Reachable (Sum.inr r) (Sum.inr s) := by
  classical
  simp only [stateAt, decide_eq_true_eq]

theorem stateAt_reach_refl {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    (stateAt hm hk H).reach r r = true :=
  (stateAt_reach_iff hm hk H r r).mpr (SimpleGraph.Reachable.refl _)

theorem stateAt_reach_symm {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r s : Fin m) :
    (stateAt hm hk H).reach r s = (stateAt hm hk H).reach s r := by
  classical
  exact decide_eq_decide.mpr SimpleGraph.reachable_comm

theorem stateAt_reach_trans {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r s t : Fin m)
    (hrs : (stateAt hm hk H).reach r s = true)
    (hst : (stateAt hm hk H).reach s t = true) :
    (stateAt hm hk H).reach r t = true :=
  (stateAt_reach_iff hm hk H r t).mpr
    (((stateAt_reach_iff hm hk H r s).mp hrs).trans ((stateAt_reach_iff hm hk H s t).mp hst))

theorem stateAt_reach_equivalence {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) :
    Equivalence (fun r s => (stateAt hm hk H).reach r s = true) := by
  refine ⟨stateAt_reach_refl hm hk H, ?_, ?_⟩
  · intro r s h
    rw [stateAt_reach_symm hm hk H s r]
    exact h
  · intro r s t hrs hst
    exact stateAt_reach_trans hm hk H r s t hrs hst

/-- The parity field is exactly the finite selected-physical-ID sum with
source column at most j; no relation edge contributes. -/
theorem stateAt_parity {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) :
    (stateAt hm hk H).parity = ∑ e ∈ assignedIds hm H, meridianWeight hm (toEdge hm e) := rfl

theorem horizontalId_assigned_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    horizontalId (j := j) hk r ∈ assignedIds hm H ↔
      toEdge hm (horizontalId (j := j) hk r) ∈ H.edgeSet := by
  rw [mem_assignedIds]
  simp only [horizontalId, sourceVertex, lowerCol, le_refl, and_true]

/-- In particular, a selected outgoing diagonal is assigned at this cut. -/
theorem diagonalId_assigned_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r : Fin m) :
    diagonalId (j := j) hk r ∈ assignedIds hm H ↔
      toEdge hm (diagonalId (j := j) hk r) ∈ H.edgeSet := by
  rw [mem_assignedIds]
  simp only [diagonalId, sourceVertex, lowerCol, le_refl, and_true]

theorem nextColumn_ne_prefixVertex {m j k : ℕ} (hk : 1 ≤ k) (r : Fin m)
    (x : Vertex m j ⊕ Fin m) :
    (r, nextCol (j := j) hk) ≠ ColumnCut.prefixVertex j k x := by
  intro h
  have hc := congrArg (fun v : Vertex m (j + 1 + k) => v.2.val) h
  cases x with
  | inl x =>
    change j + 1 = x.2.val at hc
    have hx := x.2.isLt
    omega
  | inr b =>
    change j + 1 = j at hc
    omega

/-- Its target is outside the actual prefix vertex set, so assigning the
outgoing diagonal to parity does not put it into prefix connectivity. -/
theorem diagonal_target_not_prefix {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (r : Fin m) (x : Vertex m j ⊕ Fin m) :
    targetVertex hm (diagonalId (j := j) hk r) ≠ ColumnCut.prefixVertex j k x :=
  nextColumn_ne_prefixVertex hk (rowSucc hm r) x

/-- A walk in the actual ambient graph selects only actual ambient edges. -/
theorem cycle_selectedGraph_le {m L : ℕ} (hm : 3 ≤ m) {v : Vertex m L}
    (C : (graph m L hm).Walk v v) :
    SimpleGraph.fromEdgeSet C.edgeSet ≤ graph m L hm := by
  intro x y h
  exact (SimpleGraph.mem_edgeSet _).mp (C.edges_subset_edgeSet h.1)

/-- Actual occurrence at a nonterminal column cut of a standard Hamiltonian
cycle in the actual consistently triangulated cylinder. -/
def Occurs {m : ℕ} (hm : 3 ≤ m) (s : RawBoundaryState m) : Prop :=
  ∃ j k : ℕ, ∃ hk : 1 ≤ k, ∃ v : Vertex m (j + 1 + k),
    ∃ C : (graph m (j + 1 + k) hm).Walk v v,
      C.IsHamiltonianCycle ∧ stateAt hm hk (SimpleGraph.fromEdgeSet C.edgeSet) = s

theorem occurs_stateAt {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {v : Vertex m (j + 1 + k)} (C : (graph m (j + 1 + k) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) :
    Occurs hm (stateAt hm hk (SimpleGraph.fromEdgeSet C.edgeSet)) :=
  ⟨j, k, hk, v, C, hC, rfl⟩

def ActualState {m : ℕ} (hm : 3 ≤ m) := {s : RawBoundaryState m // Occurs hm s}

instance {m : ℕ} (hm : 3 ≤ m) : Finite (ActualState hm) := by
  unfold ActualState
  infer_instance

noncomputable instance {m : ℕ} (hm : 3 ≤ m) : Fintype (ActualState hm) := Fintype.ofFinite _

theorem actualState_finite {m : ℕ} (hm : 3 ≤ m) : Finite (ActualState hm) := inferInstance

#print axioms RawBoundaryState.finite
#print axioms RawBoundaryState.ext
#print axioms RawBoundaryState.flip_involutive
#print axioms RawBoundaryState.flip_ne
#print axioms stateAt_horizontal_physical_iff
#print axioms stateAt_diagonal_physical_iff
#print axioms stateAt_horizontal_iff
#print axioms stateAt_diagonal_iff
#print axioms stateAt_reach_iff
#print axioms stateAt_reach_refl
#print axioms stateAt_reach_symm
#print axioms stateAt_reach_trans
#print axioms stateAt_reach_equivalence
#print axioms stateAt_parity
#print axioms mem_assignedIds
#print axioms horizontalId_assigned_iff
#print axioms diagonalId_assigned_iff
#print axioms diagonal_target_not_prefix
#print axioms cycle_selectedGraph_le
#print axioms occurs_stateAt
#print axioms actualState_finite

end BoundaryState
end TriangularCylinder
