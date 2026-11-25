import AcceptedRealization
import AcceptedUniqueness

/-!
# Exact correspondence with undirected Hamiltonian edge selections

Every accepted object reconstructs an actual Hamiltonian edge set in its
stated parity class. The canonical encoding and this reconstruction are
mutual inverses for cylinders of width at least three. Thus the existing
undirected parity counts equal the actual finite accepted-object counts,
and their transfer-matrix formula follows from the generic counting theorem.
No asymptotic, support-connectivity, or topology claim is made here.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding CountedHamiltonian AcceptedRealization
open scoped BigOperators Matrix

noncomputable local instance {m : ℕ} (hm : 3 ≤ m) : DecidableEq (CoreState hm) :=
  Classical.decEq _

/-- Reconstruct the counted Hamiltonian selection in the recorded parity class. -/
def acceptedSelection {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : ParitySelection hm p (n + 2) :=
  acceptedSelectionOfRealization w (acceptedEdges_hasHamiltonianRealization w)

@[simp] theorem acceptedSelection_edges {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : (acceptedSelection w).val.val = acceptedEdges w := rfl

/-- Encoding a counted selection and reconstructing it recovers that same selection. -/
theorem acceptedSelection_selectionAccepted {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (s : ParitySelection hm p (n + 2)) :
    acceptedSelection (selectionAccepted hm hn p s) = s := by
  apply Subtype.ext
  apply Subtype.ext
  exact acceptedEdges_selectionAccepted hm hn p s

/-- Reconstructing arbitrary accepted data and encoding it recovers every original choice. -/
theorem selectionAccepted_acceptedSelection {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (w : AcceptedObject hm p n) :
    selectionAccepted hm hn p (acceptedSelection w) = w :=
  selectionAccepted_of_realization hm hn w (acceptedEdges_hasHamiltonianRealization w)

/-- The exact counted-object bijection, with fixed vertex labels and no traversal multiplicity. -/
noncomputable def countedTransferEquiv {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2) :
    ParitySelection hm p (n + 2) ≃ AcceptedObject hm p n where
  toFun := selectionAccepted hm hn p
  invFun := acceptedSelection
  left_inv := acceptedSelection_selectionAccepted hm hn p
  right_inv := selectionAccepted_acceptedSelection hm hn p

/-- The existing finite filtered parity count is the cardinality of its parity subtype. -/
theorem parityCount_eq_card_paritySelection {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2) :
    parityCount m L hm p = Fintype.card (ParitySelection hm p L) := by
  classical
  simp only [parityCount, ParitySelection, Fintype.card_subtype]

/-- At width n+2≥3, the actual undirected Hamiltonian parity count is the accepted count. -/
theorem parityCount_eq_card_accepted {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2) :
    parityCount m (n + 2) hm p = Fintype.card (AcceptedObject hm p n) := by
  rw [parityCount_eq_card_paritySelection]
  exact Fintype.card_congr (countedTransferEquiv hm hn p)

/-- The exact natural-number transfer formula counts the intended undirected selections. -/
theorem parityCount_eq_transfer {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2) :
    parityCount m (n + 2) hm p =
      CylinderTransfer.initialVector (InitialLabel hm) ⬝ᵥ
        ((CylinderTransfer.transitionMatrix (LocalLabel hm) ^ n) *ᵥ
          CylinderTransfer.terminalVector (TerminalLabel hm p)) := by
  rw [parityCount_eq_card_accepted hm hn p]
  exact CylinderTransfer.card_accepted (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p) n

/-- The real-valued transfer identity is an exact cast of the counted edge-set result. -/
theorem parityCount_eq_transfer_real {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2) :
    (parityCount m (n + 2) hm p : ℝ) =
      (fun s => (Fintype.card (InitialLabel hm s) : ℝ)) ⬝ᵥ
        ((CylinderTransfer.realTransitionMatrix (LocalLabel hm) ^ n) *ᵥ
          fun s => (Fintype.card (TerminalLabel hm p s) : ℝ)) := by
  rw [parityCount_eq_card_accepted hm hn p]
  exact CylinderTransfer.card_accepted_real (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p) n

end TriangularCylinder.Transfer
