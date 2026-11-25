import WeightedCylinderEncoding
import CoreLabelFlip

/-!
# Physical local and terminal weights under the actual core flip

The existing label equivalences preserve every mask and row index. All
weights are evaluated in the same fixed cylinder, at the same column or
cut index. The realizability witnesses are not counted or reweighted.
No initial-vector symmetry or positivity premise is used.
-/

namespace TriangularCylinder.Transfer

open scoped BigOperators

variable {R : Type*}

section Products

variable [CommMonoid R]

/-- The forward local-label equivalence preserves the complete physical
factor, including the source H/D and the same new-column V positions. -/
theorem localPhysicalWeight_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (i : Fin n)
    (s t : CoreState hm) (a : LocalLabel hm s t) :
    localPhysicalWeight hm w i (coreFlip hm s) (coreFlip hm t)
        (localLabelFlipEquiv hm s t a) =
      localPhysicalWeight hm w i s t a := rfl

/-- The forward terminal-label equivalence preserves the final-cut H/D
and final-column V factors while changing the total-parity label. -/
theorem terminalPhysicalWeight_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (p : ZMod 2)
    (s : CoreState hm) (a : TerminalLabel hm p s) :
    terminalPhysicalWeight hm w (coreFlip hm s)
        (terminalLabelFlipEquiv hm p s a) =
      terminalPhysicalWeight hm w s a := rfl

end Products

section Sums

variable [CommSemiring R]

/-- The actual weighted local matrix has simultaneous core-flip symmetry
at each fixed position, for the unchanged physical activity field. -/
theorem weightedTransitionMatrix_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (i : Fin n) (s t : CoreState hm) :
    CylinderTransfer.weightedTransitionMatrix (LocalLabel hm) (localPhysicalWeight hm w i)
        (coreFlip hm s) (coreFlip hm t) =
      CylinderTransfer.weightedTransitionMatrix (LocalLabel hm) (localPhysicalWeight hm w i)
        s t := by
  classical
  exact (Fintype.sum_equiv (localLabelFlipEquiv hm s t) _ _
    (fun a => (localPhysicalWeight_flip hm w i s t a).symm)).symm

/-- The two actual terminal classes are paired at flipped core states,
with both finite sums evaluated in the same physical cylinder. -/
theorem weightedTerminalVector_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (p : ZMod 2) (s : CoreState hm) :
    CylinderTransfer.weightedTerminalVector (TerminalLabel hm (p + 1))
        (terminalPhysicalWeight hm w) (coreFlip hm s) =
      CylinderTransfer.weightedTerminalVector (TerminalLabel hm p)
        (terminalPhysicalWeight hm w) s := by
  classical
  exact (Fintype.sum_equiv (terminalLabelFlipEquiv hm p s) _ _
    (fun a => (terminalPhysicalWeight_flip hm w p s a).symm)).symm

/-- The endpoint orientation used by the matrix contraction theorem:
the parity-one terminal weight at `s` is the parity-zero weight at its flip. -/
theorem weightedTerminalVector_one_eq_zero_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (s : CoreState hm) :
    CylinderTransfer.weightedTerminalVector (TerminalLabel hm 1)
        (terminalPhysicalWeight hm w) s =
      CylinderTransfer.weightedTerminalVector (TerminalLabel hm 0)
        (terminalPhysicalWeight hm w) (coreFlip hm s) := by
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [htwo] using (weightedTerminalVector_flip hm w 1 s).symm

end Sums

#print axioms localPhysicalWeight_flip
#print axioms terminalPhysicalWeight_flip
#print axioms weightedTransitionMatrix_flip
#print axioms weightedTerminalVector_flip
#print axioms weightedTerminalVector_one_eq_zero_flip

end TriangularCylinder.Transfer
