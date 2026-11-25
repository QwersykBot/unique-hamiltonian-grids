import ExteriorGeometry
import WeightedCylinderSymmetry
import WeightedCylinderBounds

/-!
# Exterior filters under the actual core parity flip

The same complete exterior prescription and the same physical activity
field occur on both sides. The existing label equivalences preserve the
source H/D masks and the new-column or terminal V mask, without moving
any physical position. The filters therefore preserve local and terminal
symmetry, including absent-edge constraints.

These local identities need no interval-validity or event-realizability
premise. A free slot is exactly the original weighted local matrix.
The real nonnegativity statements reuse the frozen global ambient-edge
bounds. No initial-vector symmetry or conditional probability is asserted.
-/

namespace TriangularCylinder.Transfer

open scoped BigOperators
open TriangularEdgeEncoding

section Symmetry

variable {R : Type*} [CommSemiring R]

/-- The forward local-label equivalence preserves the physical factor
and its complete exterior filter at the same source-cut index. -/
theorem exteriorLocalWeight_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (i : Fin n) (s t : CoreState hm) (z : LocalLabel hm s t) :
    exteriorLocalWeight hm w σ a b i (coreFlip hm s) (coreFlip hm t)
        (localLabelFlipEquiv hm s t z) =
      exteriorLocalWeight hm w σ a b i s t z := rfl

/-- The forward terminal-label equivalence preserves the prescribed
terminal masks and all their physical factors. -/
theorem exteriorTerminalWeight_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (p : ZMod 2) (s : CoreState hm) (z : TerminalLabel hm p s) :
    exteriorTerminalWeight hm w σ (coreFlip hm s)
        (terminalLabelFlipEquiv hm p s z) =
      exteriorTerminalWeight hm w σ s z := rfl

/-- Filtering by the same exterior masks preserves simultaneous
core-flip symmetry of every local matrix entry. -/
theorem exteriorLocalMatrix_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (i : Fin n) (s t : CoreState hm) :
    exteriorLocalMatrix hm w σ a b i (coreFlip hm s) (coreFlip hm t) =
      exteriorLocalMatrix hm w σ a b i s t := by
  classical
  exact (Fintype.sum_equiv (localLabelFlipEquiv hm s t) _ _
    (fun z => (exteriorLocalWeight_flip hm w σ a b i s t z).symm)).symm

/-- The same terminal exterior prescription pairs parity `p` with
parity `p + 1` at the flipped state. -/
theorem exteriorTerminalVector_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (p : ZMod 2) (s : CoreState hm) :
    exteriorTerminalVector hm (p + 1) w σ (coreFlip hm s) =
      exteriorTerminalVector hm p w σ s := by
  classical
  exact (Fintype.sum_equiv (terminalLabelFlipEquiv hm p s) _ _
    (fun z => (exteriorTerminalWeight_flip hm w σ p s z).symm)).symm

/-- The endpoint orientation used by the contraction estimate. -/
theorem exteriorTerminalVector_one_eq_zero_flip {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (s : CoreState hm) :
    exteriorTerminalVector hm 1 w σ s =
      exteriorTerminalVector hm 0 w σ (coreFlip hm s) := by
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [htwo] using (exteriorTerminalVector_flip hm w σ 1 s).symm

/-- An unconstrained local slot is the original physical weighted
transition matrix, independently of the values recorded in `σ`. -/
theorem exteriorLocalMatrix_eq_unfiltered {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (i : Fin n) (hfree : freeLocalSlot a b i.val) :
    exteriorLocalMatrix hm w σ a b i =
      CylinderTransfer.weightedTransitionMatrix (LocalLabel hm) (localPhysicalWeight hm w i) := by
  classical
  funext s t
  change (∑ z : LocalLabel hm s t, exteriorLocalWeight hm w σ a b i s t z) =
    ∑ z : LocalLabel hm s t, localPhysicalWeight hm w i s t z
  apply Finset.sum_congr rfl
  intro z _
  simp only [exteriorLocalWeight, localExteriorFilter, if_pos hfree, mul_one]

end Symmetry

section Nonnegativity

/-- The prescribed initial factor is nonnegative under the existing
global bounds on ambient graph edges. -/
theorem exteriorInitialWeight_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2))
    (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (s : CoreState hm) (z : InitialLabel hm s) :
    0 ≤ exteriorInitialWeight hm w σ s z := by
  classical
  unfold exteriorInitialWeight
  refine mul_nonneg
    (WeightedCylinderBounds.initialPhysicalWeight_nonneg hm w hepsilon hw s z) ?_
  unfold initialExteriorFilter
  split_ifs <;> norm_num

/-- Prescribed and free local factors are both nonnegative. -/
theorem exteriorLocalWeight_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2))
    (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (a b : ℕ) (i : Fin n) (s t : CoreState hm) (z : LocalLabel hm s t) :
    0 ≤ exteriorLocalWeight hm w σ a b i s t z := by
  classical
  unfold exteriorLocalWeight
  refine mul_nonneg
    (WeightedCylinderBounds.localPhysicalWeight_nonneg hm w hepsilon hw i s t z) ?_
  unfold localExteriorFilter
  split_ifs <;> norm_num

/-- The prescribed terminal factor is nonnegative in either parity class. -/
theorem exteriorTerminalWeight_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2))
    (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    {p : ZMod 2} (s : CoreState hm) (z : TerminalLabel hm p s) :
    0 ≤ exteriorTerminalWeight hm w σ s z := by
  classical
  unfold exteriorTerminalWeight
  refine mul_nonneg
    (WeightedCylinderBounds.terminalPhysicalWeight_nonneg hm w hepsilon hw s z) ?_
  unfold terminalExteriorFilter
  split_ifs <;> norm_num

/-- The filtered initial vector is nonnegative; no flip symmetry is required. -/
theorem exteriorInitialVector_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2))
    (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (s : CoreState hm) :
    0 ≤ exteriorInitialVector hm w σ s := by
  change 0 ≤ ∑ z : InitialLabel hm s, exteriorInitialWeight hm w σ s z
  exact Finset.sum_nonneg (fun z _ => exteriorInitialWeight_nonneg hm w σ hepsilon hw s z)

/-- Every entry of the filtered local matrix is nonnegative. -/
theorem exteriorLocalMatrix_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2))
    (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (a b : ℕ) (i : Fin n) (s t : CoreState hm) :
    0 ≤ exteriorLocalMatrix hm w σ a b i s t := by
  change 0 ≤ ∑ z : LocalLabel hm s t, exteriorLocalWeight hm w σ a b i s t z
  exact Finset.sum_nonneg
    (fun z _ => exteriorLocalWeight_nonneg hm w σ hepsilon hw a b i s t z)

/-- Both filtered terminal vectors are nonnegative. -/
theorem exteriorTerminalVector_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2))
    (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (p : ZMod 2) (s : CoreState hm) :
    0 ≤ exteriorTerminalVector hm p w σ s := by
  change 0 ≤ ∑ z : TerminalLabel hm p s, exteriorTerminalWeight hm w σ s z
  exact Finset.sum_nonneg (fun z _ => exteriorTerminalWeight_nonneg hm w σ hepsilon hw s z)

end Nonnegativity

#print axioms exteriorLocalWeight_flip
#print axioms exteriorTerminalWeight_flip
#print axioms exteriorLocalMatrix_flip
#print axioms exteriorTerminalVector_flip
#print axioms exteriorTerminalVector_one_eq_zero_flip
#print axioms exteriorLocalMatrix_eq_unfiltered
#print axioms exteriorInitialWeight_nonneg
#print axioms exteriorLocalWeight_nonneg
#print axioms exteriorTerminalWeight_nonneg
#print axioms exteriorInitialVector_nonneg
#print axioms exteriorLocalMatrix_nonneg
#print axioms exteriorTerminalVector_nonneg

end TriangularCylinder.Transfer
