import WeightedCylinderEncoding

/-!
# Complete physical exterior prescriptions for one free interval

`σ : ColumnGeometry m (n + 2)` gives a selected/absent Boolean value for
every physical V/H/D edge. For `a ≤ b ≤ n`, the free slots are precisely
`Hᵢ,Dᵢ,Vᵢ₊₁` with `a ≤ i < b`. Entries of `σ` at these free slots are
ignored. Thus different total geometries may describe the same exterior
prescription; no unique observation code or normalization is asserted.

The event below tests actual unordered-edge membership for every exterior
physical ID. Since physical IDs biject with graph edges when `m ≥ 3`, it
fixes both selected and absent exterior graph edges. It places no condition
on extraneous nonedges, which cannot occur in the counted selections.
There is no realizability premise on `σ`: impossible prescriptions are
allowed and will simply receive zero total weight.

Initial, local and terminal filters follow the frozen once-only physical
ownership convention. No positivity or weight bounds are needed here.
-/

open scoped BigOperators Matrix

namespace TriangularCylinder.Transfer

open CountedHamiltonian TriangularEdgeEncoding

/-- A free local slot has the indicated source-cut index. -/
def freeLocalSlot (a b i : ℕ) : Prop := a ≤ i ∧ i < b

/-- Physical edges owned by free local slots; `V₀` is never free. -/
def freePhysicalId {m n : ℕ} (a b : ℕ) : EdgeId m (n + 2) → Prop
  | .inl (_, c) => 0 < c.val ∧ freeLocalSlot a b (c.val - 1)
  | .inr (.inl (_, c)) => freeLocalSlot a b c.val
  | .inr (.inr (_, c)) => freeLocalSlot a b c.val

/-- Exact selected-and-absent agreement on every exterior physical edge. -/
def ExteriorAgrees {m n : ℕ} (hm : 3 ≤ m)
    (σ : ColumnGeometry m (n + 2)) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) : Prop :=
  ∀ id : EdgeId m (n + 2), ¬ freePhysicalId a b id →
    (toEdge hm id ∈ E ↔ geometryFlag σ id = true)

/-- The same exterior agreement expressed directly on physical mask data. -/
def GeometryExteriorAgrees {m n : ℕ}
    (σ : ColumnGeometry m (n + 2)) (a b : ℕ)
    (g : ColumnGeometry m (n + 2)) : Prop :=
  ∀ id : EdgeId m (n + 2), ¬ freePhysicalId a b id →
    geometryFlag g id = geometryFlag σ id

/-- The three masks owned by one local slot match their prescribed values. -/
def localMaskAgreement {m n : ℕ} (σ : ColumnGeometry m (n + 2))
    (i : Fin n) (h d v : RowMask m) : Prop :=
  h = σ.2.1 (cutEdgeIndex i.castSucc) ∧
    d = σ.2.2 (cutEdgeIndex i.castSucc) ∧ v = σ.1 i.succ.castSucc

/-- The terminal slot owns the final cut and the last vertical column. -/
def terminalMaskAgreement {m n : ℕ} (σ : ColumnGeometry m (n + 2))
    (h d v : RowMask m) : Prop :=
  h = σ.2.1 (cutEdgeIndex (Fin.last n)) ∧
    d = σ.2.2 (cutEdgeIndex (Fin.last n)) ∧ v = σ.1 (Fin.last (n + 1))

variable {R : Type*} [CommSemiring R]

/-- Zero-one indicator of the actual physical exterior event. -/
noncomputable def exteriorIndicator {m n : ℕ} (hm : 3 ≤ m)
    (σ : ColumnGeometry m (n + 2)) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) : R := by
  classical
  exact if ExteriorAgrees hm σ a b E then 1 else 0

/-- `V₀` is prescribed independently of the free local interval. -/
noncomputable def initialExteriorFilter {m n : ℕ} (hm : 3 ≤ m)
    (σ : ColumnGeometry m (n + 2))
    (s : CoreState hm) (z : InitialLabel hm s) : R := by
  classical
  exact if z.val = σ.1 0 then 1 else 0

/-- Free local slots contribute filter one; every exterior slot fixes all three masks. -/
noncomputable def localExteriorFilter {m n : ℕ} (hm : 3 ≤ m)
    (σ : ColumnGeometry m (n + 2)) (a b : ℕ) (i : Fin n)
    (s t : CoreState hm) (z : LocalLabel hm s t) : R := by
  classical
  exact if freeLocalSlot a b i.val then 1 else
    if localMaskAgreement σ i s.val.horizontal s.val.diagonal z.val then 1 else 0

/-- The terminal slot is exterior when `b ≤ n`. -/
noncomputable def terminalExteriorFilter {m n : ℕ} (hm : 3 ≤ m)
    (σ : ColumnGeometry m (n + 2)) {p : ZMod 2}
    (s : CoreState hm) (z : TerminalLabel hm p s) : R := by
  classical
  exact if terminalMaskAgreement σ s.val.horizontal s.val.diagonal z.val then 1 else 0

noncomputable def exteriorInitialWeight {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (s : CoreState hm) (z : InitialLabel hm s) : R :=
  initialPhysicalWeight hm w s z * initialExteriorFilter hm σ s z

noncomputable def exteriorLocalWeight {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (i : Fin n) (s t : CoreState hm) (z : LocalLabel hm s t) : R :=
  localPhysicalWeight hm w i s t z * localExteriorFilter hm σ a b i s t z

noncomputable def exteriorTerminalWeight {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    {p : ZMod 2} (s : CoreState hm) (z : TerminalLabel hm p s) : R :=
  terminalPhysicalWeight hm w s z * terminalExteriorFilter hm σ s z

noncomputable def exteriorInitialVector {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2)) : CoreState hm → R :=
  CylinderTransfer.weightedInitialVector (InitialLabel hm) (exteriorInitialWeight hm w σ)

noncomputable def exteriorLocalMatrix {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (i : Fin n) : Matrix (CoreState hm) (CoreState hm) R := by
  classical
  exact CylinderTransfer.weightedTransitionMatrix (LocalLabel hm) (exteriorLocalWeight hm w σ a b i)

noncomputable def exteriorTerminalVector {m n : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2)) : CoreState hm → R :=
  CylinderTransfer.weightedTerminalVector (TerminalLabel hm p) (exteriorTerminalWeight hm w σ)

/-- The filtered weight on the existing dependent accepted object. -/
noncomputable def exteriorAcceptedWeight {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (x : AcceptedObject hm p n) : R :=
  CylinderTransfer.acceptedWeight (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p)
    (exteriorInitialWeight hm w σ) (exteriorLocalWeight hm w σ a b)
    (exteriorTerminalWeight hm w σ) x

/-- Physical products summed over the original unordered parity selections,
with the complete exterior-event indicator. This is not a label-count definition. -/
noncomputable def exteriorParityCount {m n : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2)) (a b : ℕ) : R := by
  classical
  exact ∑ s : ParitySelection hm p (n + 2),
    selectionProduct (graph m (n + 2) hm) w s.val * exteriorIndicator hm σ a b s.val.val

#print axioms freeLocalSlot
#print axioms freePhysicalId
#print axioms ExteriorAgrees
#print axioms GeometryExteriorAgrees
#print axioms localMaskAgreement
#print axioms terminalMaskAgreement
#print axioms exteriorIndicator
#print axioms initialExteriorFilter
#print axioms localExteriorFilter
#print axioms terminalExteriorFilter
#print axioms exteriorInitialWeight
#print axioms exteriorLocalWeight
#print axioms exteriorTerminalWeight
#print axioms exteriorInitialVector
#print axioms exteriorLocalMatrix
#print axioms exteriorTerminalVector
#print axioms exteriorAcceptedWeight
#print axioms exteriorParityCount

end TriangularCylinder.Transfer
