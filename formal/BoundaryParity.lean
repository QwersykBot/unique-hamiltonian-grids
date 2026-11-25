import ActualTransfer
import ColumnWeights

/-!
# Exact parity charging at actual column boundaries

All state parities remain the frozen assigned selected-physical-ID sum.
The formulas identify its source-filtered physical IDs and exact V/D
last-row charges. Boundary updates are proved separately from this base.
No second state parity or topological interpretation is introduced.
-/

namespace TriangularCylinder.BoundaryParity

open SimpleGraph TriangularEdgeEncoding BoundaryState Transfer
open scoped BigOperators

/-- All selected physical IDs of a graph, before imposing a source-column cutoff. -/
noncomputable def selectedPhysicalIds {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) : Finset (EdgeId m L) := by
  classical
  exact Finset.univ.filter fun id => toEdge hm id ∈ H.edgeSet

@[simp] theorem mem_selectedPhysicalIds {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (id : EdgeId m L) :
    id ∈ selectedPhysicalIds hm H ↔ toEdge hm id ∈ H.edgeSet := by
  classical
  simp only [selectedPhysicalIds, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The frozen assigned IDs are exactly the selected physical IDs through source column `j`. -/
theorem assignedIds_eq_filter {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + k))) :
    assignedIds hm H = (selectedPhysicalIds hm H).filter
      (fun id => (sourceVertex id).2.val ≤ j) := by
  ext id
  simp only [mem_assignedIds, Finset.mem_filter, mem_selectedPhysicalIds]

/-- The standard column mask encoding of exactly those selected physical IDs. -/
noncomputable def selectedGeometry {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) : ColumnGeometry m L :=
  geometryOfIds (selectedPhysicalIds hm H)

@[simp] theorem idsOfGeometry_selectedGeometry {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) :
    idsOfGeometry (selectedGeometry hm H) = selectedPhysicalIds hm H :=
  idsOfGeometry_geometryOfIds _

/-- The V component is the existing selected vertical mask. -/
theorem selectedGeometry_vertical {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin L) (r : Fin m) :
    (selectedGeometry hm H).1 c r = verticalMask hm H c r := by
  rw [Bool.eq_iff_iff]
  simp only [selectedGeometry, geometryOfIds, decide_eq_true_eq,
    mem_selectedPhysicalIds, verticalMask_physical_iff]

/-- The D component at an indexed cut is the frozen actual cut-state mask. -/
theorem selectedGeometry_diagonal_cutState {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) (r : Fin m) :
    (selectedGeometry hm H).2.2 c r = (cutState hm H c).diagonal r := by
  rw [Bool.eq_iff_iff]
  simp only [selectedGeometry, geometryOfIds, decide_eq_true_eq,
    mem_selectedPhysicalIds, cutState_diagonal_physical_iff]
  rfl

/-- Realizing a geometry selects exactly its marked physical IDs. -/
theorem selectedPhysicalIds_realizedEdges {m L : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m L) :
    selectedPhysicalIds hm (SimpleGraph.fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))) =
      idsOfGeometry g := by
  have hset : (SimpleGraph.fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))).edgeSet =
      (realizedEdges hm g : Set (Sym2 (Vertex m L))) :=
    CountedHamiltonian.selectedGraph_edgeSet (fun _ he => realizedEdges_mem hm g he)
  ext id
  rw [mem_selectedPhysicalIds, hset]
  change toEdge hm id ∈ (idsOfGeometry g).image (toEdge hm) ↔ id ∈ idsOfGeometry g
  constructor
  · intro h
    obtain ⟨other, hother, heq⟩ := Finset.mem_image.mp h
    exact (toEdge_injective hm heq) ▸ hother
  · intro h
    exact Finset.mem_image.mpr ⟨id, h, rfl⟩

@[simp] theorem selectedGeometry_realizedEdges {m L : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m L) :
    selectedGeometry hm (SimpleGraph.fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))) = g := by
  unfold selectedGeometry
  rw [selectedPhysicalIds_realizedEdges, geometryOfIds_idsOfGeometry]

/-- Exact assigned-ID/filter connection for any concrete geometry selection. -/
theorem assignedIds_realizedEdges {m j k : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m (j + 1 + k)) :
    assignedIds (j := j) (k := k) hm (SimpleGraph.fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m (j + 1 + k))))) =
      (idsOfGeometry g).filter (fun id => (sourceVertex id).2.val ≤ j) := by
  rw [assignedIds_eq_filter, selectedPhysicalIds_realizedEdges]

/-- The existing assigned parity is precisely the through-`j` V and D last-row charge. -/
theorem assignedParity_realizedEdges {m j k : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m (j + 1 + k)) :
    assignedParity (j := j) (k := k) hm (SimpleGraph.fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m (j + 1 + k))))) =
      (∑ c ∈ (Finset.univ : Finset (Fin (j + 1 + k))).filter (fun c => c.val ≤ j),
        if g.1 c (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ c ∈ (Finset.univ : Finset (Fin (j + 1 + k - 1))).filter (fun c => c.val ≤ j),
        if g.2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) := by
  unfold assignedParity
  rw [assignedIds_realizedEdges]
  exact sum_idsOfGeometry_filter_le_meridian_eq_lastRow hm g j

/-- Equality transport preserves the selected-ID charging formula in the original graph. -/
theorem assignedParity_comap_widthEquiv {m j k L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (h : j + 1 + k = L) :
    assignedParity hm (H.comap (widthEquiv h)) =
      ∑ id ∈ (selectedPhysicalIds hm H).filter
        (fun id => (sourceVertex id).2.val ≤ j), meridianWeight hm (toEdge hm id) := by
  subst L
  simp only [widthEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id]
  unfold assignedParity
  rw [assignedIds_eq_filter]

/-- Indexed actual-state parity uses the original graph's physical IDs and source cutoff. -/
theorem cutState_parity_eq_selected_filter {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) :
    (cutState hm H c).parity =
      ∑ id ∈ (selectedPhysicalIds hm H).filter
        (fun id => (sourceVertex id).2.val ≤ c.val), meridianWeight hm (toEdge hm id) :=
  assignedParity_comap_widthEquiv hm H (cutWidth_eq c)

/-- A direct graph formula: V charges through the cut plus outgoing D charges through the cut. -/
theorem cutState_parity_eq_lastRow {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1)) :
    (cutState hm H c).parity =
      (∑ v ∈ (Finset.univ : Finset (Fin (n + 2))).filter (fun v => v.val ≤ c.val),
        if verticalMask hm H v (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ d ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun d => d.val ≤ c.val),
        if (cutState hm H d).diagonal (lastRow m hm) then (1 : ZMod 2) else 0) := by
  rw [cutState_parity_eq_selected_filter, ← idsOfGeometry_selectedGeometry hm H,
    sum_idsOfGeometry_filter_le_meridian_eq_lastRow]
  simp only [selectedGeometry_vertical, selectedGeometry_diagonal_cutState]
  rfl

end TriangularCylinder.BoundaryParity
