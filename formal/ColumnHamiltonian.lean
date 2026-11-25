import ColumnGeometry
import SelectedIff

/-!
# Column masks as exact counted Hamiltonian selections

The Hamiltonian condition is imposed on the concrete selected spanning graph,
not on a frontier-state surrogate. The existing column-selection equivalence
and selected-edge characterization then identify admissible mask families with
the counted undirected Hamiltonian edge sets of the actual triangular graph.
Weights are sums on physical edge IDs, and parity is the existing meridian
indicator in ZMod 2. No contractibility or transfer-state interpretation is
asserted here.
-/

namespace TriangularEdgeEncoding

open SimpleGraph TriangularCylinder CountedHamiltonian
open scoped BigOperators

/-- The concrete selected spanning graph is connected and two-regular. -/
def IsHamiltonianGeometry {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L) : Prop :=
  (fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))).Connected ∧
    ∀ v, ((fromEdgeSet (realizedEdges hm g : Set (Sym2 (Vertex m L)))).neighborSet v).ncard = 2

/-- V/H/D mask families satisfying the actual finite-graph Hamiltonian condition. -/
def HamiltonianGeometry (m L : ℕ) (hm : 3 ≤ m) :=
  {g : ColumnGeometry m L // IsHamiltonianGeometry hm g}

noncomputable instance (m L : ℕ) (hm : 3 ≤ m) : Fintype (HamiltonianGeometry m L hm) := by
  classical
  unfold HamiltonianGeometry
  exact Fintype.ofFinite _

/-- The mask predicate is equivalent to a standard Hamiltonian-cycle witness
whose undirected selected edges are exactly the concrete realization. -/
theorem geometry_realization_iff {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L) :
    HasHamiltonianRealization (graph m L hm) (realizedEdges hm g) ↔
      IsHamiltonianGeometry hm g :=
  realization_iff_connected_two (fun _ he => realizedEdges_mem hm g he)

/-- Restrict the exact column-selection equivalence to Hamiltonian selections.
Proof witnesses do not add roots, directions, or other counted data. -/
noncomputable def hamiltonianSelectionEquiv {m L : ℕ} (hm : 3 ≤ m) :
    HamiltonianGeometry m L hm ≃ Selection (graph m L hm) := by
  let e : HamiltonianGeometry m L hm ≃
      {s : GraphEdgeSelection m L hm // HasHamiltonianRealization (graph m L hm) s.val} :=
    Equiv.subtypeEquiv (columnSelectionEquiv hm) (fun g => by
      rw [columnSelectionEquiv_val]
      exact (geometry_realization_iff hm g).symm)
  exact e.trans {
    toFun := fun s => ⟨s.val.val, s.property⟩
    invFun := fun s => ⟨⟨s.val, fun _ he => selection_edge_mem (graph m L hm) s he⟩,
      s.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The forward map selects exactly the concrete physical endpoint pairs. -/
theorem hamiltonianSelectionEquiv_val {m L : ℕ} (hm : 3 ≤ m)
    (g : HamiltonianGeometry m L hm) :
    (hamiltonianSelectionEquiv hm g).val = realizedEdges hm g.val := by
  change (columnSelectionEquiv hm g.val).val = realizedEdges hm g.val
  exact columnSelectionEquiv_val hm g.val

/-- Every column geometry is weighted once per selected physical edge ID. -/
def geometryWeight {m L : ℕ} (hm : 3 ≤ m) {W : Type*} [AddCommMonoid W]
    (w : Sym2 (Vertex m L) → W) (g : ColumnGeometry m L) : W :=
  ∑ id ∈ idsOfGeometry g, w (toEdge hm id)

/-- The counted selection weight equals the physical-ID weight. Injectivity of
the physical edge map ensures that no edge multiplicity is lost in the image. -/
theorem selectionWeight_hamiltonianSelectionEquiv {m L : ℕ} (hm : 3 ≤ m)
    {W : Type*} [AddCommMonoid W] (w : Sym2 (Vertex m L) → W)
    (g : HamiltonianGeometry m L hm) :
    selectionWeight (graph m L hm) w (hamiltonianSelectionEquiv hm g) =
      geometryWeight hm w g.val := by
  rw [selectionWeight, hamiltonianSelectionEquiv_val, realizedEdges, geometryWeight]
  exact Finset.sum_image (fun _ _ _ _ h => toEdge_injective hm h)

/-- Mod-two meridian weight on the selected physical IDs. This is a parity
class; a topological interpretation would require an additional theorem. -/
def geometryParity {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L) : ZMod 2 :=
  geometryWeight hm (meridianWeight hm) g

theorem selectionParity_hamiltonianSelectionEquiv {m L : ℕ} (hm : 3 ≤ m)
    (g : HamiltonianGeometry m L hm) :
    selectionParity hm (hamiltonianSelectionEquiv hm g) = geometryParity hm g.val :=
  selectionWeight_hamiltonianSelectionEquiv hm (meridianWeight hm) g

/-- The exact equivalence restricts to each fixed parity class. -/
noncomputable def parityGeometryEquiv {m L : ℕ} (hm : 3 ≤ m) (t : ZMod 2) :
    {g : HamiltonianGeometry m L hm // geometryParity hm g.val = t} ≃
      {s : Selection (graph m L hm) // selectionParity hm s = t} :=
  Equiv.subtypeEquiv (hamiltonianSelectionEquiv hm) (fun g => by
    rw [selectionParity_hamiltonianSelectionEquiv])

/-- Count Hamiltonian column geometries in one mod-two parity class. -/
noncomputable def geometryParityCount (m L : ℕ) (hm : 3 ≤ m) (t : ZMod 2) : ℕ := by
  classical
  exact ((Finset.univ : Finset (HamiltonianGeometry m L hm)).filter
    (fun g => geometryParity hm g.val = t)).card

/-- Each parity-specific geometry count is exactly the existing finite count
of undirected selected Hamiltonian edge sets. -/
theorem geometryParityCount_eq_parityCount (m L : ℕ) (hm : 3 ≤ m) (t : ZMod 2) :
    geometryParityCount m L hm t = parityCount m L hm t := by
  classical
  simpa only [Fintype.card_subtype, geometryParityCount, parityCount] using
    Fintype.card_congr (parityGeometryEquiv hm t)

end TriangularEdgeEncoding
