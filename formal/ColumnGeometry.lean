import PhysicalEdges
import Mathlib.Data.Fintype.Powerset

/-!
An exact local-mask encoding of finite selections of physical edge IDs.
Vertical choices have L column positions.  Horizontal and diagonal choices
have L-1 intercolumn positions.  No degree, connectedness, or Hamiltonian
condition is folded into this representation theorem.
-/

namespace TriangularEdgeEncoding

open TriangularCylinder

/-- Independent Boolean masks for V, H and D; row labels remain fixed. -/
abbrev ColumnGeometry (m L : ℕ) :=
  (Fin L → Fin m → Bool) ×
    ((Fin (L - 1) → Fin m → Bool) × (Fin (L - 1) → Fin m → Bool))

def geometryFlag {m L : ℕ} (g : ColumnGeometry m L) : EdgeId m L → Bool
  | Sum.inl (r, c) => g.1 c r
  | Sum.inr (Sum.inl (r, c)) => g.2.1 c r
  | Sum.inr (Sum.inr (r, c)) => g.2.2 c r

def geometryOfIds {m L : ℕ} (S : Finset (EdgeId m L)) : ColumnGeometry m L :=
  (fun c r => decide (Sum.inl (r, c) ∈ S),
    (fun c r => decide (Sum.inr (Sum.inl (r, c)) ∈ S),
     fun c r => decide (Sum.inr (Sum.inr (r, c)) ∈ S)))

def idsOfGeometry {m L : ℕ} (g : ColumnGeometry m L) : Finset (EdgeId m L) :=
  Finset.univ.filter (fun e => geometryFlag g e = true)

theorem geometryFlag_ofIds {m L : ℕ} (S : Finset (EdgeId m L)) (e : EdgeId m L) :
    geometryFlag (geometryOfIds S) e = decide (e ∈ S) := by
  rcases e with ⟨r, c⟩ | (⟨r, c⟩ | ⟨r, c⟩) <;> rfl

theorem mem_idsOfGeometry {m L : ℕ} (g : ColumnGeometry m L) (e : EdgeId m L) :
    e ∈ idsOfGeometry g ↔ geometryFlag g e = true := by
  simp only [idsOfGeometry, Finset.mem_filter, Finset.mem_univ, true_and]

theorem idsOfGeometry_geometryOfIds {m L : ℕ} (S : Finset (EdgeId m L)) :
    idsOfGeometry (geometryOfIds S) = S := by
  ext e
  simp only [mem_idsOfGeometry, geometryFlag_ofIds, decide_eq_true_eq]

theorem geometryOfIds_idsOfGeometry {m L : ℕ} (g : ColumnGeometry m L) :
    geometryOfIds (idsOfGeometry g) = g := by
  apply Prod.ext
  · funext c r
    cases h : g.1 c r <;> simp [geometryOfIds, idsOfGeometry, geometryFlag, h]
  · apply Prod.ext
    · funext c r
      cases h : g.2.1 c r <;> simp [geometryOfIds, idsOfGeometry, geometryFlag, h]
    · funext c r
      cases h : g.2.2 c r <;> simp [geometryOfIds, idsOfGeometry, geometryFlag, h]

/-- Every finite edge-ID selection has one and only one V/H/D mask family. -/
def geometryEquiv (m L : ℕ) : Finset (EdgeId m L) ≃ ColumnGeometry m L where
  toFun := geometryOfIds
  invFun := idsOfGeometry
  left_inv := idsOfGeometry_geometryOfIds
  right_inv := geometryOfIds_idsOfGeometry

theorem geometryOfIds_injective {m L : ℕ} :
    Function.Injective (geometryOfIds (m := m) (L := L)) :=
  (geometryEquiv m L).injective

theorem idsOfGeometry_injective {m L : ℕ} :
    Function.Injective (idsOfGeometry (m := m) (L := L)) :=
  (geometryEquiv m L).symm.injective

/-- Finite selections of actual graph edges, with no degree or connectivity
condition imposed. The data remains an unordered edge finset. -/
abbrev GraphEdgeSelection (m L : ℕ) (hm : 3 ≤ m) :=
  {E : Finset (Sym2 (Vertex m L)) // ∀ e ∈ E, e ∈ (graph m L hm).edgeSet}

/-- Transport physical identifiers to finite selections of graph edges. -/
noncomputable def graphSelectionEquiv {m L : ℕ} (hm : 3 ≤ m) :
    Finset (EdgeId m L) ≃ GraphEdgeSelection m L hm :=
  (edgeEquiv hm).finsetCongr.trans
    (Equiv.finsetSubtypeComm (fun e => e ∈ (graph m L hm).edgeSet))

/-- The equivalence uses exactly the physical endpoint-pair map. -/
theorem graphSelectionEquiv_val {m L : ℕ} (hm : 3 ≤ m)
    (S : Finset (EdgeId m L)) :
    (graphSelectionEquiv hm S).val = S.image (toEdge hm) := by
  change (S.map (edgeEquiv hm).toEmbedding).map
    ⟨Subtype.val, Subtype.val_injective⟩ = S.image (toEdge hm)
  ext e
  simp [Finset.map_map]

/-- The concrete undirected edge set selected by a family of column masks. -/
def realizedEdges {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L) :
    Finset (Sym2 (Vertex m L)) :=
  (idsOfGeometry g).image (toEdge hm)

theorem realizedEdges_mem {m L : ℕ} (hm : 3 ≤ m) (g : ColumnGeometry m L)
    {e : Sym2 (Vertex m L)} (he : e ∈ realizedEdges hm g) :
    e ∈ (graph m L hm).edgeSet := by
  obtain ⟨id, _, rfl⟩ := Finset.mem_image.mp he
  exact toEdge_mem_edgeSet hm id

/-- Exact masks-to-edge-sets bijection for the actual triangular cylinder. -/
noncomputable def columnSelectionEquiv {m L : ℕ} (hm : 3 ≤ m) :
    ColumnGeometry m L ≃ GraphEdgeSelection m L hm :=
  (geometryEquiv m L).symm.trans (graphSelectionEquiv hm)

theorem columnSelectionEquiv_val {m L : ℕ} (hm : 3 ≤ m)
    (g : ColumnGeometry m L) :
    (columnSelectionEquiv hm g).val = realizedEdges hm g :=
  graphSelectionEquiv_val hm (idsOfGeometry g)

/-- Different mask families select different finite undirected edge sets. -/
theorem realizedEdges_injective {m L : ℕ} (hm : 3 ≤ m) :
    Function.Injective (realizedEdges (L := L) hm) := by
  intro g h heq
  apply (columnSelectionEquiv hm).injective
  apply Subtype.ext
  simpa only [columnSelectionEquiv_val] using heq

/-- Every finite selection of graph edges is encoded by a mask family. -/
theorem exists_geometry_of_edges {m L : ℕ} (hm : 3 ≤ m)
    (E : Finset (Sym2 (Vertex m L)))
    (hE : ∀ e ∈ E, e ∈ (graph m L hm).edgeSet) :
    ∃ g : ColumnGeometry m L, realizedEdges hm g = E := by
  obtain ⟨g, hg⟩ := (columnSelectionEquiv hm).surjective ⟨E, hE⟩
  exact ⟨g, (columnSelectionEquiv_val hm g).symm.trans (congrArg Subtype.val hg)⟩

/-- A selected graph-edge finset has exactly one geometric mask encoding. -/
theorem existsUnique_geometry_of_edges {m L : ℕ} (hm : 3 ≤ m)
    (E : Finset (Sym2 (Vertex m L)))
    (hE : ∀ e ∈ E, e ∈ (graph m L hm).edgeSet) :
    ∃! g : ColumnGeometry m L, realizedEdges hm g = E := by
  obtain ⟨g, hg⟩ := exists_geometry_of_edges hm E hE
  exact ⟨g, hg, fun h hh => realizedEdges_injective hm (hh.trans hg.symm)⟩

#print axioms idsOfGeometry_geometryOfIds
#print axioms geometryOfIds_idsOfGeometry
#print axioms geometryOfIds_injective
#print axioms idsOfGeometry_injective
#print axioms graphSelectionEquiv_val
#print axioms columnSelectionEquiv_val
#print axioms realizedEdges_injective
#print axioms existsUnique_geometry_of_edges

end TriangularEdgeEncoding
