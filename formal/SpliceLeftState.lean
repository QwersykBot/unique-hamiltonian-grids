import SpliceSelectedGraph
import BoundaryParity

/-!
# Preservation of every old left state under a right cylinder splice

Every edge with left source column at most the old cut is unchanged: the
deleted left vertical edge and both seams begin in the last left column,
strictly after that cut. Exact prefix equality therefore preserves reach,
and the frozen selected-ID V/D charging formula preserves assigned parity.
The generic graph theorem uses no connectivity or Hamiltonicity premise.
-/

namespace TriangularCylinder.SpliceLeftState

open SimpleGraph ColumnCut BoundaryState Transfer BoundaryParity
open TriangularEdgeEncoding SplicePrefixCoordinates CylinderFrontier.EdgeReplacement
open scoped BigOperators

def leftWidthEquiv (m j k b : ℕ) :
    Vertex m (j + 1 + (k + b)) ≃ Vertex m ((j + 1 + k) + b) :=
  widthEquiv (by omega)

def joinedLeftGraph {m j k b : ℕ}
    (J : SimpleGraph (Vertex m ((j + 1 + k) + b))) :
    SimpleGraph (Vertex m (j + 1 + (k + b))) :=
  J.comap (leftWidthEquiv m j k b)

theorem leftWidth_prefixVertex {m j k b : ℕ} (x : Vertex m j ⊕ Fin m) :
    leftWidthEquiv m j k b (prefixVertex j (k + b) x) =
      leftVertex b (prefixVertex j k x) := by
  cases x <;> rfl

theorem leftWidth_boundaryCol {m j k b : ℕ} (r : Fin m) :
    leftWidthEquiv m j k b (r, boundaryCol j (k + b)) =
      leftVertex b (r, boundaryCol j k) := rfl

theorem leftWidth_nextCol {m j k b : ℕ} (hk : 1 ≤ k) (r : Fin m) :
    leftWidthEquiv m j k b (r, nextCol (j := j) (k := k + b) (by omega)) =
      leftVertex b (r, nextCol (j := j) hk) := rfl

theorem leftWidth_column {m j k b : ℕ} (r : Fin m) (c : Fin (j + 1 + k)) :
    leftWidthEquiv m j k b (r, Fin.castLE (by omega) c) = leftVertex b (r, c) := rfl

theorem leftWidth_lowerCol {m j k b : ℕ} (r : Fin m) (c : Fin (j + 1 + k - 1)) :
    leftWidthEquiv m j k b
      (r, lowerCol (L := j + 1 + (k + b)) (Fin.castLE (by omega) c)) =
      leftVertex b (r, lowerCol (L := j + 1 + k) c) := rfl

theorem leftWidth_upperCol {m j k b : ℕ} (r : Fin m) (c : Fin (j + 1 + k - 1)) :
    leftWidthEquiv m j k b
      (r, upperCol (L := j + 1 + (k + b)) (Fin.castLE (by omega) c)) =
      leftVertex b (r, upperCol (L := j + 1 + k) c) := rfl

theorem prefixVertex_col_le {m j k : ℕ} (x : Vertex m j ⊕ Fin m) :
    (prefixVertex j k x).2.val ≤ j := by
  cases x with
  | inl x =>
      change x.2.val ≤ j
      exact Nat.le_of_lt x.2.isLt
  | inr r => exact Nat.le_refl j

/-- Reindex a finite through-cut sum by the unchanged numeric column labels. -/
theorem sum_prefix_castLE {W : Type*} [AddCommMonoid W] {L L' j : ℕ}
    (hL : L ≤ L') (hj : j < L) (f : Fin L → W) (g : Fin L' → W)
    (hfg : ∀ c, c.val ≤ j → f c = g (Fin.castLE hL c)) :
    (∑ c ∈ (Finset.univ : Finset (Fin L)).filter (fun c => c.val ≤ j), f c) =
      ∑ c ∈ (Finset.univ : Finset (Fin L')).filter (fun c => c.val ≤ j), g c := by
  apply Finset.sum_bij (fun c _ => Fin.castLE hL c)
  · intro c hc
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.coe_castLE] using hc
  · intro c hc d hd h
    exact Fin.ext (congrArg (fun x : Fin L' => x.val) h)
  · intro c hc
    have hcut : c.val ≤ j := (Finset.mem_filter.mp hc).2
    let d : Fin L := ⟨c.val, lt_of_le_of_lt hcut hj⟩
    refine ⟨d, ?_, Fin.ext rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcut
  · intro c hc
    exact hfg c (Finset.mem_filter.mp hc).2

/-- This is the frozen assigned-ID parity, written using its existing through-cut
V/D charging identity. It introduces no alternate state parity. -/
theorem stateAt_parity_geometry {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) :
    (stateAt hm hk H).parity =
      (∑ c ∈ (Finset.univ : Finset (Fin (j + 1 + k))).filter (fun c => c.val ≤ j),
        if (selectedGeometry hm H).1 c (lastRow m hm) then (1 : ZMod 2) else 0) +
      (∑ c ∈ (Finset.univ : Finset (Fin (j + 1 + k - 1))).filter (fun c => c.val ≤ j),
        if (selectedGeometry hm H).2.2 c (lastRow m hm) then (1 : ZMod 2) else 0) := by
  change assignedParity hm H = _
  unfold assignedParity
  rw [assignedIds_eq_filter, ← idsOfGeometry_selectedGeometry hm H]
  exact sum_idsOfGeometry_filter_le_meridian_eq_lastRow hm _ j

theorem selectedGeometry_diagonal_iff {m L : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m L)) (c : Fin (L - 1)) (r : Fin m) :
    (selectedGeometry hm H).2.2 c r = true ↔
      H.Adj (r, lowerCol c) (rowSucc hm r, upperCol c) := by
  simp only [selectedGeometry, geometryOfIds, decide_eq_true_eq, mem_selectedPhysicalIds,
    toEdge, sourceVertex, targetVertex, SimpleGraph.mem_edgeSet]

section ExactSplice

variable {m j k b : ℕ} (hk : 1 ≤ k) (hb : 2 ≤ b)
variable (A : SimpleGraph (Vertex m (j + 1 + k))) (B : SimpleGraph (Vertex m b))
variable (J : SimpleGraph (Vertex m ((j + 1 + k) + b))) (r s : Fin m)
variable (hsplice : J.comap (columnSumEquiv m (j + 1 + k) b) =
  replacementGraph B
    (A.deleteEdges {s((r, lastCol (j + 1 + k) (by omega)), (s, lastCol (j + 1 + k) (by omega)))})
    (r, firstCol b hb) (s, firstCol b hb)
    (r, lastCol (j + 1 + k) (by omega)) (s, lastCol (j + 1 + k) (by omega)))

include hsplice

/-- Inside the old left block, the exact splice graph deletes only its chosen V edge. -/
theorem left_adj_iff (x y : Vertex m (j + 1 + k)) :
    J.Adj (leftVertex b x) (leftVertex b y) ↔
      (A.deleteEdges {s((r, lastCol (j + 1 + k) (by omega)),
        (s, lastCol (j + 1 + k) (by omega)))}).Adj x y := by
  change (J.comap (columnSumEquiv m (j + 1 + k) b)).Adj (Sum.inl x) (Sum.inl y) ↔ _
  rw [hsplice]
  rfl

/-- Any old left adjacency with a source at or before the cut is unchanged. -/
theorem left_adj_iff_of_col_le (x y : Vertex m (j + 1 + k)) (hx : x.2.val ≤ j) :
    J.Adj (leftVertex b x) (leftVertex b y) ↔ A.Adj x y := by
  have hne (t : Fin m) : x ≠ (t, lastCol (j + 1 + k) (by omega)) := by
    intro h
    have hc := congrArg (fun z : Vertex m (j + 1 + k) => z.2.val) h
    change x.2.val = j + 1 + k - 1 at hc
    omega
  rw [left_adj_iff hk hb A B J r s hsplice]
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rintro (⟨hx, _⟩ | ⟨hx, _⟩)
    · exact hne r hx
    · exact hne s hx

/-- The entire old processed prefix graph is unchanged. No connectivity premise is used. -/
theorem prefixPart_eq : prefixPart j (k + b) (joinedLeftGraph J) = prefixPart j k A := by
  ext x y
  change J.Adj (leftWidthEquiv m j k b (prefixVertex j (k + b) x))
    (leftWidthEquiv m j k b (prefixVertex j (k + b) y)) ↔
      A.Adj (prefixVertex j k x) (prefixVertex j k y)
  rw [leftWidth_prefixVertex, leftWidth_prefixVertex]
  exact left_adj_iff_of_col_le hk hb A B J r s hsplice _ _ (prefixVertex_col_le x)

theorem stateAt_horizontal_eq (hm : 3 ≤ m) :
    (stateAt hm (by omega) (joinedLeftGraph J)).horizontal = (stateAt hm hk A).horizontal := by
  funext t
  rw [Bool.eq_iff_iff, stateAt_horizontal_iff, stateAt_horizontal_iff]
  change J.Adj (leftWidthEquiv m j k b (t, boundaryCol j (k + b)))
    (leftWidthEquiv m j k b (t, nextCol (by omega))) ↔ _
  rw [leftWidth_boundaryCol, leftWidth_nextCol hk]
  exact left_adj_iff_of_col_le hk hb A B J r s hsplice _ _ (Nat.le_refl j)

theorem stateAt_diagonal_eq (hm : 3 ≤ m) :
    (stateAt hm (by omega) (joinedLeftGraph J)).diagonal = (stateAt hm hk A).diagonal := by
  funext t
  rw [Bool.eq_iff_iff, stateAt_diagonal_iff, stateAt_diagonal_iff]
  change J.Adj (leftWidthEquiv m j k b (t, boundaryCol j (k + b)))
    (leftWidthEquiv m j k b (rowSucc hm t, nextCol (by omega))) ↔ _
  rw [leftWidth_boundaryCol, leftWidth_nextCol hk]
  exact left_adj_iff_of_col_le hk hb A B J r s hsplice _ _ (Nat.le_refl j)

theorem stateAt_reach_eq (hm : 3 ≤ m) :
    (stateAt hm (by omega) (joinedLeftGraph J)).reach = (stateAt hm hk A).reach := by
  funext t u
  rw [Bool.eq_iff_iff, stateAt_reach_iff, stateAt_reach_iff,
    prefixPart_eq hk hb A B J r s hsplice]

/-- Every charged V bit through the old cut is unchanged at its physical column. -/
theorem selectedGeometry_vertical_eq (hm : 3 ≤ m) (c : Fin (j + 1 + k))
    (hc : c.val ≤ j) (t : Fin m) :
    (selectedGeometry hm (joinedLeftGraph J)).1 (Fin.castLE (by omega) c) t =
      (selectedGeometry hm A).1 c t := by
  rw [selectedGeometry_vertical, selectedGeometry_vertical, Bool.eq_iff_iff,
    verticalMask_iff, verticalMask_iff]
  change J.Adj (leftWidthEquiv m j k b (t, Fin.castLE (by omega) c))
    (leftWidthEquiv m j k b (rowSucc hm t, Fin.castLE (by omega) c)) ↔ _
  rw [leftWidth_column, leftWidth_column]
  exact left_adj_iff_of_col_le hk hb A B J r s hsplice _ _ hc

/-- Every charged outgoing D bit through the old cut is unchanged. -/
theorem selectedGeometry_diagonal_eq (hm : 3 ≤ m) (c : Fin (j + 1 + k - 1))
    (hc : c.val ≤ j) (t : Fin m) :
    (selectedGeometry hm (joinedLeftGraph J)).2.2 (Fin.castLE (by omega) c) t =
      (selectedGeometry hm A).2.2 c t := by
  rw [Bool.eq_iff_iff, selectedGeometry_diagonal_iff, selectedGeometry_diagonal_iff]
  change J.Adj (leftWidthEquiv m j k b (t, lowerCol (Fin.castLE (by omega) c)))
    (leftWidthEquiv m j k b (rowSucc hm t, upperCol (Fin.castLE (by omega) c))) ↔ _
  rw [leftWidth_lowerCol, leftWidth_upperCol]
  exact left_adj_iff_of_col_le hk hb A B J r s hsplice _ _ hc

/-- The existing assigned parity is unchanged: all its through-cut V/D charges
are the old ones, before the deleted edge or either seam source. -/
theorem stateAt_parity_eq (hm : 3 ≤ m) :
    (stateAt hm (by omega) (joinedLeftGraph J)).parity = (stateAt hm hk A).parity := by
  rw [stateAt_parity_geometry, stateAt_parity_geometry]
  apply congrArg₂ (· + ·)
  · symm
    apply sum_prefix_castLE (by omega : j + 1 + k ≤ j + 1 + (k + b)) (by omega)
    intro c hc
    rw [selectedGeometry_vertical_eq hk hb A B J r s hsplice hm c hc]
  · symm
    apply sum_prefix_castLE (by omega : j + 1 + k - 1 ≤ j + 1 + (k + b) - 1) (by omega)
    intro c hc
    rw [selectedGeometry_diagonal_eq hk hb A B J r s hsplice hm c hc]

/-- The full old left raw state survives the exact concrete splice. -/
theorem stateAt_eq_of_graph_identity (hm : 3 ≤ m) :
    stateAt hm (by omega) (joinedLeftGraph J) = stateAt hm hk A :=
  RawBoundaryState.ext (stateAt_horizontal_eq hk hb A B J r s hsplice hm)
    (stateAt_diagonal_eq hk hb A B J r s hsplice hm)
    (stateAt_reach_eq hk hb A B J r s hsplice hm)
    (stateAt_parity_eq hk hb A B J r s hsplice hm)

end ExactSplice

/-- The actual selected-edge splice has a standard Hamiltonian output preserving
the full old left state. Its exact graph identity is retained for other splice lemmas. -/
theorem exists_splice_preserving_left_state
    {m j k b : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (hb : 2 ≤ b)
    (r s : Fin m) (hgap : NextRow r s)
    {u : Vertex m (j + 1 + k)} {v : Vertex m b}
    (A : (graph m (j + 1 + k) hm).Walk u u) (B : (graph m b hm).Walk v v)
    (hA : A.IsHamiltonianCycle) (hB : B.IsHamiltonianCycle)
    (hleft : s((r, lastCol (j + 1 + k) (by omega)),
      (s, lastCol (j + 1 + k) (by omega))) ∈ A.edges)
    (hright : s((r, firstCol b hb), (s, firstCol b hb)) ∈ B.edges) :
    ∃ J : (graph m ((j + 1 + k) + b) hm).Walk
      (leftVertex b (r, lastCol (j + 1 + k) (by omega)))
      (leftVertex b (r, lastCol (j + 1 + k) (by omega))),
      J.IsHamiltonianCycle ∧ typeParity hm J = typeParity hm A + typeParity hm B ∧
      (fromEdgeSet J.edgeSet).comap (columnSumEquiv m (j + 1 + k) b) =
        replacementGraph (fromEdgeSet B.edgeSet)
          ((fromEdgeSet A.edgeSet).deleteEdges
            {s((r, lastCol (j + 1 + k) (by omega)), (s, lastCol (j + 1 + k) (by omega)))})
          (r, firstCol b hb) (s, firstCol b hb)
          (r, lastCol (j + 1 + k) (by omega)) (s, lastCol (j + 1 + k) (by omega)) ∧
      stateAt hm (by omega) (joinedLeftGraph (fromEdgeSet J.edgeSet)) =
        stateAt hm hk (fromEdgeSet A.edgeSet) := by
  obtain ⟨J, hJ, hp, hset⟩ := exists_splice_of_selected_edges hm (by omega) hb
    r s hgap A B hA hB hleft hright
  have hsplice := SpliceSelectedGraph.selected_splice_comap hm (by omega) hb r s A B J hset
  exact ⟨J, hJ, hp, hsplice,
    stateAt_eq_of_graph_identity hk hb _ _ _ r s hsplice hm⟩

#print axioms leftWidth_prefixVertex
#print axioms leftWidth_boundaryCol
#print axioms leftWidth_nextCol
#print axioms leftWidth_column
#print axioms leftWidth_lowerCol
#print axioms leftWidth_upperCol
#print axioms prefixVertex_col_le
#print axioms sum_prefix_castLE
#print axioms stateAt_parity_geometry
#print axioms selectedGeometry_diagonal_iff
#print axioms left_adj_iff
#print axioms left_adj_iff_of_col_le
#print axioms prefixPart_eq
#print axioms stateAt_horizontal_eq
#print axioms stateAt_diagonal_eq
#print axioms stateAt_reach_eq
#print axioms selectedGeometry_vertical_eq
#print axioms selectedGeometry_diagonal_eq
#print axioms stateAt_parity_eq
#print axioms stateAt_eq_of_graph_identity
#print axioms exists_splice_preserving_left_state

end TriangularCylinder.SpliceLeftState
