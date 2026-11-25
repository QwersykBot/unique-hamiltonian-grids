import SpliceSelectedGraph
import ReplacementRestriction
import SelectedCycleDeletion

/-!
# Old-prefix reachability after an actual cylinder splice

The prefix contains the entire inserted left cylinder and the complete old
prefix, including its boundary column.  After removing the chosen left edge,
the left cycle is a connected gadget replacing the chosen old first-column
edge. The exact selected graph of the concrete splice therefore preserves
reachability among every pair of old prefix vertices.
-/

namespace TriangularCylinder.SplicePrefixReachability

open SimpleGraph SplicePrefixCoordinates CylinderFrontier.EdgeReplacement

/-- The canonical joined prefix, with the full width reassociated explicitly. -/
def joinedPrefix {m a j k : ℕ}
    (G : SimpleGraph (Vertex m (a + (j + 1 + k)))) :
    SimpleGraph (TargetPrefix m a j) :=
  ColumnCut.prefixPart (a + j) k (G.comap (fullWidthEquiv m a j k))

theorem joinedPrefix_comap_eq_physical {m a j k : ℕ}
    (G : SimpleGraph (Vertex m (a + (j + 1 + k)))) :
    (joinedPrefix G).comap (prefixEquiv m a j) =
      G.comap (physicalPrefix a j k) := by
  ext x y
  simp only [joinedPrefix, ColumnCut.prefixPart, comap_adj,
    fullWidth_prefixVertex_eq_physicalPrefix]

theorem physicalPrefix_comap_eq {m a j k : ℕ}
    (G : SimpleGraph (Vertex m (a + (j + 1 + k)))) :
    G.comap (physicalPrefix a j k) =
      (G.comap (columnSumEquiv m a (j + 1 + k))).comap
        (Sum.map id (ColumnCut.prefixVertex j k)) := by
  ext x y
  cases x <;> cases y <;> rfl

/-- A replacement of the first old-column edge by a connected left graph
preserves reachability between all old-prefix vertices, including at `j = 0`. -/
theorem old_prefix_reachable_iff_of_comap
    {m a j k : ℕ} (hb : 2 ≤ j + 1 + k)
    (GA : SimpleGraph (Vertex m a)) (GB : SimpleGraph (Vertex m (j + 1 + k)))
    (GJ : SimpleGraph (Vertex m (a + (j + 1 + k))))
    (a₀ a₁ : Vertex m a) (r s : Fin m)
    (hA : GA.Connected)
    (hxy : GB.Adj (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb))
    (hsplice : GJ.comap (columnSumEquiv m a (j + 1 + k)) =
      replacementGraph GB GA
        (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb) a₀ a₁)
    (x y : Vertex m j ⊕ Fin m) :
    (joinedPrefix GJ).Reachable (prefixEquiv m a j (Sum.inr x))
        (prefixEquiv m a j (Sum.inr y)) ↔
      (ColumnCut.prefixPart j k GB).Reachable x y := by
  have hf : Function.Injective (ColumnCut.prefixVertex (m := m) j k) :=
    (ColumnCut.vertexEquiv m j k).injective.comp
      (CylinderFrontier.prefixEmbedding (Vertex m j) (Fin m) (Vertex m k)).injective
  have hrestricted : (joinedPrefix GJ).comap (prefixEquiv m a j) =
      replacementGraph (ColumnCut.prefixPart j k GB) GA
        (firstPrefixVertex j r) (firstPrefixVertex j s) a₀ a₁ := by
    rw [joinedPrefix_comap_eq_physical, physicalPrefix_comap_eq, hsplice,
      ← prefixVertex_firstPrefixVertex hb r, ← prefixVertex_firstPrefixVertex hb s,
      comap_replacementGraph GB GA (ColumnCut.prefixVertex j k) hf]
    rfl
  have hxy' : (ColumnCut.prefixPart j k GB).Adj
      (firstPrefixVertex j r) (firstPrefixVertex j s) := by
    change GB.Adj (ColumnCut.prefixVertex j k (firstPrefixVertex j r))
      (ColumnCut.prefixVertex j k (firstPrefixVertex j s))
    simpa only [prefixVertex_firstPrefixVertex hb] using hxy
  calc
    _ ↔ ((joinedPrefix GJ).comap (prefixEquiv m a j)).Reachable
        (Sum.inr x) (Sum.inr y) :=
      Iso.reachable_iff (φ := Iso.comap (prefixEquiv m a j) (joinedPrefix GJ))
    _ ↔ _ := by
      rw [hrestricted]
      exact old_reachable_iff (ColumnCut.prefixPart j k GB) GA hxy' hA a₀ a₁ x y

/-- The actual selected-edge splice can be chosen with its Hamiltonicity,
parity sum and exact edge formula, and it preserves all old-prefix reachability.
The right prefix interior may be empty; no positive-cut assumption is imposed. -/
theorem exists_splice_preserving_old_prefix_reachability
    {m a j k : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ j + 1 + k)
    (r s : Fin m) (hgap : NextRow r s)
    {u : Vertex m a} {v : Vertex m (j + 1 + k)}
    (A : (graph m a hm).Walk u u)
    (B : (graph m (j + 1 + k) hm).Walk v v)
    (hA : A.IsHamiltonianCycle) (hB : B.IsHamiltonianCycle)
    (hleft : s((r, lastCol a ha), (s, lastCol a ha)) ∈ A.edges)
    (hright : s((r, firstCol (j + 1 + k) hb),
      (s, firstCol (j + 1 + k) hb)) ∈ B.edges) :
    ∃ J : (graph m (a + (j + 1 + k)) hm).Walk
        (leftVertex (j + 1 + k) (r, lastCol a ha))
        (leftVertex (j + 1 + k) (r, lastCol a ha)),
      J.IsHamiltonianCycle ∧ typeParity hm J = typeParity hm A + typeParity hm B ∧
      J.edgeSet =
        insert s(leftVertex (j + 1 + k) (r, lastCol a ha),
          rightVertex a (r, firstCol (j + 1 + k) hb))
          (insert s(rightVertex a (s, firstCol (j + 1 + k) hb),
            leftVertex (j + 1 + k) (s, lastCol a ha))
            (((A.map (leftHom hm)).edgeSet \
                {s(leftVertex (j + 1 + k) (r, lastCol a ha),
                  leftVertex (j + 1 + k) (s, lastCol a ha))}) ∪
              ((B.map (rightHom hm)).edgeSet \
                {s(rightVertex a (s, firstCol (j + 1 + k) hb),
                  rightVertex a (r, firstCol (j + 1 + k) hb))}))) ∧
      ∀ x y : Vertex m j ⊕ Fin m,
        (joinedPrefix (fromEdgeSet J.edgeSet)).Reachable
            (prefixEquiv m a j (Sum.inr x)) (prefixEquiv m a j (Sum.inr y)) ↔
          (ColumnCut.prefixPart j k (fromEdgeSet B.edgeSet)).Reachable x y := by
  classical
  obtain ⟨J, hJ, hparity, hset⟩ :=
    exists_splice_of_selected_edges hm ha hb r s hgap A B hA hB hleft hright
  refine ⟨J, hJ, hparity, hset, ?_⟩
  intro x y
  apply old_prefix_reachable_iff_of_comap hb
    ((fromEdgeSet A.edgeSet).deleteEdges {s((r, lastCol a ha), (s, lastCol a ha))})
    (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet)
    (r, lastCol a ha) (s, lastCol a ha) r s
    (CylinderFrontier.selected_cycle_delete_edge_connected A hA hleft) _
    (SpliceSelectedGraph.selected_splice_comap hm ha hb r s A B J hset) x y
  exact (fromEdgeSet_adj B.edgeSet).mpr
    ⟨hright, (vertical_edge hm r s hgap (firstCol (j + 1 + k) hb)).ne⟩

#print axioms joinedPrefix_comap_eq_physical
#print axioms physicalPrefix_comap_eq
#print axioms old_prefix_reachable_iff_of_comap
#print axioms exists_splice_preserving_old_prefix_reachability

end TriangularCylinder.SplicePrefixReachability
