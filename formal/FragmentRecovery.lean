import PrefixReplacement

/-!
# Exact recovery of glued column fragments

The prefix owns the edges within the shared boundary column. When the suffix
has no such edges, cutting the canonical transported glue recovers both input
graphs exactly. These graph equalities use only the canonical inclusions;
they require no ambient-validity, connectedness, or degree hypotheses.

For concrete prefix replacement, the encoded reachability field is inherited
from the retained prefix and both outgoing physical masks from the retained
suffix. No parity claim is made here.
-/

namespace CylinderFrontier

variable {I B O : Type*}

/-- The suffix contributes no adjacency between vertices of the prefix when
it owns no edges within the shared boundary. -/
theorem glue_prefix_adj_of_no_boundary_edges
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hQ : ∀ b c, ¬ Q.Adj (Sum.inr b) (Sum.inr c)) (x y : I ⊕ B) :
    (glue P Q).Adj (prefixEmbedding I B O x) (prefixEmbedding I B O y) ↔ P.Adj x y := by
  cases x <;> cases y <;>
    simp [glue, SimpleGraph.map_adj, Sum.exists, prefixEmbedding, suffixEmbedding, hQ]

/-- Restricting to the suffix and discarding boundary-to-boundary edges
recovers exactly the suffix graph. -/
theorem glue_suffix_restricted_adj
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hQ : ∀ b c, ¬ Q.Adj (Sum.inr b) (Sum.inr c)) (x y : O ⊕ B) :
    ((glue P Q).Adj (suffixEmbedding I B O x) (suffixEmbedding I B O y) ∧
      ∃ o : O, x = Sum.inl o ∨ y = Sum.inl o) ↔ Q.Adj x y := by
  cases x <;> cases y <;>
    simp [glue, SimpleGraph.map_adj, Sum.exists, prefixEmbedding, suffixEmbedding, hQ]

end CylinderFrontier

namespace TriangularCylinder.FragmentRecovery

open SimpleGraph ColumnCut ColumnFragments BoundaryState PrefixReplacement

/-- Cutting the transported glue on the prefix side recovers every input
prefix edge and adds none. -/
theorem prefixPart_transportedGlue {m j k : ℕ}
    (P : SimpleGraph (Vertex m j ⊕ Fin m))
    (Q : SimpleGraph (Vertex m k ⊕ Fin m))
    (hQ : ∀ r s, ¬ Q.Adj (Sum.inr r) (Sum.inr s)) :
    prefixPart j k (transportedGlue P Q) = P := by
  ext x y
  change ((CylinderFrontier.glue P Q).map (vertexEquiv m j k).toEmbedding).Adj
    ((vertexEquiv m j k).toEmbedding (CylinderFrontier.prefixEmbedding _ _ _ x))
    ((vertexEquiv m j k).toEmbedding (CylinderFrontier.prefixEmbedding _ _ _ y)) ↔ P.Adj x y
  rw [SimpleGraph.map_adj_apply]
  exact CylinderFrontier.glue_prefix_adj_of_no_boundary_edges P Q hQ x y

/-- Cutting the transported glue on the suffix side recovers every input
suffix edge, with boundary-column edges still owned by the prefix. -/
theorem suffixPart_transportedGlue {m j k : ℕ}
    (P : SimpleGraph (Vertex m j ⊕ Fin m))
    (Q : SimpleGraph (Vertex m k ⊕ Fin m))
    (hQ : ∀ r s, ¬ Q.Adj (Sum.inr r) (Sum.inr s)) :
    suffixPart j k (transportedGlue P Q) = Q := by
  ext x y
  change (((CylinderFrontier.glue P Q).map (vertexEquiv m j k).toEmbedding).Adj
    ((vertexEquiv m j k).toEmbedding (CylinderFrontier.suffixEmbedding _ _ _ x))
    ((vertexEquiv m j k).toEmbedding (CylinderFrontier.suffixEmbedding _ _ _ y)) ∧
      ∃ o : Vertex m k, x = Sum.inl o ∨ y = Sum.inl o) ↔ Q.Adj x y
  rw [SimpleGraph.map_adj_apply]
  exact CylinderFrontier.glue_suffix_restricted_adj P Q hQ x y

/-- In concrete replacement, the new prefix is exactly the chosen old prefix. -/
theorem prefixPart_mixedGraph {m j oldSuffix oldPrefix k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    prefixPart j k (mixedGraph H K) = prefixPart j oldSuffix H :=
  prefixPart_transportedGlue _ _ (suffixPart_no_boundary_edges K)

/-- In concrete replacement, the new suffix is exactly the fixed old suffix. -/
theorem suffixPart_mixedGraph {m j oldSuffix oldPrefix k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    suffixPart j k (mixedGraph H K) = suffixPart oldPrefix k K :=
  suffixPart_transportedGlue _ _ (suffixPart_no_boundary_edges K)

/-- Physical edges from the boundary to the next column belong to the suffix
restriction, with their exact row labels. -/
theorem suffixPart_boundary_next_adj_iff {m j k : ℕ} (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k))) (r s : Fin m) :
    (suffixPart j k H).Adj (Sum.inr r) (Sum.inl (s, ⟨0, by omega⟩)) ↔
      H.Adj (r, boundaryCol j k) (s, nextCol hk) := by
  change (H.Adj (r, boundaryCol j k) (s, nextCol hk) ∧
    ∃ o : Vertex m k, Sum.inr r = Sum.inl o ∨
      Sum.inl (s, (⟨0, by omega⟩ : Fin k)) = Sum.inl o) ↔ _
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, (s, ⟨0, by omega⟩), Or.inr rfl⟩

/-- Equal normalized suffix graphs have equal outgoing horizontal masks,
even when their original prefix lengths differ. -/
theorem stateAt_horizontal_eq_of_suffixPart_eq {m j j' k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k)))
    (K : SimpleGraph (Vertex m (j' + 1 + k)))
    (hQ : suffixPart j k H = suffixPart j' k K) :
    (stateAt hm hk H).horizontal = (stateAt hm hk K).horizontal := by
  funext r
  apply Bool.eq_iff_iff.mpr
  change ((stateAt hm hk H).horizontal r = true ↔
    (stateAt hm hk K).horizontal r = true)
  rw [stateAt_horizontal_iff, stateAt_horizontal_iff,
    ← suffixPart_boundary_next_adj_iff hk H r r,
    ← suffixPart_boundary_next_adj_iff hk K r r, hQ]

/-- Equal normalized suffix graphs have equal outgoing diagonal masks. -/
theorem stateAt_diagonal_eq_of_suffixPart_eq {m j j' k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + k)))
    (K : SimpleGraph (Vertex m (j' + 1 + k)))
    (hQ : suffixPart j k H = suffixPart j' k K) :
    (stateAt hm hk H).diagonal = (stateAt hm hk K).diagonal := by
  funext r
  apply Bool.eq_iff_iff.mpr
  change ((stateAt hm hk H).diagonal r = true ↔
    (stateAt hm hk K).diagonal r = true)
  rw [stateAt_diagonal_iff, stateAt_diagonal_iff,
    ← suffixPart_boundary_next_adj_iff hk H r (TriangularEdgeEncoding.rowSucc hm r),
    ← suffixPart_boundary_next_adj_iff hk K r (TriangularEdgeEncoding.rowSucc hm r), hQ]

/-- The outgoing physical horizontal mask is inherited from the retained suffix. -/
theorem stateAt_mixedGraph_horizontal {m j oldSuffix oldPrefix k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    (stateAt hm hk (mixedGraph H K)).horizontal = (stateAt hm hk K).horizontal :=
  stateAt_horizontal_eq_of_suffixPart_eq hm hk _ _ (suffixPart_mixedGraph H K)

/-- The outgoing physical diagonal mask is inherited from the retained suffix. -/
theorem stateAt_mixedGraph_diagonal {m j oldSuffix oldPrefix k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    (stateAt hm hk (mixedGraph H K)).diagonal = (stateAt hm hk K).diagonal :=
  stateAt_diagonal_eq_of_suffixPart_eq hm hk _ _ (suffixPart_mixedGraph H K)

/-- The boundary reachability relation is inherited from the retained prefix. -/
theorem stateAt_mixedGraph_reach {m j oldSuffix oldPrefix k : ℕ}
    (hm : 3 ≤ m) (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    (stateAt hm hk (mixedGraph H K)).reach = (stateAt hm hOldSuffix H).reach := by
  funext r s
  apply Bool.eq_iff_iff.mpr
  change ((stateAt hm hk (mixedGraph H K)).reach r s = true ↔
    (stateAt hm hOldSuffix H).reach r s = true)
  rw [stateAt_reach_iff, stateAt_reach_iff, prefixPart_mixedGraph]

/-- With matching old physical masks, every non-parity state field after
replacement agrees with the chosen prefix's original state. -/
theorem stateAt_mixedGraph_fields {m j oldSuffix oldPrefix k : ℕ}
    (hm : 3 ≤ m) (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k)))
    (hhor : (stateAt hm hOldSuffix H).horizontal = (stateAt hm hk K).horizontal)
    (hdiag : (stateAt hm hOldSuffix H).diagonal = (stateAt hm hk K).diagonal) :
    (stateAt hm hk (mixedGraph H K)).horizontal = (stateAt hm hOldSuffix H).horizontal ∧
    (stateAt hm hk (mixedGraph H K)).diagonal = (stateAt hm hOldSuffix H).diagonal ∧
    (stateAt hm hk (mixedGraph H K)).reach = (stateAt hm hOldSuffix H).reach :=
  ⟨(stateAt_mixedGraph_horizontal hm hk H K).trans hhor.symm,
    (stateAt_mixedGraph_diagonal hm hk H K).trans hdiag.symm,
    stateAt_mixedGraph_reach hm hOldSuffix hk H K⟩

#print axioms CylinderFrontier.glue_prefix_adj_of_no_boundary_edges
#print axioms CylinderFrontier.glue_suffix_restricted_adj
#print axioms prefixPart_transportedGlue
#print axioms suffixPart_transportedGlue
#print axioms prefixPart_mixedGraph
#print axioms suffixPart_mixedGraph
#print axioms suffixPart_boundary_next_adj_iff
#print axioms stateAt_horizontal_eq_of_suffixPart_eq
#print axioms stateAt_diagonal_eq_of_suffixPart_eq
#print axioms stateAt_mixedGraph_horizontal
#print axioms stateAt_mixedGraph_diagonal
#print axioms stateAt_mixedGraph_reach
#print axioms stateAt_mixedGraph_fields

end TriangularCylinder.FragmentRecovery
