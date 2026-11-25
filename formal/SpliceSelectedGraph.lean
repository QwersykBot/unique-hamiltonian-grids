import SelectedCylinderSplice
import SplicePrefixCoordinates
import EdgeReplacementReachability

/-!
# The selected graph of a concrete cylinder splice

The exact selected-edge formula is transported through the disjoint column
bijection and identified with replacement of one old edge by the cut-open
left cycle.  This module supplies graph identities; connectivity is separate.
-/

namespace CylinderFrontier.EdgeReplacement

open SimpleGraph

variable {N V W : Type*}

/-- The selected edge set, on a sum of vertex types, of a two-seam splice. -/
def spliceEdges (EA : Set (Sym2 N)) (EB : Set (Sym2 V))
    (a₀ a₁ : N) (b₀ b₁ : V) : Set (Sym2 (N ⊕ V)) :=
  insert s(Sum.inl a₀, Sum.inr b₀)
    (insert s(Sum.inr b₁, Sum.inl a₁)
      (((Sym2.map Sum.inl '' EA) \ {s(Sum.inl a₀, Sum.inl a₁)}) ∪
        ((Sym2.map Sum.inr '' EB) \ {s(Sum.inr b₁, Sum.inr b₀)})))

private theorem pair_mem_image_map_iff
    (f : N → W) (E : Set (Sym2 N)) (x y : W) :
    s(x, y) ∈ Sym2.map f '' E ↔
      ∃ u v, s(u, v) ∈ E ∧
        ((f u = x ∧ f v = y) ∨ (f u = y ∧ f v = x)) := by
  simp only [Set.mem_image, Sym2.exists, Sym2.map_pair_eq, Sym2.eq_iff]

/-- On the disjoint vertex types, the selected graph is exactly the generic
edge-replacement graph. No regularity or connectivity premise is needed. -/
theorem fromEdgeSet_spliceEdges (EA : Set (Sym2 N)) (EB : Set (Sym2 V))
    (a₀ a₁ : N) (b₀ b₁ : V) :
    fromEdgeSet (spliceEdges EA EB a₀ a₁ b₀ b₁) =
      replacementGraph (fromEdgeSet EB)
        ((fromEdgeSet EA).deleteEdges {s(a₀, a₁)}) b₀ b₁ a₀ a₁ := by
  ext u v
  cases u <;> cases v <;>
    simp only [fromEdgeSet_adj, spliceEdges, replacementGraph, deleteEdges_adj,
      Set.mem_insert_iff, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
      pair_mem_image_map_iff] <;>
    simp [Sym2.eq_iff, Sym2.eq_swap, or_and_right, exists_or,
      and_comm, and_left_comm, and_assoc]

private theorem mem_image_map_equiv (e : N ≃ W) (E : Set (Sym2 N))
    (x y : N) :
    s(e x, e y) ∈ Sym2.map e '' E ↔ s(x, y) ∈ E := by
  rw [← Sym2.map_pair_eq]
  exact (Sym2.map.injective e.injective).mem_set_image

/-- Pulling a selected graph back along the bijection used to map its edges
recovers the original graph, including when the edge set contains diagonals. -/
theorem fromEdgeSet_image_comap (e : N ≃ W) (E : Set (Sym2 N)) :
    (fromEdgeSet (Sym2.map e '' E)).comap e = fromEdgeSet E := by
  ext x y
  simp only [comap_adj, fromEdgeSet_adj, mem_image_map_equiv, e.injective.ne_iff]

/-- The disjoint splice edge formula is compatible with any vertex bijection. -/
theorem image_spliceEdges (e : N ⊕ V ≃ W)
    (EA : Set (Sym2 N)) (EB : Set (Sym2 V)) (a₀ a₁ : N) (b₀ b₁ : V) :
    Sym2.map e '' spliceEdges EA EB a₀ a₁ b₀ b₁ =
      insert s(e (Sum.inl a₀), e (Sum.inr b₀))
        (insert s(e (Sum.inr b₁), e (Sum.inl a₁))
          (((Sym2.map (e ∘ Sum.inl) '' EA) \
              {s(e (Sum.inl a₀), e (Sum.inl a₁))}) ∪
            ((Sym2.map (e ∘ Sum.inr) '' EB) \
              {s(e (Sum.inr b₁), e (Sum.inr b₀))}))) := by
  simp only [spliceEdges, Set.image_insert_eq, Set.image_union,
    Set.image_diff (Sym2.map.injective e.injective), Set.image_singleton,
    Sym2.map_pair_eq, Set.image_image, Sym2.map_map]

#print axioms fromEdgeSet_spliceEdges
#print axioms fromEdgeSet_image_comap
#print axioms image_spliceEdges

end CylinderFrontier.EdgeReplacement

namespace TriangularCylinder.SpliceSelectedGraph

open SimpleGraph SplicePrefixCoordinates CylinderFrontier.EdgeReplacement

/-- The exact edge formula returned by `exists_splice_of_selected_edges`
identifies its selected graph with the connected-gadget replacement model. -/
theorem selected_splice_comap
    {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (r s : Fin m) {u : Vertex m a} {v : Vertex m b} {w : Vertex m (a + b)}
    (A : (graph m a hm).Walk u u) (B : (graph m b hm).Walk v v)
    (J : (graph m (a + b) hm).Walk w w)
    (hset : J.edgeSet =
      insert s(leftVertex b (r, lastCol a ha), rightVertex a (r, firstCol b hb))
        (insert s(rightVertex a (s, firstCol b hb), leftVertex b (s, lastCol a ha))
          (((A.map (leftHom hm)).edgeSet \
              {s(leftVertex b (r, lastCol a ha), leftVertex b (s, lastCol a ha))}) ∪
            ((B.map (rightHom hm)).edgeSet \
              {s(rightVertex a (s, firstCol b hb), rightVertex a (r, firstCol b hb))})))) :
    (fromEdgeSet J.edgeSet).comap (columnSumEquiv m a b) =
      replacementGraph (fromEdgeSet B.edgeSet)
        ((fromEdgeSet A.edgeSet).deleteEdges {s((r, lastCol a ha), (s, lastCol a ha))})
        (r, firstCol b hb) (s, firstCol b hb) (r, lastCol a ha) (s, lastCol a ha) := by
  have hmap : J.edgeSet = Sym2.map (columnSumEquiv m a b) ''
      spliceEdges A.edgeSet B.edgeSet
        (r, lastCol a ha) (s, lastCol a ha) (r, firstCol b hb) (s, firstCol b hb) := by
    rw [hset, image_spliceEdges]
    simp only [columnSumEquiv_left, columnSumEquiv_right, Walk.edgeSet_map]
    rfl
  rw [hmap, fromEdgeSet_image_comap, fromEdgeSet_spliceEdges]

#print axioms selected_splice_comap

end TriangularCylinder.SpliceSelectedGraph
