import SelectedEdgePresentation
import TriangularParity

/-!
# Concrete cylinder splicing from selected-edge membership

The input cycles may have arbitrary starting vertices and traversal directions.
Selected boundary edges are rerooted and oriented by the general presentation
bridge, then the checked concrete splice and parity theorems apply.
-/

namespace TriangularCylinder

open SimpleGraph SelectedEdgePresentation

/-- Two actual Hamiltonian cycles selecting aligned boundary gaps can be
spliced without an edge-first presentation hypothesis. The output records
Hamiltonicity, parity addition and the exact selected-edge replacement. -/
theorem exists_splice_of_selected_edges
    {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (r s : Fin m) (hgap : NextRow r s)
    {u : Vertex m a} {v : Vertex m b}
    (A : (graph m a hm).Walk u u) (B : (graph m b hm).Walk v v)
    (hA : A.IsHamiltonianCycle) (hB : B.IsHamiltonianCycle)
    (hleft : s((r, lastCol a ha), (s, lastCol a ha)) ∈ A.edges)
    (hright : s((r, firstCol b hb), (s, firstCol b hb)) ∈ B.edges) :
    ∃ J : (graph m (a + b) hm).Walk
        (leftVertex b (r, lastCol a ha)) (leftVertex b (r, lastCol a ha)),
      J.IsHamiltonianCycle ∧ typeParity hm J = typeParity hm A + typeParity hm B ∧
      J.edgeSet =
        insert s(leftVertex b (r, lastCol a ha), rightVertex a (r, firstCol b hb))
          (insert s(rightVertex a (s, firstCol b hb), leftVertex b (s, lastCol a ha))
            (((A.map (leftHom hm)).edgeSet \
                {s(leftVertex b (r, lastCol a ha), leftVertex b (s, lastCol a ha))}) ∪
              ((B.map (rightHom hm)).edgeSet \
                {s(rightVertex a (s, firstCol b hb), rightVertex a (r, firstCol b hb))}))) := by
  obtain ⟨adjL, p, hp, hpermL⟩ := exists_edge_first A hA hleft
  have hright' : s((s, firstCol b hb), (r, firstCol b hb)) ∈ B.edges := by
    simpa only [Sym2.eq_swap] using hright
  obtain ⟨adjR, q, hq, hpermR⟩ := exists_edge_first B hB hright'
  have hp' : (Walk.cons (vertical_edge hm r s hgap (lastCol a ha)) p).IsHamiltonianCycle := hp
  have hq' : (Walk.cons (vertical_edge hm r s hgap (firstCol b hb)).symm q).IsHamiltonianCycle := hq
  refine ⟨spliceAt hm ha hb r s p q,
    spliceAt_isHamiltonianCycle hm ha hb r s hgap p q hp' hq', ?_, ?_⟩
  · rw [spliceAt_typeParity hm ha hb r s hgap]
    exact congrArg₂ (· + ·)
      (edgeWeight_eq_of_edges_perm (meridianWeight hm) _ _ hpermL)
      (edgeWeight_eq_of_edges_perm (meridianWeight hm) _ _ hpermR)
  · have hmapL : ((Walk.cons (vertical_edge hm r s hgap (lastCol a ha)) p).map
        (leftHom (b := b) hm)).edgeSet = (A.map (leftHom hm)).edgeSet := by
      apply edgeSet_eq_of_edges_perm
      simpa only [Walk.edges_map] using hpermL.map (Sym2.map (leftHom (b := b) hm))
    have hmapR : ((Walk.cons (vertical_edge hm r s hgap (firstCol b hb)).symm q).map
        (rightHom (a := a) hm)).edgeSet = (B.map (rightHom hm)).edgeSet := by
      apply edgeSet_eq_of_edges_perm
      simpa only [Walk.edges_map] using hpermR.map (Sym2.map (rightHom (a := a) hm))
    have hcycleL : ((Walk.cons (vertical_edge hm r s hgap (lastCol a ha)) p).map
        (leftHom (b := b) hm)).IsCycle :=
      hp'.isCycle.map (leftVertex_injective (m := m) (a := a) (b := b))
    have hcycleR : ((Walk.cons (vertical_edge hm r s hgap (firstCol b hb)).symm q).map
        (rightHom (a := a) hm)).IsCycle :=
      hq'.isCycle.map (rightVertex_injective (m := m) (a := a) (b := b))
    have hset := CylinderSplice.splice_edgeSet
      (p.map (leftHom (b := b) hm)) (q.map (rightHom (a := a) hm))
      ((leftHom hm).map_adj (vertical_edge hm r s hgap (lastCol a ha)))
      ((rightHom hm).map_adj (vertical_edge hm r s hgap (firstCol b hb)).symm)
      (horizontal_seam hm ha hb r) (horizontal_seam hm ha hb s).symm
      (by simpa only [Walk.map_cons] using hcycleL)
      (by simpa only [Walk.map_cons] using hcycleR)
    simp only [Walk.map_cons] at hmapL hmapR
    simpa only [hmapL, hmapR] using hset

#print axioms exists_splice_of_selected_edges

end TriangularCylinder
