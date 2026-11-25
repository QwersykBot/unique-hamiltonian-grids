import ActualTransfer
import ColumnCutOutgoing
import FrontierCongruence

/-!
# The connectivity update after one physical column

Within one column, the physical vertical mask determines every selected
adjacency. Between a processed boundary and one new column, the previous
horizontal/diagonal masks and the new vertical mask determine the entire
suffix fragment. Equal attached prefix relations therefore give equal
reachability between the new boundary rows. Prefixes may be disconnected.
-/

namespace TriangularCylinder.ColumnStep

open SimpleGraph TriangularEdgeEncoding BoundaryState ColumnCut Transfer

/-- Actual same-column adjacency is determined by the two possible oriented
vertical identifiers. No horizontal or diagonal can stay in that column. -/
theorem sameColumn_adj_iff {m L : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m L)} (hH : H ≤ graph m L hm)
    (c : Fin L) (r s : Fin m) :
    H.Adj (r, c) (s, c) ↔
      (s = rowSucc hm r ∧ verticalMask hm H c r = true) ∨
      (r = rowSucc hm s ∧ verticalMask hm H c s = true) := by
  constructor
  · intro hrs
    rcases hH hrs with hf | hb
    · rcases hf with ⟨_, hrow⟩ | ⟨_, hcol⟩ | ⟨_, hcol⟩
      · have hs : s = rowSucc hm r := Fin.ext hrow
        subst s
        exact Or.inl ⟨rfl, (verticalMask_iff hm H c r).mpr hrs⟩
      · change c.val + 1 = c.val at hcol
        omega
      · change c.val + 1 = c.val at hcol
        omega
    · rcases hb with ⟨_, hrow⟩ | ⟨_, hcol⟩ | ⟨_, hcol⟩
      · have hr : r = rowSucc hm s := Fin.ext hrow
        subst r
        exact Or.inr ⟨rfl, (verticalMask_iff hm H c s).mpr hrs.symm⟩
      · change c.val + 1 = c.val at hcol
        omega
      · change c.val + 1 = c.val at hcol
        omega
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hv⟩)
    · exact (verticalMask_iff hm H c r).mp hv
    · exact ((verticalMask_iff hm H c s).mp hv).symm

/-- The same vertical mask gives the same within-column graph at any two lengths. -/
theorem sameColumn_adj_iff_of_masks_eq {m L L' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m L)} {K : SimpleGraph (Vertex m L')}
    (hH : H ≤ graph m L hm) (hK : K ≤ graph m L' hm)
    (c : Fin L) (d : Fin L')
    (hV : verticalMask hm H c = verticalMask hm K d) (r s : Fin m) :
    H.Adj (r, c) (s, c) ↔ K.Adj (r, d) (s, d) := by
  rw [sameColumn_adj_iff hm hH, sameColumn_adj_iff hm hK, hV]

/-- In particular, the first processed prefix is determined by its vertical mask. -/
theorem firstPrefix_eq_of_verticalMask_eq {m k k' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (0 + 1 + k))}
    {K : SimpleGraph (Vertex m (0 + 1 + k'))}
    (hH : H ≤ graph m (0 + 1 + k) hm) (hK : K ≤ graph m (0 + 1 + k') hm)
    (hV : verticalMask hm H (boundaryCol 0 k) = verticalMask hm K (boundaryCol 0 k')) :
    prefixPart 0 k H = prefixPart 0 k' K := by
  ext x y
  cases x with
  | inl x => exact Fin.elim0 x.2
  | inr r =>
      cases y with
      | inl y => exact Fin.elim0 y.2
      | inr s =>
          change H.Adj (r, boundaryCol 0 k) (s, boundaryCol 0 k) ↔
            K.Adj (r, boundaryCol 0 k') (s, boundaryCol 0 k')
          exact sameColumn_adj_iff_of_masks_eq hm hH hK _ _ hV r s

/-- The first-cut relation is a function of the actual first-column vertical mask. -/
theorem firstState_reach_eq_of_verticalMask_eq {m k k' : ℕ} (hm : 3 ≤ m)
    (hk : 1 ≤ k) (hk' : 1 ≤ k')
    {H : SimpleGraph (Vertex m (0 + 1 + k))}
    {K : SimpleGraph (Vertex m (0 + 1 + k'))}
    (hH : H ≤ graph m (0 + 1 + k) hm) (hK : K ≤ graph m (0 + 1 + k') hm)
    (hV : verticalMask hm H (boundaryCol 0 k) = verticalMask hm K (boundaryCol 0 k')) :
    (stateAt hm hk H).reach = (stateAt hm hk' K).reach := by
  have hp := firstPrefix_eq_of_verticalMask_eq hm hH hK hV
  funext r s
  rw [Bool.eq_iff_iff, stateAt_reach_iff, stateAt_reach_iff, hp]

/-- Interior adjacency in the one-column suffix is its selected physical adjacency. -/
theorem oneColumn_suffix_interior_adj {m j : ℕ}
    (H : SimpleGraph (Vertex m (j + 2))) (x y : Vertex m 1) :
    (suffixPart j 1 H).Adj (Sum.inl x) (Sum.inl y) ↔
      H.Adj (suffixVertex j 1 (Sum.inl x)) (suffixVertex j 1 (Sum.inl y)) :=
  ⟨And.left, fun h => ⟨h, x, Or.inl rfl⟩⟩

/-- Old outgoing H/D masks and the new V mask determine the full one-column suffix. -/
theorem oneColumn_suffix_eq_of_masks_eq {m j j' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 2))} {K : SimpleGraph (Vertex m (j' + 2))}
    (hH : H ≤ graph m (j + 2) hm) (hK : K ≤ graph m (j' + 2) hm)
    (hHor : (stateAt (j := j) (k := 1) hm (by decide) H).horizontal =
      (stateAt (j := j') (k := 1) hm (by decide) K).horizontal)
    (hDiag : (stateAt (j := j) (k := 1) hm (by decide) H).diagonal =
      (stateAt (j := j') (k := 1) hm (by decide) K).diagonal)
    (hV : verticalMask hm H (nextCol (j := j) (k := 1) (by decide)) =
      verticalMask hm K (nextCol (j := j') (k := 1) (by decide))) :
    suffixPart j 1 H = suffixPart j' 1 K := by
  have hboundary (r : Fin m) (x : Vertex m 1 ⊕ Fin m) :
      (suffixPart j 1 H).Adj (Sum.inr r) x ↔
        (suffixPart j' 1 K).Adj (Sum.inr r) x := by
    rw [suffixPart_boundary_adj_iff_masks hm (by decide) hH,
      suffixPart_boundary_adj_iff_masks hm (by decide) hK, hHor, hDiag]
  ext x y
  cases x with
  | inr r => exact hboundary r y
  | inl x =>
      cases y with
      | inr s =>
          exact ⟨fun h => ((hboundary s (Sum.inl x)).mp h.symm).symm,
            fun h => ((hboundary s (Sum.inl x)).mpr h.symm).symm⟩
      | inl y =>
          rw [oneColumn_suffix_interior_adj, oneColumn_suffix_interior_adj]
          obtain ⟨r, c⟩ := x
          obtain ⟨s, d⟩ := y
          have hc : c = (0 : Fin 1) := Subsingleton.elim _ _
          have hd : d = (0 : Fin 1) := Subsingleton.elim _ _
          subst c
          subst d
          exact sameColumn_adj_iff_of_masks_eq hm hH hK _ _ hV r s

/-- Reachability between new boundary rows depends on the old prefix relation
and the physical masks of this one-column extension. The prefixes need only
attach to their boundary; neither full enlarged prefix is assumed connected. -/
theorem nextColumn_reachable_iff {m j j' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 2))} {K : SimpleGraph (Vertex m (j' + 2))}
    (hH : H ≤ graph m (j + 2) hm) (hK : K ≤ graph m (j' + 2) hm)
    (hAttachH : CylinderFrontier.TouchesBoundary (prefixPart j 1 H))
    (hAttachK : CylinderFrontier.TouchesBoundary (prefixPart j' 1 K))
    (hHor : (stateAt (j := j) (k := 1) hm (by decide) H).horizontal =
      (stateAt (j := j') (k := 1) hm (by decide) K).horizontal)
    (hDiag : (stateAt (j := j) (k := 1) hm (by decide) H).diagonal =
      (stateAt (j := j') (k := 1) hm (by decide) K).diagonal)
    (hReach : (stateAt (j := j) (k := 1) hm (by decide) H).reach =
      (stateAt (j := j') (k := 1) hm (by decide) K).reach)
    (hV : verticalMask hm H (nextCol (j := j) (k := 1) (by decide)) =
      verticalMask hm K (nextCol (j := j') (k := 1) (by decide))) (r s : Fin m) :
    H.Reachable (r, nextCol (j := j) (k := 1) (by decide))
      (s, nextCol (j := j) (k := 1) (by decide)) ↔
    K.Reachable (r, nextCol (j := j') (k := 1) (by decide))
      (s, nextCol (j := j') (k := 1) (by decide)) := by
  have hQ := oneColumn_suffix_eq_of_masks_eq hm hH hK hHor hDiag hV
  have hBoundary (r s : Fin m) :
      (prefixPart j 1 H).Reachable (Sum.inr r) (Sum.inr s) ↔
        (prefixPart j' 1 K).Reachable (Sum.inr r) (Sum.inr s) := by
    rw [← stateAt_reach_iff hm (by decide), ← stateAt_reach_iff hm (by decide), hReach]
  have hc := CylinderFrontier.glue_suffix_reachable_iff
    (suffixPart j 1 H) hAttachH hAttachK hBoundary
    (Sum.inl (r, (0 : Fin 1))) (Sum.inl (s, (0 : Fin 1)))
  rw [hQ] at hc
  have hleft := SimpleGraph.Iso.reachable_iff (φ := glueIso hm hH)
    (u := Sum.inr (Sum.inr (r, (0 : Fin 1))))
    (v := Sum.inr (Sum.inr (s, (0 : Fin 1))))
  have hright := SimpleGraph.Iso.reachable_iff (φ := glueIso hm hK)
    (u := Sum.inr (Sum.inr (r, (0 : Fin 1))))
    (v := Sum.inr (Sum.inr (s, (0 : Fin 1))))
  change H.Reachable (r, nextCol (j := j) (k := 1) (by decide))
      (s, nextCol (j := j) (k := 1) (by decide)) ↔
    (CylinderFrontier.glue (prefixPart j 1 H) (suffixPart j 1 H)).Reachable
      (Sum.inr (Sum.inr (r, (0 : Fin 1))))
      (Sum.inr (Sum.inr (s, (0 : Fin 1)))) at hleft
  rw [hQ] at hleft
  exact hleft.trans (hc.trans hright.symm)

end TriangularCylinder.ColumnStep
