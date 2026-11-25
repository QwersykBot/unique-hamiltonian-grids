import FragmentRecovery
import ProcessedPrefix

/-!
# Advancing a completed prefix by one column

These coordinate lemmas expose the next cut of a canonical prefix replacement.
They preserve exact prefix and suffix graphs and the physical masks used by a
one-column extension. No parity identity or accepted-object realization is
assumed or proved in this module.
-/

namespace TriangularCylinder.CompletionTransport

open SimpleGraph ColumnCut ColumnFragments BoundaryState Transfer
open ProcessedPrefix FragmentRecovery PrefixReplacement

/-- Reassociate the column count to expose the next processed boundary. -/
def advanceGraph {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    SimpleGraph (Vertex m ((j + 1) + 1 + k)) :=
  H.comap (widthEquiv (by omega))

def advanceIso {m j k : ℕ} (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    advanceGraph H ≃g H := SimpleGraph.Iso.comap (widthEquiv (by omega)) H

theorem advanceGraph_le {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    (hH : H ≤ graph m (j + 1 + (k + 1)) hm) :
    advanceGraph H ≤ graph m ((j + 1) + 1 + k) hm := by
  calc
    advanceGraph H ≤ (graph m (j + 1 + (k + 1)) hm).comap (widthEquiv (by omega)) :=
      SimpleGraph.comap_monotone (widthEquiv (by omega)).toEmbedding hH
    _ = graph m ((j + 1) + 1 + k) hm := widthEquiv_graph_comap hm _

theorem advanceGraph_connected {m j k : ℕ}
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))} (hH : H.Connected) :
    (advanceGraph H).Connected :=
  hH.map (advanceIso H).symm.toHom (advanceIso H).symm.toEquiv.surjective

theorem advanceGraph_ncard_two {m j k : ℕ}
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    (hH : ∀ v, (H.neighborSet v).ncard = 2) :
    ∀ v, ((advanceGraph H).neighborSet v).ncard = 2 := by
  intro v
  have h := congrArg ENat.toNat (Set.encard_congr ((advanceIso H).mapNeighborSet v))
  exact h.trans (hH _)

/-- The short graph containing precisely the old prefix and one new column. -/
def nextPrefix {m j k : ℕ} (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    SimpleGraph (Vertex m (j + 2)) :=
  normalizedPrefix (j + 1) k (advanceGraph H)

theorem nextPrefix_le {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    (hH : H ≤ graph m (j + 1 + (k + 1)) hm) :
    nextPrefix H ≤ graph m (j + 2) hm :=
  normalizedPrefix_le hm (advanceGraph_le hm hH)

theorem nextPrefix_old_prefix {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    prefixPart j 1 (nextPrefix H) = prefixPart j (k + 1) H := by
  ext x y
  cases x <;> cases y <;> rfl

theorem nextPrefix_old_horizontal {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    (stateAt (j := j) (k := 1) hm (by decide) (nextPrefix H)).horizontal =
      (stateAt hm (by omega) H).horizontal := by
  funext r
  rw [Bool.eq_iff_iff, stateAt_horizontal_iff, stateAt_horizontal_iff]
  rfl

theorem nextPrefix_old_diagonal {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    (stateAt (j := j) (k := 1) hm (by decide) (nextPrefix H)).diagonal =
      (stateAt hm (by omega) H).diagonal := by
  funext r
  rw [Bool.eq_iff_iff, stateAt_diagonal_iff, stateAt_diagonal_iff]
  rfl

theorem nextPrefix_old_reach {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    (stateAt (j := j) (k := 1) hm (by decide) (nextPrefix H)).reach =
      (stateAt hm (by omega) H).reach := by
  funext r s
  rw [Bool.eq_iff_iff, stateAt_reach_iff, stateAt_reach_iff, nextPrefix_old_prefix]

theorem nextPrefix_vertical {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) :
    verticalMask hm (nextPrefix H) (nextCol (j := j) (k := 1) (by decide)) =
      verticalMask hm H (nextCol (j := j) (k := k + 1) (by omega)) := by
  funext r
  rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
  rfl

theorem nextPrefix_reachable_iff {m j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) (r s : Fin m) :
    (stateAt hm hk (advanceGraph H)).reach r s = true ↔
      (nextPrefix H).Reachable (r, nextCol (j := j) (k := 1) (by decide))
        (s, nextCol (j := j) (k := 1) (by decide)) := by
  rw [stateAt_reach_iff]
  exact (SimpleGraph.Iso.reachable_iff
    (φ := normalizedPrefixIso (advanceGraph H))
    (u := Sum.inr r) (v := Sum.inr s)).symm

/-- Exact old prefix graphs and physical extension choices determine the
entire new prefix graph, with no connectedness premise. -/
theorem nextPrefix_eq_of_old_data {m j k k' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    {K : SimpleGraph (Vertex m (j + 1 + (k' + 1)))}
    (hH : H ≤ graph m (j + 1 + (k + 1)) hm)
    (hK : K ≤ graph m (j + 1 + (k' + 1)) hm)
    (hP : prefixPart j (k + 1) H = prefixPart j (k' + 1) K)
    (hHor : (stateAt hm (by omega) H).horizontal = (stateAt hm (by omega) K).horizontal)
    (hDiag : (stateAt hm (by omega) H).diagonal = (stateAt hm (by omega) K).diagonal)
    (hV : verticalMask hm H (nextCol (by omega)) = verticalMask hm K (nextCol (by omega))) :
    nextPrefix H = nextPrefix K := by
  have hp : prefixPart j 1 (nextPrefix H) = prefixPart j 1 (nextPrefix K) := by
    rw [nextPrefix_old_prefix, nextPrefix_old_prefix, hP]
  have hq := ColumnStep.oneColumn_suffix_eq_of_masks_eq hm
    (nextPrefix_le hm hH) (nextPrefix_le hm hK)
    ((nextPrefix_old_horizontal hm H).trans (hHor.trans (nextPrefix_old_horizontal hm K).symm))
    ((nextPrefix_old_diagonal hm H).trans (hDiag.trans (nextPrefix_old_diagonal hm K).symm))
    ((nextPrefix_vertical hm H).trans (hV.trans (nextPrefix_vertical hm K).symm))
  have hc : (nextPrefix H).comap (vertexEquiv m j 1) =
      (nextPrefix K).comap (vertexEquiv m j 1) := by
    rw [← glue_parts_eq_comap (j := j) (k := 1) hm (nextPrefix_le hm hH),
      ← glue_parts_eq_comap (j := j) (k := 1) hm (nextPrefix_le hm hK), hp, hq]
  ext x y
  obtain ⟨u, rfl⟩ := (vertexEquiv m j 1).surjective x
  obtain ⟨v, rfl⟩ := (vertexEquiv m j 1).surjective y
  change ((nextPrefix H).comap (vertexEquiv m j 1)).Adj u v ↔
    ((nextPrefix K).comap (vertexEquiv m j 1)).Adj u v
  rw [hc]

theorem normalizedPrefix_comap {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + k))) :
    (normalizedPrefix j k H).comap (prefixCoord j) = prefixPart j k H := by
  ext x y
  change H.Adj (columnInclusion j k (prefixCoord j x))
    (columnInclusion j k (prefixCoord j y)) ↔ H.Adj (prefixVertex j k x) (prefixVertex j k y)
  rw [columnInclusion_prefixCoord, columnInclusion_prefixCoord]

theorem advance_prefix_eq_of_nextPrefix_eq {m j k k' : ℕ}
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    {K : SimpleGraph (Vertex m (j + 1 + (k' + 1)))}
    (h : nextPrefix H = nextPrefix K) :
    prefixPart (j + 1) k (advanceGraph H) = prefixPart (j + 1) k' (advanceGraph K) := by
  rw [← normalizedPrefix_comap, ← normalizedPrefix_comap]
  exact congrArg (fun G => G.comap (prefixCoord (j + 1))) h

/-- Reachability at the new cut follows from the old three non-parity fields
and the physical new-column mask. Original connectedness supplies attachment. -/
theorem advance_reach_eq {m j j' k k' : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (hk' : 1 ≤ k')
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    {K : SimpleGraph (Vertex m (j' + 1 + (k' + 1)))}
    (hH : H ≤ graph m (j + 1 + (k + 1)) hm)
    (hK : K ≤ graph m (j' + 1 + (k' + 1)) hm)
    (hconnH : H.Connected) (hconnK : K.Connected)
    (hHor : (stateAt hm (by omega) H).horizontal = (stateAt hm (by omega) K).horizontal)
    (hDiag : (stateAt hm (by omega) H).diagonal = (stateAt hm (by omega) K).diagonal)
    (hReach : (stateAt hm (by omega) H).reach = (stateAt hm (by omega) K).reach)
    (hV : verticalMask hm H (nextCol (by omega)) = verticalMask hm K (nextCol (by omega))) :
    (stateAt hm hk (advanceGraph H)).reach = (stateAt hm hk' (advanceGraph K)).reach := by
  have haH : CylinderFrontier.TouchesBoundary (prefixPart j 1 (nextPrefix H)) := by
    rw [nextPrefix_old_prefix]
    exact prefixPart_touchesBoundary hm hH hconnH
  have haK : CylinderFrontier.TouchesBoundary (prefixPart j' 1 (nextPrefix K)) := by
    rw [nextPrefix_old_prefix]
    exact prefixPart_touchesBoundary hm hK hconnK
  funext r s
  rw [Bool.eq_iff_iff, nextPrefix_reachable_iff, nextPrefix_reachable_iff]
  exact ColumnStep.nextColumn_reachable_iff hm (nextPrefix_le hm hH) (nextPrefix_le hm hK)
    haH haK
    ((nextPrefix_old_horizontal hm H).trans (hHor.trans (nextPrefix_old_horizontal hm K).symm))
    ((nextPrefix_old_diagonal hm H).trans (hDiag.trans (nextPrefix_old_diagonal hm K).symm))
    ((nextPrefix_old_reach hm H).trans (hReach.trans (nextPrefix_old_reach hm K).symm))
    ((nextPrefix_vertical hm H).trans (hV.trans (nextPrefix_vertical hm K).symm)) r s

theorem suffixPart_interior_adj {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + k))) (x y : Vertex m k) :
    (suffixPart j k H).Adj (Sum.inl x) (Sum.inl y) ↔
      H.Adj (suffixVertex j k (Sum.inl x)) (suffixVertex j k (Sum.inl y)) :=
  ⟨And.left, fun h => ⟨h, x, Or.inl rfl⟩⟩

theorem advance_suffix_coordinate {m j k : ℕ} (x : Vertex m k ⊕ Fin m) :
    widthEquiv (show (j + 1) + 1 + k = j + 1 + (k + 1) by omega)
      (suffixVertex (j + 1) k x) =
      suffixVertex j (k + 1) (Sum.inl (suffixCoord k x)) := by
  cases x with
  | inl x =>
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change j + 1 + 1 + x.2.val = j + 1 + (x.2.val + 1)
        omega
  | inr r => rfl

theorem advance_suffix_adj {m j k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + (k + 1)))) (x y : Vertex m k ⊕ Fin m) :
    (suffixPart (j + 1) k (advanceGraph H)).Adj x y ↔
      (suffixPart j (k + 1) H).Adj (Sum.inl (suffixCoord k x)) (Sum.inl (suffixCoord k y)) ∧
        ∃ o : Vertex m k, x = Sum.inl o ∨ y = Sum.inl o := by
  rw [suffixPart_interior_adj]
  change (H.Adj (widthEquiv _ (suffixVertex (j + 1) k x))
    (widthEquiv _ (suffixVertex (j + 1) k y)) ∧ _) ↔ _
  rw [advance_suffix_coordinate, advance_suffix_coordinate]

/-- Moving the cut one column right preserves equality of the remaining suffixes. -/
theorem advance_suffix_eq {m j j' k : ℕ}
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    {K : SimpleGraph (Vertex m (j' + 1 + (k + 1)))}
    (hQ : suffixPart j (k + 1) H = suffixPart j' (k + 1) K) :
    suffixPart (j + 1) k (advanceGraph H) = suffixPart (j' + 1) k (advanceGraph K) := by
  ext x y
  rw [advance_suffix_adj, advance_suffix_adj, hQ]

/-- The first suffix column's vertical mask is determined by that exact suffix. -/
theorem next_vertical_eq_of_suffix_eq {m j j' k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))}
    {K : SimpleGraph (Vertex m (j' + 1 + (k + 1)))}
    (hQ : suffixPart j (k + 1) H = suffixPart j' (k + 1) K) :
    verticalMask hm H (nextCol (by omega)) = verticalMask hm K (nextCol (by omega)) := by
  funext r
  rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
  change H.Adj (suffixVertex j (k + 1) (Sum.inl (r, (0 : Fin (k + 1)))))
      (suffixVertex j (k + 1) (Sum.inl (TriangularEdgeEncoding.rowSucc hm r, (0 : Fin (k + 1))))) ↔
    K.Adj (suffixVertex j' (k + 1) (Sum.inl (r, (0 : Fin (k + 1)))))
      (suffixVertex j' (k + 1) (Sum.inl (TriangularEdgeEncoding.rowSucc hm r, (0 : Fin (k + 1)))))
  rw [← suffixPart_interior_adj, ← suffixPart_interior_adj, hQ]

/-- A specified cut and total width determine the remaining split uniquely. -/
theorem stateAt_split_eq_cutState {m n k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1))
    (hwidth : c.val + 1 + k = n + 2) :
    stateAt hm hk (H.comap (widthEquiv hwidth)) = cutState hm H c := by
  have hkEq : k = cutTail c := by have h := cutWidth_eq c; omega
  subst k
  rfl

theorem prefixPart_split_eq_cutGraph {m n k : ℕ}
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1))
    (hwidth : c.val + 1 + k = n + 2) :
    prefixPart c.val k (H.comap (widthEquiv hwidth)) =
      prefixPart c.val (cutTail c) (cutGraph H c) := by
  have hkEq : k = cutTail c := by have h := cutWidth_eq c; omega
  subst k
  rfl

theorem advance_comap_widthEquiv {m j k L : ℕ}
    (H : SimpleGraph (Vertex m L)) (h : j + 1 + (k + 1) = L)
    (h' : (j + 1) + 1 + k = L) :
    advanceGraph (H.comap (widthEquiv h)) = H.comap (widthEquiv h') := by
  ext x y
  rfl

#print axioms advanceGraph_le
#print axioms advanceGraph_connected
#print axioms advanceGraph_ncard_two
#print axioms nextPrefix_le
#print axioms nextPrefix_old_prefix
#print axioms nextPrefix_old_horizontal
#print axioms nextPrefix_old_diagonal
#print axioms nextPrefix_old_reach
#print axioms nextPrefix_vertical
#print axioms nextPrefix_reachable_iff
#print axioms nextPrefix_eq_of_old_data
#print axioms normalizedPrefix_comap
#print axioms advance_prefix_eq_of_nextPrefix_eq
#print axioms advance_reach_eq
#print axioms suffixPart_interior_adj
#print axioms advance_suffix_coordinate
#print axioms advance_suffix_adj
#print axioms advance_suffix_eq
#print axioms next_vertical_eq_of_suffix_eq
#print axioms stateAt_split_eq_cutState
#print axioms prefixPart_split_eq_cutGraph
#print axioms advance_comap_widthEquiv

end TriangularCylinder.CompletionTransport
