import BoundaryState
import ThreeColumnWitnessCut
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# The common raw state of the two- and three-column witnesses

The outgoing masks, actual-prefix reachability, and assigned physical-edge
parity are computed from the selected edges of the explicit checked cycles.
No transition or return in a transfer-state model is asserted.
-/

namespace TriangularCylinder

open SimpleGraph TriangularEdgeEncoding BoundaryState

/-- The two extreme horizontal crossings, one prefix component, and zero parity. -/
def commonWitnessState (m : ℕ) (hm : 3 ≤ m) : RawBoundaryState m where
  horizontal := fun r => decide (r = firstRow m hm ∨ r = lastRow m hm)
  diagonal := fun _ => false
  reach := fun _ _ => true
  parity := 0

private theorem selected_walk_edge_iff {V : Type*} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (e : Sym2 V) :
    e ∈ (fromEdgeSet p.edgeSet).edgeSet ↔ e ∈ p.edges := by
  rw [edgeSet_fromEdgeSet]
  change (e ∈ p.edges ∧ ¬ e.IsDiag) ↔ e ∈ p.edges
  exact ⟨And.left, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)⟩⟩

private theorem selected_walk_adj_iff {V : Type*} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (x y : V) :
    (fromEdgeSet p.edgeSet).Adj x y ↔ s(x, y) ∈ p.edges := by
  rw [← SimpleGraph.mem_edgeSet, selected_walk_edge_iff]

/-- A walk contained in processed columns gives actual prefix reachability.
Its edges must be selected, but no connectedness premise is used. -/
private theorem prefix_reachable_of_walk {m j k : ℕ}
    {G H : SimpleGraph (Vertex m (j + 1 + k))} {a b : Vertex m (j + 1 + k)}
    (p : G.Walk a b)
    (hcols : ∀ x ∈ p.support, x.2.val ≤ j)
    (hedges : ∀ e ∈ p.edges, e ∈ H.edgeSet)
    (r s : Fin m)
    (hr : (r, boundaryCol j k) ∈ p.support)
    (hs : (s, boundaryCol j k) ∈ p.support) :
    (ColumnCut.prefixPart j k H).Reachable (Sum.inr r) (Sum.inr s) := by
  classical
  let embed := ColumnCut.prefixVertex (m := m) j k
  have hinj : Function.Injective embed :=
    (ColumnCut.vertexEquiv m j k).injective.comp
      (CylinderFrontier.prefixEmbedding (Vertex m j) (Fin m) (Vertex m k)).injective
  have hrange : ∀ x ∈ p.support, ∃ y, embed y = x := by
    intro x hx
    have hc := hcols x hx
    by_cases hlt : x.2.val < j
    · refine ⟨Sum.inl (x.1, ⟨x.2.val, hlt⟩), ?_⟩
      apply Prod.ext
      · rfl
      · exact Fin.ext rfl
    · have heq : x.2.val = j := by omega
      refine ⟨Sum.inr x.1, ?_⟩
      apply Prod.ext
      · rfl
      · exact Fin.ext heq.symm
  let lift : p.toSubgraph.verts → Vertex m j ⊕ Fin m :=
    fun x => Classical.choose (hrange x.val (p.mem_verts_toSubgraph.mp x.property))
  have hlift (x : p.toSubgraph.verts) : embed (lift x) = x.val :=
    Classical.choose_spec (hrange x.val (p.mem_verts_toSubgraph.mp x.property))
  let liftHom : p.toSubgraph.coe →g ColumnCut.prefixPart j k H := {
    toFun := lift
    map_rel' := by
      intro x y hxy
      change H.Adj (embed (lift x)) (embed (lift y))
      rw [hlift, hlift]
      exact (SimpleGraph.mem_edgeSet H).mp
        (hedges _ (p.mem_edges_toSubgraph.mp (Subgraph.mem_edgeSet.mpr hxy)))
  }
  let x : p.toSubgraph.verts := ⟨(r, boundaryCol j k), p.mem_verts_toSubgraph.mpr hr⟩
  let y : p.toSubgraph.verts := ⟨(s, boundaryCol j k), p.mem_verts_toSubgraph.mpr hs⟩
  have hx : liftHom x = Sum.inr r := hinj (hlift x)
  have hy : liftHom y = Sum.inr s := hinj (hlift y)
  simpa only [hx, hy] using (p.toSubgraph_connected x y).map liftHom

theorem perimeterCycle_selected_edgeWeight_zero (n : ℕ) (hn : 2 ≤ n)
    (e : Sym2 (Vertex (n + 1) 2)) (he : e ∈ (perimeterCycle n hn).edges) :
    meridianWeight (show 3 ≤ n + 1 by omega) e = 0 := by
  rcases (mem_perimeterCycle_edges n hn e).mp he with h | ⟨i, hi⟩
  · rw [h]
    exact perimeter_closing_weight n hn
  · rw [← hi]
    exact perimeterVertex_edgeWeight_zero n hn i

theorem threeWitnessCycle_selected_edgeWeight_zero (n : ℕ) (hn : 2 ≤ n)
    (e : Sym2 (Vertex (n + 1) 3)) (he : e ∈ (threeWitnessCycle n hn).edges) :
    meridianWeight (show 3 ≤ n + 1 by omega) e = 0 := by
  rcases (mem_threeWitnessCycle_edges n hn e).mp he with h | ⟨i, hi⟩
  · rw [h]
    exact threeWitness_closing_weight n hn
  · rw [← hi]
    exact threeWitnessVertex_edgeWeight_zero n hn i

private theorem assignedParity_zero_of_selected_zero {m j k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (j + 1 + k)))
    (hzero : ∀ e ∈ H.edgeSet, meridianWeight hm e = 0) : assignedParity hm H = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  exact hzero (toEdge hm e) ((mem_assignedIds hm H e).mp he).1

theorem perimeterCycle_state_horizontal (n : ℕ) (hn : 2 ≤ n) (r : Fin (n + 1)) :
    (stateAt (j := 0) (k := 1) (by omega) (by decide)
      (fromEdgeSet (perimeterCycle n hn).edgeSet)).horizontal r =
        decide (r = firstRow (n + 1) (by omega) ∨ r = lastRow (n + 1) (by omega)) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, stateAt_horizontal_iff, selected_walk_adj_iff]
  simpa only [eq_self_iff_true, true_and] using perimeterCycle_lastCut_edges_iff n hn r r

theorem threeWitnessCycle_state_horizontal (n : ℕ) (hn : 2 ≤ n) (r : Fin (n + 1)) :
    (stateAt (j := 1) (k := 1) (by omega) (by decide)
      (fromEdgeSet (threeWitnessCycle n hn).edgeSet)).horizontal r =
        decide (r = firstRow (n + 1) (by omega) ∨ r = lastRow (n + 1) (by omega)) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, stateAt_horizontal_iff, selected_walk_adj_iff]
  simpa only [eq_self_iff_true, true_and] using threeWitnessCycle_lastCut_edges_iff n hn r r

theorem perimeterCycle_state_diagonal (n : ℕ) (hn : 2 ≤ n) (r : Fin (n + 1)) :
    (stateAt (j := 0) (k := 1) (by omega) (by decide)
      (fromEdgeSet (perimeterCycle n hn).edgeSet)).diagonal r = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (stateAt_diagonal_iff (j := 0) (k := 1) (by omega) (by decide)
    (fromEdgeSet (perimeterCycle n hn).edgeSet) r).mp h
  have hrows := ((perimeterCycle_lastCut_edges_iff n hn r (rowSucc (by omega) r)).mp
    ((selected_walk_adj_iff (perimeterCycle n hn) _ _).mp he)).1
  exact (nextRow_ne (by omega) (nextRow_rowSucc (by omega) r)) hrows

theorem threeWitnessCycle_state_diagonal (n : ℕ) (hn : 2 ≤ n) (r : Fin (n + 1)) :
    (stateAt (j := 1) (k := 1) (by omega) (by decide)
      (fromEdgeSet (threeWitnessCycle n hn).edgeSet)).diagonal r = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (stateAt_diagonal_iff (j := 1) (k := 1) (by omega) (by decide)
    (fromEdgeSet (threeWitnessCycle n hn).edgeSet) r).mp h
  have hrows := ((threeWitnessCycle_lastCut_edges_iff n hn r (rowSucc (by omega) r)).mp
    ((selected_walk_adj_iff (threeWitnessCycle n hn) _ _).mp he)).1
  exact (nextRow_ne (by omega) (nextRow_rowSucc (by omega) r)) hrows

theorem perimeterCycle_prefix_reachable (n : ℕ) (hn : 2 ≤ n) (r s : Fin (n + 1)) :
    (ColumnCut.prefixPart 0 1 (fromEdgeSet (perimeterCycle n hn).edgeSet)).Reachable
      (Sum.inr r) (Sum.inr s) := by
  apply prefix_reachable_of_walk (perimeterPrefixWalk n hn)
  · intro x hx
    have hc := (perimeterPrefixWalk_support_iff n hn x).mp hx
    simp only [hc, Fin.val_zero, le_refl]
  · intro e he
    exact (selected_walk_edge_iff (perimeterCycle n hn) e).mpr
      (perimeterPrefixWalk_edges_in_cycle n hn e he)
  · exact (perimeterPrefixWalk_support_iff n hn _).mpr rfl
  · exact (perimeterPrefixWalk_support_iff n hn _).mpr rfl

theorem threeWitnessCycle_prefix_reachable (n : ℕ) (hn : 2 ≤ n) (r s : Fin (n + 1)) :
    (ColumnCut.prefixPart 1 1 (fromEdgeSet (threeWitnessCycle n hn).edgeSet)).Reachable
      (Sum.inr r) (Sum.inr s) := by
  apply prefix_reachable_of_walk (threePrefixWalk n hn)
  · intro x hx
    have hc := (threePrefixWalk_support_iff n hn x).mp hx
    omega
  · intro e he
    exact (selected_walk_edge_iff (threeWitnessCycle n hn) e).mpr
      (threePrefixWalk_edges_in_cycle n hn e he)
  · exact (threePrefixWalk_support_iff n hn _).mpr (by change (1 : ℕ) < 2; decide)
  · exact (threePrefixWalk_support_iff n hn _).mpr (by change (1 : ℕ) < 2; decide)

theorem perimeterCycle_state_reach (n : ℕ) (hn : 2 ≤ n) (r s : Fin (n + 1)) :
    (stateAt (j := 0) (k := 1) (by omega) (by decide)
      (fromEdgeSet (perimeterCycle n hn).edgeSet)).reach r s = true :=
  (stateAt_reach_iff _ _ _ r s).mpr (perimeterCycle_prefix_reachable n hn r s)

theorem threeWitnessCycle_state_reach (n : ℕ) (hn : 2 ≤ n) (r s : Fin (n + 1)) :
    (stateAt (j := 1) (k := 1) (by omega) (by decide)
      (fromEdgeSet (threeWitnessCycle n hn).edgeSet)).reach r s = true :=
  (stateAt_reach_iff _ _ _ r s).mpr (threeWitnessCycle_prefix_reachable n hn r s)

theorem perimeterCycle_state_parity (n : ℕ) (hn : 2 ≤ n) :
    (stateAt (j := 0) (k := 1) (by omega) (by decide)
      (fromEdgeSet (perimeterCycle n hn).edgeSet)).parity = 0 := by
  apply assignedParity_zero_of_selected_zero
  intro e he
  exact perimeterCycle_selected_edgeWeight_zero n hn e
    ((selected_walk_edge_iff (perimeterCycle n hn) e).mp he)

theorem threeWitnessCycle_state_parity (n : ℕ) (hn : 2 ≤ n) :
    (stateAt (j := 1) (k := 1) (by omega) (by decide)
      (fromEdgeSet (threeWitnessCycle n hn).edgeSet)).parity = 0 := by
  apply assignedParity_zero_of_selected_zero
  intro e he
  exact threeWitnessCycle_selected_edgeWeight_zero n hn e
    ((selected_walk_edge_iff (threeWitnessCycle n hn) e).mp he)

theorem perimeterCycle_stateAt_common (n : ℕ) (hn : 2 ≤ n) :
    stateAt (j := 0) (k := 1) (by omega) (by decide)
      (fromEdgeSet (perimeterCycle n hn).edgeSet) = commonWitnessState (n + 1) (by omega) := by
  apply RawBoundaryState.ext
  · exact funext (perimeterCycle_state_horizontal n hn)
  · exact funext (perimeterCycle_state_diagonal n hn)
  · exact funext (fun r => funext (perimeterCycle_state_reach n hn r))
  · exact perimeterCycle_state_parity n hn

theorem threeWitnessCycle_stateAt_common (n : ℕ) (hn : 2 ≤ n) :
    stateAt (j := 1) (k := 1) (by omega) (by decide)
      (fromEdgeSet (threeWitnessCycle n hn).edgeSet) = commonWitnessState (n + 1) (by omega) := by
  apply RawBoundaryState.ext
  · exact funext (threeWitnessCycle_state_horizontal n hn)
  · exact funext (threeWitnessCycle_state_diagonal n hn)
  · exact funext (fun r => funext (threeWitnessCycle_state_reach n hn r))
  · exact threeWitnessCycle_state_parity n hn

theorem witness_states_eq (n : ℕ) (hn : 2 ≤ n) :
    stateAt (j := 0) (k := 1) (by omega) (by decide)
      (fromEdgeSet (perimeterCycle n hn).edgeSet) =
    stateAt (j := 1) (k := 1) (by omega) (by decide)
      (fromEdgeSet (threeWitnessCycle n hn).edgeSet) :=
  (perimeterCycle_stateAt_common n hn).trans (threeWitnessCycle_stateAt_common n hn).symm

/-- This raw state occurs in an actual Hamiltonian cylinder cycle at every width. -/
theorem commonWitnessState_occurs (m : ℕ) (hm : 3 ≤ m) :
    Occurs hm (commonWitnessState m hm) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  have h := occurs_stateAt (j := 0) (k := 1) hm (by decide) (perimeterCycle n hn)
    (perimeterCycle_isHamiltonianCycle n hn)
  simpa only [perimeterCycle_stateAt_common n hn] using h

end TriangularCylinder
