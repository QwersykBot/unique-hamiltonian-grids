import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Saturation of a supplied cycle in a connected two-regular graph

The input walk is an arbitrary supplied standard `Walk.IsCycle`. Its own
subgraph is closed under ambient adjacency because both local degrees are
two. Connectedness therefore forces that same cycle to visit every vertex.
No cycle-existence constructor or replacement cycle is used.
-/

namespace CycleSaturation

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every supplied standard cycle in a finite connected two-regular graph
is itself a standard Hamiltonian cycle. -/
theorem isHamiltonianCycle_of_neighbor_ncard_two [Finite V] [DecidableEq V]
    (hG : G.Connected) (hdegree : ∀ w : V, (G.neighborSet w).ncard = 2)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) : p.IsHamiltonianCycle := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hcycles : G.IsCycles := fun {w} _ => hdegree w
  have hclosed : ∀ w ∈ p.toSubgraph.verts, ∀ x, G.Adj w x → p.toSubgraph.Adj w x := by
    intro w hw x hwx
    exact (hp.adj_toSubgraph_iff_of_isCycles hcycles hw x).mpr hwx
  have hsupport : ∀ w : V, w ∈ p.support := by
    intro w
    exact p.mem_verts_toSubgraph.mp
      ((hG v w).mem_subgraphVerts hclosed p.start_mem_verts_toSubgraph)
  refine Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
    ⟨hp, fun w => ?_⟩
  apply List.count_eq_one_of_mem hp.support_nodup
  by_cases hw : w = v
  · subst w
    exact p.end_mem_tail_support hp.not_nil
  · have hmem := hsupport w
    rw [p.support_eq_cons] at hmem
    exact (List.mem_cons.mp hmem).resolve_left hw

/-- Consequently the length of that supplied cycle equals the total number
of vertices; there is no separate spanning hypothesis. -/
theorem length_eq_card_of_neighbor_ncard_two [Fintype V] [DecidableEq V]
    (hG : G.Connected) (hdegree : ∀ w : V, (G.neighborSet w).ncard = 2)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) : p.length = Fintype.card V :=
  (isHamiltonianCycle_of_neighbor_ncard_two hG hdegree hp).length_eq

end CycleSaturation
