import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# The standard Hamiltonian interface for connected degree-two graphs

Mathlib's `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`
already supplies the substantive cycle-existence theorem. These wrappers use
connectedness to obtain full vertex coverage and express the result using
Mathlib's standard `Walk.IsHamiltonianCycle` predicate.

No spanning cycle or Hamiltonicity is assumed. Degree two excludes the
degenerate small graphs, so a separate vertex-cardinality bound is unnecessary.
This is a finite graph-theoretic result with no topology or counting claim.
-/

namespace ConnectedTwoRegular

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Every chosen root of a finite connected degree-two graph lies on a
standard Hamiltonian cycle, using Mathlib's component-spanning cycle theorem. -/
theorem exists_isHamiltonianCycle_at_of_neighbor_ncard_two
    [Finite V] [DecidableEq V] (hG : G.Connected)
    (hdegree : ∀ v : V, (G.neighborSet v).ncard = 2) (v : V) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  have hcycles : G.IsCycles := fun {w} _ => hdegree w
  have hneighbor : (G.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hdegree v]; decide)
  obtain ⟨p, hp, hverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := G.connectedComponentMk v) (by rfl) hneighbor
  refine ⟨p, Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
    ⟨hp, fun w => ?_⟩⟩
  apply List.count_eq_one_of_mem hp.support_nodup
  by_cases hw : w = v
  · subst w
    exact p.end_mem_tail_support hp.not_nil
  · have hmem : w ∈ p.support := by
      apply p.mem_verts_toSubgraph.mp
      rw [hverts]
      change G.connectedComponentMk w = G.connectedComponentMk v
      exact ConnectedComponent.sound (hG w v)
    rw [p.support_eq_cons] at hmem
    exact (List.mem_cons.mp hmem).resolve_left hw

/-- Existence form with the root supplied by actual graph connectedness. -/
theorem exists_isHamiltonianCycle_of_neighbor_ncard_two
    [Finite V] [DecidableEq V] (hG : G.Connected)
    (hdegree : ∀ v : V, (G.neighborSet v).ncard = 2) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨p, hp⟩ := exists_isHamiltonianCycle_at_of_neighbor_ncard_two hG hdegree v
  exact ⟨v, p, hp⟩

/-- Convenience interface using the usual graph degree. `LocallyFinite`
provides the finite neighbor enumerations used by that definition. -/
theorem exists_isHamiltonianCycle_of_degree_two
    [Finite V] [DecidableEq V] [LocallyFinite G] (hG : G.Connected)
    (hdegree : ∀ v : V, G.degree v = 2) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  apply exists_isHamiltonianCycle_of_neighbor_ncard_two hG
  intro v
  simpa only [Set.ncard_eq_toFinset_card', degree, neighborFinset] using hdegree v

#print axioms exists_isHamiltonianCycle_at_of_neighbor_ncard_two
#print axioms exists_isHamiltonianCycle_of_neighbor_ncard_two
#print axioms exists_isHamiltonianCycle_of_degree_two

end ConnectedTwoRegular
