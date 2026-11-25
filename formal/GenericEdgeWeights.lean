import CylinderSplice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Additive trail weights depend only on selected undirected edges

This bridge uses Mathlib's walks and trail predicate, and the frozen
`CylinderSplice.edgeWeight` definition. It makes no counting, quotient,
orientation-multiplicity, or cylinder-topology claim.
-/

open scoped BigOperators

namespace CountedHamiltonian

open SimpleGraph

universe u v

variable {V : Type u} [DecidableEq V]

/-- The finite set of undirected edges selected by a walk. -/
def selectedEdges {G : SimpleGraph V} {x y : V} (p : G.Walk x y) :
    Finset (Sym2 V) :=
  p.edges.toFinset

/-- The finite representation agrees with Mathlib's walk edge set. -/
theorem coe_selectedEdges {G : SimpleGraph V} {x y : V} (p : G.Walk x y) :
    (selectedEdges p : Set (Sym2 V)) = p.edgeSet :=
  Walk.coe_edges_toFinset p

/-- Equality of Mathlib edge sets gives equality of the finite selected sets.
The walks may have different endpoints and even different ambient graphs. -/
theorem selectedEdges_eq_of_edgeSet_eq
    {G H : SimpleGraph V} {x y x' y' : V}
    (p : G.Walk x y) (q : H.Walk x' y') (h : p.edgeSet = q.edgeSet) :
    selectedEdges p = selectedEdges q := by
  apply Finset.coe_injective
  simpa only [coe_selectedEdges] using h

/-- A trail uses each selected edge once, so its list weight is exactly the
finite sum of the weights of its selected undirected edges. -/
theorem edgeWeight_eq_sum_selectedEdges
    {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.IsTrail) :
    CylinderSplice.edgeWeight w p = ∑ e ∈ selectedEdges p, w e := by
  simpa only [CylinderSplice.edgeWeight, selectedEdges] using
    (List.sum_toFinset w hp.edges_nodup).symm

/-- Additive weights of trails agree whenever their selected edge sets agree.
No common starting vertex, direction, or traversal presentation is assumed. -/
theorem edgeWeight_eq_of_selectedEdges_eq
    {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    {G H : SimpleGraph V} {x y x' y' : V}
    (p : G.Walk x y) (q : H.Walk x' y')
    (hp : p.IsTrail) (hq : q.IsTrail)
    (h : selectedEdges p = selectedEdges q) :
    CylinderSplice.edgeWeight w p = CylinderSplice.edgeWeight w q := by
  rw [edgeWeight_eq_sum_selectedEdges w p hp,
    edgeWeight_eq_sum_selectedEdges w q hq, h]

/-- The same presentation-independence statement using Mathlib's edgeSet. -/
theorem edgeWeight_eq_of_edgeSet_eq
    {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    {G H : SimpleGraph V} {x y x' y' : V}
    (p : G.Walk x y) (q : H.Walk x' y')
    (hp : p.IsTrail) (hq : q.IsTrail)
    (h : p.edgeSet = q.edgeSet) :
    CylinderSplice.edgeWeight w p = CylinderSplice.edgeWeight w q :=
  edgeWeight_eq_of_selectedEdges_eq w p q hp hq
    (selectedEdges_eq_of_edgeSet_eq p q h)

/-- Hamiltonian-cycle specialization; the base vertices may differ. -/
theorem hamiltonianCycle_edgeWeight_eq_of_selectedEdges_eq
    {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    {G H : SimpleGraph V} {x y : V}
    (p : G.Walk x x) (q : H.Walk y y)
    (hp : p.IsHamiltonianCycle) (hq : q.IsHamiltonianCycle)
    (h : selectedEdges p = selectedEdges q) :
    CylinderSplice.edgeWeight w p = CylinderSplice.edgeWeight w q :=
  edgeWeight_eq_of_selectedEdges_eq w p q
    hp.isCycle.isCircuit.isTrail hq.isCycle.isCircuit.isTrail h

/-- Hamiltonian-cycle specialization expressed with Mathlib's edgeSet. -/
theorem hamiltonianCycle_edgeWeight_eq_of_edgeSet_eq
    {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    {G H : SimpleGraph V} {x y : V}
    (p : G.Walk x x) (q : H.Walk y y)
    (hp : p.IsHamiltonianCycle) (hq : q.IsHamiltonianCycle)
    (h : p.edgeSet = q.edgeSet) :
    CylinderSplice.edgeWeight w p = CylinderSplice.edgeWeight w q :=
  hamiltonianCycle_edgeWeight_eq_of_selectedEdges_eq w p q hp hq
    (selectedEdges_eq_of_edgeSet_eq p q h)

end CountedHamiltonian
