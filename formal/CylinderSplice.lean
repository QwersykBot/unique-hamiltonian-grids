import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# A generic two-cycle splice

This file formalizes the graph-theoretic join used in the released square and
triangular cylinder manuscripts.  It does not formalize either cylinder theorem.
In particular it makes no claim about annular topology, frontier states, or
asymptotic counting.

Two cycles are presented with the selected deleted edge first.  Their remaining
paths have disjoint supports and jointly cover the ambient vertex type.  Two
available seam edges then give an actual `SimpleGraph.Walk.IsHamiltonianCycle`.
The edge-list and additive-weight lemmas record the exact edge replacement.
-/

namespace CylinderSplice

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
variable {a₀ a₁ b₀ b₁ : V}

/-- Delete the first edge of each original cycle and connect the remaining
paths using the two supplied seam edges.  The second path is oriented from
`b₀` to `b₁`, so the two seam edges are `a₀ b₀` and `b₁ a₁`. -/
def splice (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁) : G.Walk a₀ a₀ :=
  .cons seam₀ (q.append (.cons seam₁ p))

/-- The new traversal uses exactly the two seams and the two paths obtained
by deleting the designated cycle edges. -/
theorem splice_edges (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁) :
    (splice p q seam₀ seam₁).edges =
      s(a₀, b₀) :: (q.edges ++ s(b₁, a₁) :: p.edges) := by
  simp [splice, Walk.edges_append]

/-- The tail of the joined cycle visits, in order, all vertices of `q` and
then all vertices of `p`.  There are no unrecorded identifications. -/
theorem splice_tail_support (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁) :
    (splice p q seam₀ seam₁).support.tail = q.support ++ p.support := by
  simp [splice, Walk.support_append]

/-- Two disjoint paths jointly covering the vertex type can be closed with
two seam edges into a Hamiltonian cycle.  The noncoincidence hypothesis rules
out the degenerate two-edge traversal; it holds when `p` comes from deleting
an edge of a simple cycle. -/
theorem splice_paths_isHamiltonianCycle [DecidableEq V]
    (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisjoint : List.Disjoint p.support q.support)
    (hcover : ∀ x : V, x ∈ p.support ∨ x ∈ q.support)
    (hne : a₀ ≠ a₁) :
    (splice p q seam₀ seam₁).IsHamiltonianCycle := by
  have hpath : (q.append (.cons seam₁ p)).IsPath := by
    apply Walk.IsPath.mk'
    simp only [Walk.support_append, Walk.support_cons, List.tail_cons]
    exact List.nodup_append.mpr ⟨hq.support_nodup, hp.support_nodup, hdisjoint.symm⟩
  have hamiltonian : (q.append (.cons seam₁ p)).IsHamiltonian := by
    apply hpath.isHamiltonian_of_mem
    intro x
    simpa only [Walk.support_append, Walk.support_cons, List.tail_cons,
      List.mem_append, or_comm] using hcover x
  have hnotedge : s(a₀, b₀) ∉ (q.append (.cons seam₁ p)).edges := by
    simp only [Walk.edges_append, Walk.edges_cons, List.mem_append, List.mem_cons]
    rintro (hqedge | hseam | hpedge)
    · exact hdisjoint (p.end_mem_support) (q.fst_mem_support_of_mem_edges hqedge)
    · have hends := Sym2.eq_iff.mp hseam
      rcases hends with h | h
      · exact hdisjoint (p.end_mem_support) (h.1.symm ▸ q.end_mem_support)
      · exact hne h.1
    · exact hdisjoint (p.snd_mem_support_of_mem_edges hpedge) (q.start_mem_support)
  refine ⟨?_, ?_⟩
  · exact (Walk.cons_isCycle_iff _ seam₀).mpr ⟨hpath, hnotedge⟩
  · simpa [splice, Walk.IsHamiltonian] using hamiltonian

/-- Generic complete-cycle splice: the two input cycles are given with the
chosen deleted edges first.  Their remaining paths partition all ambient
vertices.  The output is Hamiltonian in Mathlib's standard sense. -/
theorem splice_cycles_isHamiltonianCycle [DecidableEq V]
    (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (deleted₀ : G.Adj a₀ a₁) (deleted₁ : G.Adj b₁ b₀)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁)
    (hcycle₀ : (Walk.cons deleted₀ p).IsCycle)
    (hcycle₁ : (Walk.cons deleted₁ q).IsCycle)
    (hdisjoint : List.Disjoint p.support q.support)
    (hcover : ∀ x : V, x ∈ p.support ∨ x ∈ q.support) :
    (splice p q seam₀ seam₁).IsHamiltonianCycle := by
  exact splice_paths_isHamiltonianCycle p q seam₀ seam₁
    ((Walk.cons_isCycle_iff p deleted₀).mp hcycle₀).1
    ((Walk.cons_isCycle_iff q deleted₁).mp hcycle₁).1
    hdisjoint hcover deleted₀.ne

/-- Removing the designated first edge of a cycle leaves exactly the edge
set of its remaining path.  The cycle hypothesis supplies the required
nonrepetition of that edge. -/
theorem cycle_delete_first_edgeSet {x y : V} (p : G.Walk y x)
    (deleted : G.Adj x y) (hcycle : (Walk.cons deleted p).IsCycle) :
    (Walk.cons deleted p).edgeSet \ {s(x, y)} = p.edgeSet := by
  rw [Walk.edgeSet_cons]
  exact Set.insert_diff_self_of_not_mem ((Walk.cons_isCycle_iff p deleted).mp hcycle).2

/-- Set-level version of the exact graph surgery: remove the chosen edge
from each input cycle and insert precisely the two seam edges. -/
theorem splice_edgeSet
    (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (deleted₀ : G.Adj a₀ a₁) (deleted₁ : G.Adj b₁ b₀)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁)
    (hcycle₀ : (Walk.cons deleted₀ p).IsCycle)
    (hcycle₁ : (Walk.cons deleted₁ q).IsCycle) :
    (splice p q seam₀ seam₁).edgeSet =
      insert s(a₀, b₀) (insert s(b₁, a₁)
        (((Walk.cons deleted₀ p).edgeSet \ {s(a₀, a₁)}) ∪
          ((Walk.cons deleted₁ q).edgeSet \ {s(b₁, b₀)}))) := by
  rw [cycle_delete_first_edgeSet p deleted₀ hcycle₀,
    cycle_delete_first_edgeSet q deleted₁ hcycle₁]
  ext e
  simp [splice, Walk.edgeSet_append, or_comm, or_left_comm, or_assoc]

/-- Additive edge weight of a walk.  Taking the codomain to be `ZMod 2`
and the weight to record meridian crossings gives the combinatorial parity
calculation, once the cylinder edge geometry has been supplied separately. -/
def edgeWeight {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    {x y : V} (p : G.Walk x y) : W :=
  (p.edges.map w).sum

/-- Exact additive bookkeeping for the splice.  The equality of the total
deleted-edge and inserted-edge weights is explicit; no topological premise
is hidden in the proof. -/
theorem splice_edgeWeight
    {W : Type v} [AddCommMonoid W] (w : Sym2 V → W)
    (p : G.Walk a₁ a₀) (q : G.Walk b₀ b₁)
    (deleted₀ : G.Adj a₀ a₁) (deleted₁ : G.Adj b₁ b₀)
    (seam₀ : G.Adj a₀ b₀) (seam₁ : G.Adj b₁ a₁)
    (hbalance : w s(a₀, a₁) + w s(b₁, b₀) =
      w s(a₀, b₀) + w s(b₁, a₁)) :
    edgeWeight w (splice p q seam₀ seam₁) =
      edgeWeight w (.cons deleted₀ p) + edgeWeight w (.cons deleted₁ q) := by
  simp only [edgeWeight, splice_edges, Walk.edges_cons, List.map_cons,
    List.map_append, List.sum_cons, List.sum_append]
  calc
    w s(a₀, b₀) + ((List.map w q.edges).sum +
        (w s(b₁, a₁) + (List.map w p.edges).sum)) =
        (w s(a₀, b₀) + w s(b₁, a₁)) +
          ((List.map w p.edges).sum + (List.map w q.edges).sum) := by ac_rfl
    _ = (w s(a₀, a₁) + w s(b₁, b₀)) +
          ((List.map w p.edges).sum + (List.map w q.edges).sum) := by rw [hbalance]
    _ = (w s(a₀, a₁) + (List.map w p.edges).sum) +
          (w s(b₁, b₀) + (List.map w q.edges).sum) := by ac_rfl

#print axioms splice_cycles_isHamiltonianCycle
#print axioms splice_edgeSet
#print axioms splice_edgeWeight

end CylinderSplice
