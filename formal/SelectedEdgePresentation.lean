import CylinderSplice

/-!
# Presenting a Hamiltonian cycle at any selected oriented edge

The input is an arbitrary standard Hamiltonian closed walk and membership of
an unordered edge in its selected edges. The resulting cycle begins with that
edge in the requested orientation and has a permutation of the original edge
list, so every additive unordered-edge weight is unchanged.
-/

namespace SelectedEdgePresentation

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A cyclic change of the cut in a closed walk preserves Hamiltonicity. -/
theorem isHamiltonianCycle_append_swap {u v : V}
    (p : G.Walk u v) (q : G.Walk v u)
    (h : (p.append q).IsHamiltonianCycle) : (q.append p).IsHamiltonianCycle := by
  have hc := h.isCycle
  have hc' : (q.append p).IsCycle := by
    rw [Walk.isCycle_def] at hc ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append_comm,
        ← Walk.edges_append, ← Walk.isTrail_def]
      exact hc.1
    · intro hz
      apply hc.2.1
      apply Walk.length_eq_zero_iff.mp
      have hlen : (q.append p).length = 0 := by rw [hz]; rfl
      simpa only [Walk.length_append, Nat.add_comm] using hlen
    · rw [Walk.tail_support_append, List.nodup_append_comm, ← Walk.tail_support_append]
      exact hc.2.2
  apply Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
  refine ⟨hc', ?_⟩
  intro z
  have hz := (Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp h).2 z
  simpa only [Walk.tail_support_append, List.count_append, Nat.add_comm] using hz

/-- Reversing a standard Hamiltonian cycle preserves Hamiltonicity. -/
theorem isHamiltonianCycle_reverse {u : V} (p : G.Walk u u)
    (h : p.IsHamiltonianCycle) : p.reverse.IsHamiltonianCycle := by
  apply Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
  refine ⟨h.isCycle.reverse, ?_⟩
  intro z
  have heq : p.reverse.support.count z = p.support.count z := by
    rw [Walk.support_reverse, List.count_reverse]
  rw [Walk.support_eq_cons p.reverse, Walk.support_eq_cons p] at heq
  simp only [List.count_cons] at heq
  have hz := (Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp h).2 z
  omega

omit [DecidableEq V] in
/-- A selected unordered edge occurs as a directed step in one of its two
orientations, with an exact prefix and suffix. -/
theorem edge_decomposition {u v x y : V} (p : G.Walk u v)
    (he : s(x, y) ∈ p.edges) :
    (∃ (h : G.Adj x y) (a : G.Walk u x) (b : G.Walk y v),
      p = a.append (Walk.cons h b)) ∨
    (∃ (h : G.Adj y x) (a : G.Walk u y) (b : G.Walk x v),
      p = a.append (Walk.cons h b)) := by
  induction p with
  | nil => simp only [Walk.edges_nil, List.not_mem_nil] at he
  | @cons u z v h p ih =>
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨h, Walk.nil, p, rfl⟩
      · exact Or.inr ⟨h, Walk.nil, p, rfl⟩
    · rcases ih he with ⟨hxy, a, b, hab⟩ | ⟨hyx, a, b, hab⟩
      · exact Or.inl ⟨hxy, Walk.cons h a, b, by rw [hab]; rfl⟩
      · exact Or.inr ⟨hyx, Walk.cons h a, b, by rw [hab]; rfl⟩

/-- Any selected edge admits an edge-first Hamiltonian presentation in an
arbitrarily specified orientation, preserving the full unordered edge list
up to permutation. -/
theorem exists_edge_first {u x y : V} (C : G.Walk u u)
    (hC : C.IsHamiltonianCycle) (he : s(x, y) ∈ C.edges) :
    ∃ (hxy : G.Adj x y) (p : G.Walk y x),
      (Walk.cons hxy p).IsHamiltonianCycle ∧
      (Walk.cons hxy p).edges.Perm C.edges := by
  rcases edge_decomposition C he with ⟨hxy, a, b, rfl⟩ | ⟨hyx, a, b, rfl⟩
  · refine ⟨hxy, b.append a, isHamiltonianCycle_append_swap a (Walk.cons hxy b) hC, ?_⟩
    change ((Walk.cons hxy b).append a).edges.Perm (a.append (Walk.cons hxy b)).edges
    simpa only [Walk.edges_append] using List.perm_append_comm
  · have hr : (b.reverse.append (Walk.cons hyx.symm a.reverse)).IsHamiltonianCycle := by
      simpa only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc,
        Walk.cons_nil_append] using isHamiltonianCycle_reverse (a.append (Walk.cons hyx b)) hC
    refine ⟨hyx.symm, a.reverse.append b.reverse,
      isHamiltonianCycle_append_swap b.reverse (Walk.cons hyx.symm a.reverse) hr, ?_⟩
    have hperm : ((Walk.cons hyx.symm a.reverse).append b.reverse).edges.Perm
        (b.reverse.append (Walk.cons hyx.symm a.reverse)).edges := by
      simpa only [Walk.edges_append] using List.perm_append_comm
    have hrev : (b.reverse.append (Walk.cons hyx.symm a.reverse)).edges =
        (a.append (Walk.cons hyx b)).reverse.edges := by
      simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc,
        Walk.cons_nil_append]
    rw [hrev, Walk.edges_reverse] at hperm
    exact hperm.trans (List.reverse_perm _)

omit [DecidableEq V] in
theorem edgeSet_eq_of_edges_perm {u v x y : V}
    (p : G.Walk u v) (q : G.Walk x y) (h : p.edges.Perm q.edges) :
    p.edgeSet = q.edgeSet := by
  ext e
  exact h.mem_iff

omit [DecidableEq V] in
theorem edgeWeight_eq_of_edges_perm {W : Type*} [AddCommMonoid W]
    (w : Sym2 V → W) {u v x y : V}
    (p : G.Walk u v) (q : G.Walk x y) (h : p.edges.Perm q.edges) :
    CylinderSplice.edgeWeight w p = CylinderSplice.edgeWeight w q := by
  exact (h.map w).sum_eq

/-- The same presentation records both the selected edge set and any chosen
additive unordered-edge weight. -/
theorem exists_edge_first_with_weight {W : Type*} [AddCommMonoid W]
    (w : Sym2 V → W) {u x y : V} (C : G.Walk u u)
    (hC : C.IsHamiltonianCycle) (he : s(x, y) ∈ C.edges) :
    ∃ (hxy : G.Adj x y) (p : G.Walk y x),
      (Walk.cons hxy p).IsHamiltonianCycle ∧
      (Walk.cons hxy p).edgeSet = C.edgeSet ∧
      CylinderSplice.edgeWeight w (Walk.cons hxy p) = CylinderSplice.edgeWeight w C := by
  obtain ⟨hxy, p, hp, hperm⟩ := exists_edge_first C hC he
  exact ⟨hxy, p, hp, edgeSet_eq_of_edges_perm _ _ hperm,
    edgeWeight_eq_of_edges_perm w _ _ hperm⟩

#print axioms isHamiltonianCycle_append_swap
#print axioms isHamiltonianCycle_reverse
#print axioms exists_edge_first
#print axioms exists_edge_first_with_weight

end SelectedEdgePresentation
