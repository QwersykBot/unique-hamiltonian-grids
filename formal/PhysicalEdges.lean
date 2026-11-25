import TriangularCylinder

/-!
# Physical identifiers for the exact triangular-cylinder edges

The three disjoint identifier families represent vertical, horizontal, and
consistently oriented diagonal edges. The circumference is at least three;
there is no lower bound on the number of columns. No topological or
Hamiltonian-cycle premise is used.
-/

namespace TriangularEdgeEncoding

open TriangularCylinder

/-- Vertical identifiers, followed by horizontal and diagonal identifiers. -/
abbrev EdgeId (m L : ℕ) :=
  (Fin m × Fin L) ⊕ ((Fin m × Fin (L - 1)) ⊕ (Fin m × Fin (L - 1)))

def rowSucc {m : ℕ} (hm : 3 ≤ m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩

def lowerCol {L : ℕ} (j : Fin (L - 1)) : Fin L :=
  ⟨j.val, by have hj := j.isLt; omega⟩

def upperCol {L : ℕ} (j : Fin (L - 1)) : Fin L :=
  ⟨j.val + 1, by have hj := j.isLt; omega⟩

def sourceVertex {m L : ℕ} : EdgeId m L → Vertex m L
  | .inl e => e
  | .inr (.inl e) => (e.1, lowerCol e.2)
  | .inr (.inr e) => (e.1, lowerCol e.2)

def targetVertex {m L : ℕ} (hm : 3 ≤ m) : EdgeId m L → Vertex m L
  | .inl e => (rowSucc hm e.1, e.2)
  | .inr (.inl e) => (e.1, upperCol e.2)
  | .inr (.inr e) => (rowSucc hm e.1, upperCol e.2)

/-- The actual unordered pair of endpoints of a physical edge identifier. -/
def toEdge {m L : ℕ} (hm : 3 ≤ m) (e : EdgeId m L) : Sym2 (Vertex m L) :=
  s(sourceVertex e, targetVertex hm e)

theorem nextRow_rowSucc {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    NextRow i (rowSucc hm i) := rfl

/-- A cyclic row step cannot also be a step in the opposite direction when
the circumference is at least three. This fails at circumference two. -/
theorem nextRow_asymm {m : ℕ} (hm : 3 ≤ m) {r s : Fin m}
    (h : NextRow r s) : ¬ NextRow s r := by
  intro h'
  unfold NextRow at h h'
  have hr := r.isLt
  have hs := s.isLt
  by_cases hrl : r.val + 1 < m
  · rw [Nat.mod_eq_of_lt hrl] at h
    by_cases hsl : s.val + 1 < m
    · rw [Nat.mod_eq_of_lt hsl] at h'
      omega
    · have heq : s.val + 1 = m := by omega
      rw [heq, Nat.mod_self] at h'
      omega
  · have heq : r.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at h
    have hsl : s.val + 1 < m := by omega
    rw [Nat.mod_eq_of_lt hsl] at h'
    omega

theorem forward_col_le {m L : ℕ} {x y : Vertex m L} (h : Forward x y) :
    x.2.val ≤ y.2.val := by
  rcases h with ⟨hc, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · exact le_of_eq (congrArg Fin.val hc)
  · omega
  · omega

theorem forward_asymm {m L : ℕ} (hm : 3 ≤ m) {x y : Vertex m L}
    (h : Forward x y) : ¬ Forward y x := by
  intro h'
  have hle := forward_col_le h'
  rcases h with ⟨hc, hr⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · rcases h' with ⟨_, hr'⟩ | ⟨_, hc'⟩ | ⟨_, hc'⟩
    · exact nextRow_asymm hm hr hr'
    · have hv := congrArg Fin.val hc
      omega
    · have hv := congrArg Fin.val hc
      omega
  · omega
  · omega

theorem forward_source_target {m L : ℕ} (hm : 3 ≤ m) (e : EdgeId m L) :
    Forward (sourceVertex e) (targetVertex hm e) := by
  rcases e with e | e | e
  · exact Or.inl ⟨rfl, nextRow_rowSucc hm e.1⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨nextRow_rowSucc hm e.1, rfl⟩)

theorem toEdge_mem_edgeSet {m L : ℕ} (hm : 3 ≤ m) (e : EdgeId m L) :
    toEdge hm e ∈ (graph m L hm).edgeSet :=
  (SimpleGraph.mem_edgeSet (graph m L hm)).mpr (Or.inl (forward_source_target hm e))

/-- Equal unordered edges have the same forward-oriented endpoints. -/
theorem toEdge_endpoints {m L : ℕ} (hm : 3 ≤ m) {e f : EdgeId m L}
    (h : toEdge hm e = toEdge hm f) :
    sourceVertex e = sourceVertex f ∧ targetVertex hm e = targetVertex hm f := by
  rcases Sym2.eq_iff.mp h with h | ⟨hs, ht⟩
  · exact h
  · have hf := forward_source_target hm f
    rw [← hs, ← ht] at hf
    exact False.elim (forward_asymm hm (forward_source_target hm e) hf)

theorem toEdge_injective {m L : ℕ} (hm : 3 ≤ m) :
    Function.Injective (toEdge (L := L) hm) := by
  intro e f h
  have hs := (toEdge_endpoints hm h).1
  have ht := (toEdge_endpoints hm h).2
  rcases e with e | e | e <;> rcases f with f | f | f
  all_goals
    have hsr := congrArg (fun v : Vertex m L => v.1) hs
    have hsc := congrArg (fun v : Vertex m L => v.2.val) hs
    have htr := congrArg (fun v : Vertex m L => v.1) ht
    have htc := congrArg (fun v : Vertex m L => v.2.val) ht
    simp only [sourceVertex, targetVertex, lowerCol, upperCol] at hsr hsc htr htc
  · exact congrArg Sum.inl hs
  · omega
  · omega
  · omega
  · exact congrArg (fun p => Sum.inr (Sum.inl p)) (Prod.ext hsr (Fin.ext hsc))
  · exact False.elim ((nextRow_ne hm (nextRow_rowSucc hm f.1)) (hsr.symm.trans htr))
  · omega
  · exact False.elim ((nextRow_ne hm (nextRow_rowSucc hm e.1)) (hsr.trans htr.symm))
  · exact congrArg (fun p => Sum.inr (Sum.inr p)) (Prod.ext hsr (Fin.ext hsc))

theorem exists_toEdge_of_forward {m L : ℕ} (hm : 3 ≤ m)
    (x y : Vertex m L) (h : Forward x y) :
    ∃ e : EdgeId m L, toEdge hm e = s(x, y) := by
  rcases x with ⟨r, c⟩
  rcases y with ⟨s, d⟩
  change (c = d ∧ NextRow r s) ∨ (r = s ∧ c.val + 1 = d.val) ∨
    (NextRow r s ∧ c.val + 1 = d.val) at h
  rcases h with ⟨hc, hr⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
  · have hrs : rowSucc hm r = s := Fin.ext hr.symm
    refine ⟨.inl (r, c), ?_⟩
    simp only [toEdge, sourceVertex, targetVertex, hrs, hc]
  · have hj : c.val < L - 1 := by have hd := d.isLt; omega
    let j : Fin (L - 1) := ⟨c.val, hj⟩
    have hlo : lowerCol j = c := Fin.ext rfl
    have hup : upperCol j = d := Fin.ext hc
    refine ⟨.inr (.inl (r, j)), ?_⟩
    simp only [toEdge, sourceVertex, targetVertex, hlo, hup, hr]
  · have hj : c.val < L - 1 := by have hd := d.isLt; omega
    let j : Fin (L - 1) := ⟨c.val, hj⟩
    have hlo : lowerCol j = c := Fin.ext rfl
    have hup : upperCol j = d := Fin.ext hc
    have hrs : rowSucc hm r = s := Fin.ext hr.symm
    refine ⟨.inr (.inr (r, j)), ?_⟩
    simp only [toEdge, sourceVertex, targetVertex, hlo, hup, hrs]

/-- Every undirected graph edge has a physical identifier. -/
theorem exists_toEdge {m L : ℕ} (hm : 3 ≤ m)
    (e : Sym2 (Vertex m L)) (he : e ∈ (graph m L hm).edgeSet) :
    ∃ id : EdgeId m L, toEdge hm id = e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    rcases (SimpleGraph.mem_edgeSet (graph m L hm)).mp he with h | h
    · exact exists_toEdge_of_forward hm x y h
    · obtain ⟨id, hid⟩ := exists_toEdge_of_forward hm y x h
      exact ⟨id, hid.trans Sym2.eq_swap⟩

def toGraphEdge {m L : ℕ} (hm : 3 ≤ m) (e : EdgeId m L) :
    (graph m L hm).edgeSet :=
  ⟨toEdge hm e, toEdge_mem_edgeSet hm e⟩

theorem toGraphEdge_bijective {m L : ℕ} (hm : 3 ≤ m) :
    Function.Bijective (toGraphEdge (L := L) hm) := by
  constructor
  · intro e f h
    exact toEdge_injective hm (congrArg Subtype.val h)
  · intro e
    obtain ⟨id, hid⟩ := exists_toEdge hm e.val e.property
    exact ⟨id, Subtype.ext hid⟩

/-- Physical V/H/D identifiers are exactly the edges of the simple graph.
The inverse is chosen from the proved bijection; no multigraph convention is
silently collapsed into this circumference-at-least-three statement. -/
noncomputable def edgeEquiv {m L : ℕ} (hm : 3 ≤ m) :
    EdgeId m L ≃ (graph m L hm).edgeSet :=
  Equiv.ofBijective (toGraphEdge hm) (toGraphEdge_bijective hm)

@[simp] theorem edgeEquiv_apply_val {m L : ℕ} (hm : 3 ≤ m) (e : EdgeId m L) :
    (edgeEquiv hm e).val = toEdge hm e := rfl

end TriangularEdgeEncoding
