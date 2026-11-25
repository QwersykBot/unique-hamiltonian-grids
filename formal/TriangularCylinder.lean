import CylinderSplice

/-!
# Concrete consistently triangulated cylinders

This development instantiates the generic graph splice on the exact finite
vertex and edge families of the released triangular-cylinder manuscript.
Rows are cyclic, columns are finite intervals, and every diagonal has the
same orientation.  Contractibility, frontier states, and counting asymptotics
are outside the statement proved here.
-/

namespace TriangularCylinder

open SimpleGraph

abbrev Vertex (m L : ℕ) := Fin m × Fin L

/-- A positively oriented cyclic row step, including the last-to-first gap. -/
def NextRow {m : ℕ} (r s : Fin m) : Prop :=
  s.val = (r.val + 1) % m

theorem nextRow_ne {m : ℕ} (hm : 3 ≤ m) {r s : Fin m} (h : NextRow r s) : r ≠ s := by
  intro hrs
  subst s
  unfold NextRow at h
  have hr := r.isLt
  by_cases hlt : r.val + 1 < m
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have heq : r.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at h
    omega

/-- Vertical, horizontal, and consistently oriented diagonal forward edges. -/
def Forward {m L : ℕ} (x y : Vertex m L) : Prop :=
  (x.2 = y.2 ∧ NextRow x.1 y.1) ∨
  (x.1 = y.1 ∧ x.2.val + 1 = y.2.val) ∨
  (NextRow x.1 y.1 ∧ x.2.val + 1 = y.2.val)

theorem not_forward_self {m L : ℕ} (hm : 3 ≤ m) (x : Vertex m L) : ¬ Forward x x := by
  rintro (⟨_, hrow⟩ | ⟨_, hcol⟩ | ⟨_, hcol⟩)
  · exact nextRow_ne hm hrow rfl
  · omega
  · omega

/-- The exact simple graph at circumference at least three.  An undirected
edge is a forward vertical/horizontal/diagonal edge in either orientation. -/
def graph (m L : ℕ) (hm : 3 ≤ m) : SimpleGraph (Vertex m L) where
  Adj x y := Forward x y ∨ Forward y x
  symm _ _ h := h.elim Or.inr Or.inl
  loopless x h := h.elim (not_forward_self hm x) (not_forward_self hm x)

def firstCol (L : ℕ) (hL : 2 ≤ L) : Fin L := ⟨0, by omega⟩

def lastCol (L : ℕ) (hL : 2 ≤ L) : Fin L := ⟨L - 1, by omega⟩

/-- Embed the left block without changing a row or column number. -/
def leftVertex {m a : ℕ} (b : ℕ) (x : Vertex m a) : Vertex m (a + b) :=
  (x.1, Fin.castAdd b x.2)

/-- Embed the right block by translating its column number by `a`. -/
def rightVertex {m b : ℕ} (a : ℕ) (x : Vertex m b) : Vertex m (a + b) :=
  (x.1, Fin.natAdd a x.2)

theorem leftVertex_injective {m a b : ℕ} :
    Function.Injective (leftVertex (m := m) (a := a) b) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : Vertex m (a + b) => z.1) h
  · apply Fin.ext
    exact congrArg (fun z : Vertex m (a + b) => z.2.val) h

theorem rightVertex_injective {m a b : ℕ} :
    Function.Injective (rightVertex (m := m) (b := b) a) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : Vertex m (a + b) => z.1) h
  · apply Fin.ext
    have hc := congrArg (fun z : Vertex m (a + b) => z.2.val) h
    simpa [rightVertex] using hc

theorem forward_left_iff {m a b : ℕ} (x y : Vertex m a) :
    Forward (leftVertex b x) (leftVertex b y) ↔ Forward x y := by
  simp [Forward, leftVertex, Fin.ext_iff]

theorem forward_right_iff {m a b : ℕ} (x y : Vertex m b) :
    Forward (rightVertex a x) (rightVertex a y) ↔ Forward x y := by
  simp [Forward, rightVertex, Fin.ext_iff, Nat.add_assoc]

def leftHom {m a b : ℕ} (hm : 3 ≤ m) : graph m a hm →g graph m (a + b) hm where
  toFun := leftVertex b
  map_rel' := by
    intro x y h
    change Forward (leftVertex b x) (leftVertex b y) ∨
      Forward (leftVertex b y) (leftVertex b x)
    simpa only [forward_left_iff] using h

def rightHom {m a b : ℕ} (hm : 3 ≤ m) : graph m b hm →g graph m (a + b) hm where
  toFun := rightVertex a
  map_rel' := by
    intro x y h
    change Forward (rightVertex a x) (rightVertex a y) ∨
      Forward (rightVertex a y) (rightVertex a x)
    simpa only [forward_right_iff] using h

theorem left_ne_right {m a b : ℕ} (x : Vertex m a) (y : Vertex m b) :
    leftVertex b x ≠ rightVertex a y := by
  intro h
  have hc := congrArg (fun z : Vertex m (a + b) => z.2.val) h
  simp only [leftVertex, rightVertex, Fin.coe_castAdd, Fin.coe_natAdd] at hc
  have hx := x.2.isLt
  omega

/-- The two embedded column blocks partition every vertex of the joined graph. -/
theorem vertex_partition {m a b : ℕ} (x : Vertex m (a + b)) :
    (∃ y : Vertex m a, leftVertex b y = x) ∨
    (∃ y : Vertex m b, rightVertex a y = x) := by
  by_cases hleft : x.2.val < a
  · left
    refine ⟨(x.1, ⟨x.2.val, hleft⟩), ?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl
  · right
    have hright : x.2.val - a < b := by
      have hx := x.2.isLt
      omega
    refine ⟨(x.1, ⟨x.2.val - a, hright⟩), ?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change a + (x.2.val - a) = x.2.val
      omega

theorem vertical_edge {m L : ℕ} (hm : 3 ≤ m) (r s : Fin m)
    (hgap : NextRow r s) (c : Fin L) : (graph m L hm).Adj (r, c) (s, c) :=
  Or.inl (Or.inl ⟨rfl, hgap⟩)

/-- The seam joins the last left column to the first right column in one row. -/
theorem horizontal_seam {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (r : Fin m) :
    (graph m (a + b) hm).Adj
      (leftVertex b (r, lastCol a ha)) (rightVertex a (r, firstCol b hb)) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  refine ⟨rfl, ?_⟩
  change (a - 1) + 1 = a + 0
  omega

/-- Concrete joined traversal.  The chosen right input cycle edge is oriented
from `s` to `r`, so its remaining path goes from `r` to `s`. -/
def spliceAt {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (r s : Fin m)
    (p : (graph m a hm).Walk (s, lastCol a ha) (r, lastCol a ha))
    (q : (graph m b hm).Walk (r, firstCol b hb) (s, firstCol b hb)) :
    (graph m (a + b) hm).Walk
      (leftVertex b (r, lastCol a ha)) (leftVertex b (r, lastCol a ha)) :=
  CylinderSplice.splice (p.map (leftHom hm)) (q.map (rightHom hm))
    (horizontal_seam hm ha hb r) (horizontal_seam hm ha hb s).symm

/-- All-width concrete triangular-cylinder splice.  The hypotheses are two
actual Hamiltonian cycles containing the prescribed vertical boundary edges.
No abstract cylinder-splicing or frontier-state conclusion is assumed. -/
theorem spliceAt_isHamiltonianCycle
    {m a b : ℕ} (hm : 3 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (r s : Fin m) (hgap : NextRow r s)
    (p : (graph m a hm).Walk (s, lastCol a ha) (r, lastCol a ha))
    (q : (graph m b hm).Walk (r, firstCol b hb) (s, firstCol b hb))
    (hp : (Walk.cons (vertical_edge hm r s hgap (lastCol a ha)) p).IsHamiltonianCycle)
    (hq : (Walk.cons (vertical_edge hm r s hgap (firstCol b hb)).symm q).IsHamiltonianCycle) :
    (spliceAt hm ha hb r s p q).IsHamiltonianCycle := by
  have hpPath : p.IsHamiltonian := by
    simpa [Walk.IsHamiltonian] using hp.isHamiltonian_tail
  have hqPath : q.IsHamiltonian := by
    simpa [Walk.IsHamiltonian] using hq.isHamiltonian_tail
  apply CylinderSplice.splice_cycles_isHamiltonianCycle
    (p.map (leftHom hm)) (q.map (rightHom hm))
    ((leftHom hm).map_adj (vertical_edge hm r s hgap (lastCol a ha)))
    ((rightHom hm).map_adj (vertical_edge hm r s hgap (firstCol b hb)).symm)
    (horizontal_seam hm ha hb r) (horizontal_seam hm ha hb s).symm
  · simpa only [Walk.map_cons] using hp.isCycle.map
      (leftVertex_injective (m := m) (a := a) (b := b))
  · simpa only [Walk.map_cons] using hq.isCycle.map
      (rightVertex_injective (m := m) (a := a) (b := b))
  · intro x hx hy
    simp only [Walk.support_map, List.mem_map] at hx hy
    rcases hx with ⟨xl, _, hl⟩
    rcases hy with ⟨xr, _, hr⟩
    exact left_ne_right xl xr (hl.trans hr.symm)
  · intro x
    rcases vertex_partition x with ⟨xl, hl⟩ | ⟨xr, hr⟩
    · left
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨xl, hpPath.mem_support xl, hl⟩
    · right
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨xr, hqPath.mem_support xr, hr⟩

#print axioms spliceAt_isHamiltonianCycle

end TriangularCylinder
