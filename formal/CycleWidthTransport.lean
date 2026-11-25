import ActualTransfer

/-!
# Walks and selected graphs under equal-width transport

The homomorphism below uses the existing `Transfer.widthEquiv`, preserving
the row and numeric column. Equality elimination reduces the walk, selected
graph, and type-parity statements to the identity transport. No new width
equivalence, parity definition, local label, or terminal label is introduced.
-/

namespace TriangularCylinder.CycleWidthTransport

open SimpleGraph

/-- The existing coordinate-preserving width equivalence as a graph homomorphism. -/
def widthHom {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L') :
    graph m L hm →g graph m L' hm where
  toFun := Transfer.widthEquiv h
  map_rel' := by
    intro x y hxy
    subst L'
    exact hxy

@[simp] theorem widthHom_apply {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L')
    (x : Vertex m L) :
    widthHom hm h x = Transfer.widthEquiv h x := rfl

@[simp] theorem widthHom_row {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L')
    (x : Vertex m L) :
    (widthHom hm h x).1 = x.1 := rfl

@[simp] theorem widthHom_col_val {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L')
    (x : Vertex m L) :
    (widthHom hm h x).2.val = x.2.val := rfl

theorem widthHom_bijective {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L') :
    Function.Bijective (widthHom hm h) :=
  (Transfer.widthEquiv h).bijective

@[simp] theorem widthHom_refl {m L : ℕ} (hm : 3 ≤ m) :
    widthHom (L := L) hm rfl = Hom.id := by
  apply DFunLike.ext
  intro x
  rfl

/-- Equal-width transport preserves a standard Hamiltonian cycle. -/
theorem map_isHamiltonianCycle {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L')
    {v : Vertex m L} (C : (graph m L hm).Walk v v) (hC : C.IsHamiltonianCycle) :
    (C.map (widthHom hm h)).IsHamiltonianCycle :=
  hC.map (widthHom hm h) (widthHom_bijective hm h)

/-- Type parity is preserved for every walk, including nonclosed walks. -/
theorem typeParity_map {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L')
    {x y : Vertex m L} (C : (graph m L hm).Walk x y) :
    typeParity hm (C.map (widthHom hm h)) = typeParity hm C := by
  cases h
  change typeParity hm (C.map Hom.id) = typeParity hm C
  rw [Walk.map_id]

/-- The transported selected graph pulls back the original selected graph
along the inverse width equivalence, from target vertices to source vertices. -/
theorem selectedGraph_map {m L L' : ℕ} (hm : 3 ≤ m) (h : L = L')
    {x y : Vertex m L} (C : (graph m L hm).Walk x y) :
    fromEdgeSet (C.map (widthHom hm h)).edgeSet =
      (fromEdgeSet C.edgeSet).comap (Transfer.widthEquiv h.symm) := by
  cases h
  change fromEdgeSet (C.map Hom.id).edgeSet = fromEdgeSet C.edgeSet
  rw [Walk.map_id]

#print axioms widthHom_apply
#print axioms widthHom_row
#print axioms widthHom_col_val
#print axioms widthHom_bijective
#print axioms widthHom_refl
#print axioms map_isHamiltonianCycle
#print axioms typeParity_map
#print axioms selectedGraph_map

end TriangularCylinder.CycleWidthTransport
