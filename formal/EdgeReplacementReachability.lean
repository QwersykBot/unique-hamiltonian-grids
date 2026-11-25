import Mathlib.Combinatorics.SimpleGraph.Path

/-!
# Replacing an edge by a connected gadget preserves old-vertex reachability

Remove the unordered edge `{x, y}` from a simple graph `G`. Add a disjoint
connected graph `A` and seams from `x` to `a` and from `b` to `y`, where `a`
and `b` are arbitrary gadget vertices, possibly equal. The replacement has
exactly the original reachability relation on old vertices, and every gadget
vertex reaches `x`.

No finiteness or degree assumptions are made. This module proves connectivity
facts only, not Hamiltonicity, an embedding theorem, or a counting bijection.
-/

namespace CylinderFrontier.EdgeReplacement

variable {V N : Type*}

/-- The connected gadget occupies the left summand; the surviving old graph
occupies the right summand. Distinct gadget attachment vertices are not required. -/
def replacementGraph (G : SimpleGraph V) (A : SimpleGraph N)
    (x y : V) (a b : N) : SimpleGraph (N ⊕ V) where
  Adj u v := match u, v with
    | Sum.inl n, Sum.inl m => A.Adj n m
    | Sum.inl n, Sum.inr v => (n = a ∧ v = x) ∨ (n = b ∧ v = y)
    | Sum.inr v, Sum.inl n => (n = a ∧ v = x) ∨ (n = b ∧ v = y)
    | Sum.inr v, Sum.inr w =>
        G.Adj v w ∧ ¬((v = x ∧ w = y) ∨ (v = y ∧ w = x))
  symm := by
    intro u v h
    cases u <;> cases v
    · exact A.symm h
    · exact h
    · exact h
    · refine ⟨G.symm h.1, ?_⟩
      intro hbad
      apply h.2
      rcases hbad with ⟨hv, hw⟩ | ⟨hv, hw⟩
      · exact Or.inr ⟨hw, hv⟩
      · exact Or.inl ⟨hw, hv⟩
  loopless := by
    intro u
    cases u
    · exact A.loopless _
    · exact fun h => G.loopless _ h.1

/-- Collapse the whole gadget to the old left endpoint. -/
def collapse (x : V) : N ⊕ V → V
  | Sum.inl _ => x
  | Sum.inr v => v

/-- The gadget itself embeds as a graph homomorphism. -/
def gadgetHom (G : SimpleGraph V) (A : SimpleGraph N)
    (x y : V) (a b : N) : SimpleGraph.Hom A (replacementGraph G A x y a b) where
  toFun := Sum.inl
  map_rel' := by
    intro n m h
    exact h

theorem left_seam (G : SimpleGraph V) (A : SimpleGraph N)
    (x y : V) (a b : N) :
    (replacementGraph G A x y a b).Adj (Sum.inl a) (Sum.inr x) := by
  exact Or.inl ⟨rfl, rfl⟩

theorem right_seam (G : SimpleGraph V) (A : SimpleGraph N)
    (x y : V) (a b : N) :
    (replacementGraph G A x y a b).Adj (Sum.inl b) (Sum.inr y) := by
  exact Or.inr ⟨rfl, rfl⟩

/-- The removed old edge is replaced by a path through the connected gadget. -/
theorem seam_path (G : SimpleGraph V) (A : SimpleGraph N) (hA : A.Connected)
    (x y : V) (a b : N) :
    (replacementGraph G A x y a b).Reachable (Sum.inr x) (Sum.inr y) := by
  exact ((left_seam G A x y a b).symm.reachable.trans
    ((hA.preconnected a b).map (gadgetHom G A x y a b))).trans
      (right_seam G A x y a b).reachable

/-- The collapse sends each replacement edge to original reachability. -/
theorem collapse_adj_reachable (G : SimpleGraph V) (A : SimpleGraph N)
    {x y : V} (hxy : G.Adj x y) (a b : N)
    {u v : N ⊕ V} (huv : (replacementGraph G A x y a b).Adj u v) :
    G.Reachable (collapse x u) (collapse x v) := by
  cases u with
  | inl n =>
    cases v with
    | inl m => exact SimpleGraph.Reachable.refl _
    | inr v =>
      rcases huv with ⟨_, hv⟩ | ⟨_, hv⟩
      · subst v
        exact SimpleGraph.Reachable.refl _
      · subst v
        exact hxy.reachable
  | inr u =>
    cases v with
    | inl n =>
      rcases huv with ⟨_, hu⟩ | ⟨_, hu⟩
      · subst u
        exact SimpleGraph.Reachable.refl _
      · subst u
        exact hxy.symm.reachable
    | inr v => exact huv.1.reachable

/-- Every original adjacency lifts to reachability, including the removed edge. -/
theorem old_adj_reachable (G : SimpleGraph V) (A : SimpleGraph N) (hA : A.Connected)
    (x y : V) (a b : N) {v w : V} (hvw : G.Adj v w) :
    (replacementGraph G A x y a b).Reachable (Sum.inr v) (Sum.inr w) := by
  classical
  by_cases hremoved : (v = x ∧ w = y) ∨ (v = y ∧ w = x)
  · rcases hremoved with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · subst v
      subst w
      exact seam_path G A hA x y a b
    · subst v
      subst w
      exact (seam_path G A hA x y a b).symm
  · exact (show (replacementGraph G A x y a b).Adj (Sum.inr v) (Sum.inr w) from
      ⟨hvw, hremoved⟩).reachable

private theorem transport_reachable {X Y : Type*}
    {H : SimpleGraph X} {K : SimpleGraph Y} (f : X → Y)
    (hadj : ∀ u v, H.Adj u v → K.Reachable (f u) (f v))
    {u v : X} (huv : H.Reachable u v) : K.Reachable (f u) (f v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
  exact Relation.ReflTransGen.lift' f
    (fun u v h => (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hadj u v h)) huv

/-- The replacement preserves the entire reachability relation on old vertices. -/
theorem old_reachable_iff (G : SimpleGraph V) (A : SimpleGraph N)
    {x y : V} (hxy : G.Adj x y) (hA : A.Connected) (a b : N) (v w : V) :
    (replacementGraph G A x y a b).Reachable (Sum.inr v) (Sum.inr w) ↔
      G.Reachable v w := by
  constructor
  · intro h
    exact transport_reachable (collapse x)
      (fun _ _ h => collapse_adj_reachable G A hxy a b h) h
  · intro h
    exact transport_reachable Sum.inr
      (fun _ _ h => old_adj_reachable G A hA x y a b h) h

/-- Every gadget vertex reaches the old left endpoint, even when `a = b`. -/
theorem gadget_reaches_left (G : SimpleGraph V) (A : SimpleGraph N) (hA : A.Connected)
    (x y : V) (a b n : N) :
    (replacementGraph G A x y a b).Reachable (Sum.inl n) (Sum.inr x) := by
  exact ((hA.preconnected n a).map (gadgetHom G A x y a b)).trans
    (left_seam G A x y a b).reachable

#print axioms old_reachable_iff
#print axioms gadget_reaches_left

end CylinderFrontier.EdgeReplacement
