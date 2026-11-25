import EdgeReplacementReachability

/-!
# Restricting an edge replacement along an injective old-vertex map

The entire gadget is retained while the old graph is pulled back along an
injective map. When the removed endpoints lie in that map, the restricted
replacement is exactly the replacement of the restricted old graph. Thus the
frozen generic reachability theorem applies directly inside this restriction.

No finiteness, degree, cylinder, or Hamiltonian assumptions are made.
-/

namespace CylinderFrontier.EdgeReplacement

variable {V W N : Type*}

/-- Restricting the old vertices commutes with edge replacement when the vertex
map is injective and both removed endpoints are in its image. -/
theorem comap_replacementGraph (G : SimpleGraph V) (A : SimpleGraph N)
    (f : W → V) (hf : Function.Injective f) (x y : W) (a b : N) :
    (replacementGraph G A (f x) (f y) a b).comap (Sum.map id f) =
      replacementGraph (G.comap f) A x y a b := by
  ext u v
  cases u <;> cases v <;>
    simp [SimpleGraph.comap_adj, replacementGraph, hf.eq_iff]

/-- In the restricted replacement, old-vertex reachability is exactly
reachability in the restricted old graph. -/
theorem restricted_old_reachable_iff (G : SimpleGraph V) (A : SimpleGraph N)
    (f : W → V) (hf : Function.Injective f) {x y : W}
    (hxy : (G.comap f).Adj x y) (hA : A.Connected) (a b : N) (v w : W) :
    ((replacementGraph G A (f x) (f y) a b).comap (Sum.map id f)).Reachable
        (Sum.inr v) (Sum.inr w) ↔
      (G.comap f).Reachable v w := by
  rw [comap_replacementGraph G A f hf x y a b]
  exact old_reachable_iff (G.comap f) A hxy hA a b v w

#print axioms comap_replacementGraph
#print axioms restricted_old_reachable_iff

end CylinderFrontier.EdgeReplacement
