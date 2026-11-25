import FrontierSubstitution

/-!
# Boundary attachment forced by connectivity

Every glued walk that starts in the prefix interior either remains reachable
there using prefix edges or has already met the shared boundary using prefix
edges. Consequently a connected completion forces boundary attachment whenever
there is any boundary or suffix vertex. No finiteness, degree, Hamiltonicity,
or supplied attachment premise is used.
-/

namespace CylinderFrontier

variable {I B O : Type*}

/-- Along a glued walk, a prefix-reachable interior starting point either
reaches the shared boundary or stays prefix-reachable in the interior. -/
theorem boundary_or_interior_of_walk
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    {i : I} {x y : I ⊕ (B ⊕ O)} (p : (glue P Q).Walk x y) :
    (∃ j : I, x = Sum.inl j ∧ P.Reachable (Sum.inl i) (Sum.inl j)) →
      (∃ b : B, P.Reachable (Sum.inl i) (Sum.inr b)) ∨
        ∃ j : I, y = Sum.inl j ∧ P.Reachable (Sum.inl i) (Sum.inl j) := by
  induction p with
  | nil =>
    intro hx
    exact Or.inr hx
  | cons h p ih =>
    rintro ⟨j, rfl, hij⟩
    rcases h with hp | hq
    · rcases hp with ⟨u, v, huv, hu, rfl⟩
      cases u with
      | inl k =>
        have hkj : k = j := Sum.inl.inj hu
        subst k
        cases v with
        | inl k => exact ih ⟨k, rfl, hij.trans huv.reachable⟩
        | inr b => exact Or.inl ⟨b, hij.trans huv.reachable⟩
      | inr b => simp [prefixEmbedding] at hu
    · rcases hq with ⟨u, v, huv, hu, hv⟩
      cases u <;> simp [suffixEmbedding] at hu

/-- Reaching any vertex outside the prefix interior requires a prefix path
from the starting interior vertex to some shared boundary vertex. -/
theorem boundary_reachable_of_glue_reachable
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    {i : I} {z : B ⊕ O}
    (h : (glue P Q).Reachable (Sum.inl i) (Sum.inr z)) :
    ∃ b : B, P.Reachable (Sum.inl i) (Sum.inr b) := by
  obtain ⟨p⟩ := h
  rcases boundary_or_interior_of_walk P Q p
      ⟨i, rfl, SimpleGraph.Reachable.refl _⟩ with hb | ⟨j, hj, _⟩
  · exact hb
  · cases hj

/-- Preconnectedness already forces prefix attachment if there is a vertex
outside the prefix interior. -/
theorem touchesBoundary_of_glue_preconnected
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hconn : (glue P Q).Preconnected) (hside : Nonempty (B ⊕ O)) :
    TouchesBoundary P := by
  obtain ⟨z⟩ := hside
  intro i
  exact boundary_reachable_of_glue_reachable P Q (hconn (Sum.inl i) (Sum.inr z))

/-- A connected completion supplies the attachment hypothesis required by
the prefix-substitution theorem. -/
theorem touchesBoundary_of_glue_connected
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hconn : (glue P Q).Connected) (hside : Nonempty (B ⊕ O)) :
    TouchesBoundary P :=
  touchesBoundary_of_glue_preconnected P Q hconn.preconnected hside

theorem touchesBoundary_of_glue_connected_of_nonempty_boundary
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hconn : (glue P Q).Connected) (hB : Nonempty B) :
    TouchesBoundary P :=
  touchesBoundary_of_glue_connected P Q hconn (hB.map Sum.inl)

/-- Exchange the two interiors while fixing every distinct boundary vertex. -/
def swapGlueVertex : I ⊕ (B ⊕ O) → O ⊕ (B ⊕ I)
  | Sum.inl i => Sum.inr (Sum.inr i)
  | Sum.inr (Sum.inl b) => Sum.inr (Sum.inl b)
  | Sum.inr (Sum.inr o) => Sum.inl o

@[simp] theorem swapGlueVertex_prefix (x : I ⊕ B) :
    swapGlueVertex (prefixEmbedding I B O x) = suffixEmbedding O B I x := by
  cases x <;> rfl

@[simp] theorem swapGlueVertex_suffix (x : O ⊕ B) :
    swapGlueVertex (suffixEmbedding I B O x) = prefixEmbedding O B I x := by
  cases x <;> rfl

theorem swapGlueVertex_surjective :
    Function.Surjective (swapGlueVertex : I ⊕ (B ⊕ O) → O ⊕ (B ⊕ I)) := by
  intro x
  cases x with
  | inl o => exact ⟨Sum.inr (Sum.inr o), rfl⟩
  | inr s =>
    cases s with
    | inl b => exact ⟨Sum.inr (Sum.inl b), rfl⟩
    | inr i => exact ⟨Sum.inl i, rfl⟩

/-- Swapping the interiors exchanges the prefix and suffix glued graphs. -/
def swapGlueHom (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) :
    SimpleGraph.Hom (glue P Q) (glue Q P) where
  toFun := swapGlueVertex
  map_rel' := by
    intro x y h
    rcases h with hp | hq
    · rcases hp with ⟨u, v, huv, rfl, rfl⟩
      exact Or.inr ⟨u, v, huv, (swapGlueVertex_prefix u).symm,
        (swapGlueVertex_prefix v).symm⟩
    · rcases hq with ⟨u, v, huv, rfl, rfl⟩
      exact Or.inl ⟨u, v, huv, (swapGlueVertex_suffix u).symm,
        (swapGlueVertex_suffix v).symm⟩

theorem glue_connected_swap
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hconn : (glue P Q).Connected) : (glue Q P).Connected :=
  hconn.map (swapGlueHom P Q) swapGlueVertex_surjective

/-- The symmetric suffix attachment result needs a vertex outside the suffix
interior, and no prefix attachment premise. -/
theorem suffix_touchesBoundary_of_glue_connected
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hconn : (glue P Q).Connected) (hside : Nonempty (B ⊕ I)) :
    TouchesBoundary Q :=
  touchesBoundary_of_glue_connected Q P (glue_connected_swap P Q hconn) hside

/-- With a nonempty shared boundary, both interiors attach in their own
graphs whenever the glued graph is connected. -/
theorem both_touchBoundary_of_glue_connected
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hconn : (glue P Q).Connected) (hB : Nonempty B) :
    TouchesBoundary P ∧ TouchesBoundary Q :=
  ⟨touchesBoundary_of_glue_connected_of_nonempty_boundary P Q hconn hB,
    suffix_touchesBoundary_of_glue_connected P Q hconn (hB.map Sum.inl)⟩

#print axioms boundary_reachable_of_glue_reachable
#print axioms touchesBoundary_of_glue_preconnected
#print axioms touchesBoundary_of_glue_connected
#print axioms touchesBoundary_of_glue_connected_of_nonempty_boundary
#print axioms glue_connected_swap
#print axioms suffix_touchesBoundary_of_glue_connected
#print axioms both_touchBoundary_of_glue_connected

end CylinderFrontier
