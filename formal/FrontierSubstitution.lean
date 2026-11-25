import Mathlib.Combinatorics.SimpleGraph.Path

/-!
# Connectivity under replacement of a prefix graph

The prefix and suffix are embedded in `I ⊕ (B ⊕ O)` by their canonical
inclusions. Their images intersect exactly at the distinct boundary vertices
`B`. No assumption is made about the suffix components, graph finiteness,
degrees, Hamiltonian walks, or geometric topology.

This module proves a connectivity replacement theorem, not a cylinder
frontier encoding or a transfer/counting bijection.
-/

namespace CylinderFrontier

variable {I I' B O : Type*}

/-- Include the prefix interior and the shared boundary. -/
def prefixEmbedding (I B O : Type*) : (I ⊕ B) ↪ I ⊕ (B ⊕ O) where
  toFun
    | Sum.inl i => Sum.inl i
    | Sum.inr b => Sum.inr (Sum.inl b)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- Include the suffix interior and the same shared boundary. -/
def suffixEmbedding (I B O : Type*) : (O ⊕ B) ↪ I ⊕ (B ⊕ O) where
  toFun
    | Sum.inl o => Sum.inr (Sum.inr o)
    | Sum.inr b => Sum.inr (Sum.inl b)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- Glue two simple graphs along the boundary, without identifying distinct stubs. -/
def glue (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) :
    SimpleGraph (I ⊕ (B ⊕ O)) :=
  P.map (prefixEmbedding I B O) ⊔ Q.map (suffixEmbedding I B O)

/-- The prefix inclusion is a graph homomorphism into the glued graph. -/
def prefixHom (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) :
    SimpleGraph.Hom P (glue P Q) where
  toFun := prefixEmbedding I B O
  map_rel' := by
    intro x y h
    exact Or.inl ⟨x, y, h, rfl, rfl⟩

/-- The suffix inclusion is a graph homomorphism into the glued graph. -/
def suffixHom (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) :
    SimpleGraph.Hom Q (glue P Q) where
  toFun := suffixEmbedding I B O
  map_rel' := by
    intro x y h
    exact Or.inr ⟨x, y, h, rfl, rfl⟩

/-- Every prefix interior vertex belongs to a component meeting the boundary. -/
def TouchesBoundary (P : SimpleGraph (I ⊕ B)) : Prop :=
  ∀ i : I, ∃ b : B, P.Reachable (Sum.inl i) (Sum.inr b)

/-- Choose a reachable boundary anchor, fixing boundary vertices themselves. -/
noncomputable def anchor {P : SimpleGraph (I ⊕ B)} (hP : TouchesBoundary P) :
    I ⊕ B → B
  | Sum.inl i => Classical.choose (hP i)
  | Sum.inr b => b

theorem reachable_anchor {P : SimpleGraph (I ⊕ B)} (hP : TouchesBoundary P)
    (x : I ⊕ B) : P.Reachable x (Sum.inr (anchor hP x)) := by
  cases x with
  | inl i => exact Classical.choose_spec (hP i)
  | inr b => exact SimpleGraph.Reachable.refl _

/-- Replace an old interior vertex by its boundary anchor; fix the entire suffix. -/
noncomputable def replacement {P : SimpleGraph (I ⊕ B)} (hP : TouchesBoundary P) :
    I ⊕ (B ⊕ O) → I' ⊕ (B ⊕ O)
  | Sum.inl i => Sum.inr (Sum.inl (Classical.choose (hP i)))
  | Sum.inr s => Sum.inr s

@[simp] theorem replacement_prefix {P : SimpleGraph (I ⊕ B)}
    (hP : TouchesBoundary P) (x : I ⊕ B) :
    replacement (I' := I') hP (prefixEmbedding I B O x) =
      prefixEmbedding I' B O (Sum.inr (anchor hP x)) := by
  cases x <;> rfl

@[simp] theorem replacement_suffix {P : SimpleGraph (I ⊕ B)}
    (hP : TouchesBoundary P) (x : O ⊕ B) :
    replacement (I' := I') hP (suffixEmbedding I B O x) =
      suffixEmbedding I' B O x := by
  cases x <;> rfl

theorem replacement_adj_reachable
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P)
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) →
      P'.Reachable (Sum.inr b) (Sum.inr c))
    {x y : I ⊕ (B ⊕ O)} (hxy : (glue P Q).Adj x y) :
    (glue P' Q).Reachable (replacement hP x) (replacement hP y) := by
  rcases hxy with hp | hq
  · rcases hp with ⟨u, v, huv, rfl, rfl⟩
    have hbound : P.Reachable (Sum.inr (anchor hP u)) (Sum.inr (anchor hP v)) :=
      (reachable_anchor hP u).symm.trans (huv.reachable.trans (reachable_anchor hP v))
    have hnew := (hBoundary _ _ hbound).map (prefixHom P' Q)
    simpa only [replacement_prefix] using hnew
  · rcases hq with ⟨u, v, huv, rfl, rfl⟩
    have hnew := huv.reachable.map (suffixHom P' Q)
    simpa only [replacement_suffix] using hnew

theorem replacement_reachable
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P)
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) →
      P'.Reachable (Sum.inr b) (Sum.inr c))
    {x y : I ⊕ (B ⊕ O)} (hxy : (glue P Q).Reachable x y) :
    (glue P' Q).Reachable (replacement hP x) (replacement hP y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy ⊢
  exact Relation.ReflTransGen.lift' (replacement (I' := I') hP)
    (fun u v huv => (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (replacement_adj_reachable Q hP hBoundary huv)) hxy

/-- Every vertex in the new glued graph reaches an image of the replacement map. -/
theorem reachable_replacement_image
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P) (hP' : TouchesBoundary P')
    (x' : I' ⊕ (B ⊕ O)) :
    ∃ x : I ⊕ (B ⊕ O), (glue P' Q).Reachable x' (replacement hP x) := by
  cases x' with
  | inl i =>
      obtain ⟨b, hb⟩ := hP' i
      refine ⟨Sum.inr (Sum.inl b), ?_⟩
      exact hb.map (prefixHom P' Q)
  | inr s => exact ⟨Sum.inr s, SimpleGraph.Reachable.refl _⟩

/-- Increasing boundary reachability preserves preconnectedness after replacement. -/
theorem glue_preconnected_of_boundary_imp
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P) (hP' : TouchesBoundary P')
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) →
      P'.Reachable (Sum.inr b) (Sum.inr c))
    (hconn : (glue P Q).Preconnected) : (glue P' Q).Preconnected := by
  intro x' y'
  obtain ⟨x, hx⟩ := reachable_replacement_image Q hP hP' x'
  obtain ⟨y, hy⟩ := reachable_replacement_image Q hP hP' y'
  exact hx.trans ((replacement_reachable Q hP hBoundary (hconn x y)).trans hy.symm)

/-- Boundary reachability equality suffices for global preconnectedness equivalence.

No nonemptiness or suffix-attachment hypothesis is needed.
-/
theorem glue_preconnected_iff
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P) (hP' : TouchesBoundary P')
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) ↔
      P'.Reachable (Sum.inr b) (Sum.inr c)) :
    (glue P Q).Preconnected ↔ (glue P' Q).Preconnected := by
  constructor
  · exact glue_preconnected_of_boundary_imp Q hP hP' (fun b c => (hBoundary b c).mp)
  · exact glue_preconnected_of_boundary_imp Q hP' hP (fun b c => (hBoundary b c).mpr)

/-- Connectedness transfers too, with nonemptiness derived from the replacement map. -/
theorem glue_connected_of_boundary_imp
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P) (hP' : TouchesBoundary P')
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) →
      P'.Reachable (Sum.inr b) (Sum.inr c))
    (hconn : (glue P Q).Connected) : (glue P' Q).Connected where
  preconnected := glue_preconnected_of_boundary_imp Q hP hP' hBoundary hconn.preconnected
  nonempty := hconn.nonempty.map (replacement (I' := I') hP)

/-- Replace a prefix by any attached prefix with the same boundary connectivity. -/
theorem glue_connected_iff
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P) (hP' : TouchesBoundary P')
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) ↔
      P'.Reachable (Sum.inr b) (Sum.inr c)) :
    (glue P Q).Connected ↔ (glue P' Q).Connected := by
  constructor
  · exact glue_connected_of_boundary_imp Q hP hP' (fun b c => (hBoundary b c).mp)
  · exact glue_connected_of_boundary_imp Q hP' hP (fun b c => (hBoundary b c).mpr)

#print axioms glue_preconnected_iff
#print axioms glue_connected_iff

end CylinderFrontier
