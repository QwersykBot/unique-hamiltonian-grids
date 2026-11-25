import FrontierSubstitution
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Card

/-!
# Neighbor counts in the canonical frontier glue

This module uses the canonical embeddings and `glue` from the frozen
`FrontierSubstitution` module. Interior neighbor sets are injective images of
the corresponding piece's neighbor sets. At a boundary vertex the two images
are disjoint when neither piece has boundary-to-boundary edges.

Distinct boundary vertices remain distinct, including when several boundary
vertices have the same suffix-interior neighbor. The results concern neighbor
cardinalities only; they assert no connectivity, Hamiltonian-walk, or counting
theorem.
-/

namespace CylinderFrontier

variable {I B O : Type*}

private theorem glue_neighborSet_prefix_interior
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) (i : I) :
    (glue P Q).neighborSet (Sum.inl i) =
      (prefixEmbedding I B O) '' P.neighborSet (Sum.inl i) := by
  ext x
  constructor
  · rintro (hp | hq)
    · rcases hp with ⟨u, v, huv, hu, hv⟩
      have hu' : u = Sum.inl i := (prefixEmbedding I B O).injective hu
      subst u
      exact ⟨v, huv, hv⟩
    · rcases hq with ⟨u, v, huv, hu, hv⟩
      cases u <;> simp [suffixEmbedding] at hu
  · rintro ⟨v, hv, rfl⟩
    exact Or.inl ⟨Sum.inl i, v, hv, rfl, rfl⟩

private theorem glue_neighborSet_suffix_interior
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) (o : O) :
    (glue P Q).neighborSet (Sum.inr (Sum.inr o)) =
      (suffixEmbedding I B O) '' Q.neighborSet (Sum.inl o) := by
  ext x
  constructor
  · rintro (hp | hq)
    · rcases hp with ⟨u, v, huv, hu, hv⟩
      cases u <;> simp [prefixEmbedding] at hu
    · rcases hq with ⟨u, v, huv, hu, hv⟩
      have hu' : u = Sum.inl o := (suffixEmbedding I B O).injective hu
      subst u
      exact ⟨v, huv, hv⟩
  · rintro ⟨v, hv, rfl⟩
    exact Or.inr ⟨Sum.inl o, v, hv, rfl, rfl⟩

private theorem glue_neighborSet_boundary
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) (b : B) :
    (glue P Q).neighborSet (Sum.inr (Sum.inl b)) =
      (prefixEmbedding I B O) '' P.neighborSet (Sum.inr b) ∪
      (suffixEmbedding I B O) '' Q.neighborSet (Sum.inr b) := by
  ext x
  constructor
  · rintro (hp | hq)
    · rcases hp with ⟨u, v, huv, hu, hv⟩
      have hu' : u = Sum.inr b := (prefixEmbedding I B O).injective hu
      subst u
      exact Or.inl ⟨v, huv, hv⟩
    · rcases hq with ⟨u, v, huv, hu, hv⟩
      have hu' : u = Sum.inr b := (suffixEmbedding I B O).injective hu
      subst u
      exact Or.inr ⟨v, huv, hv⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact Or.inl ⟨Sum.inr b, v, hv, rfl, rfl⟩
    · exact Or.inr ⟨Sum.inr b, v, hv, rfl, rfl⟩

private theorem glue_boundary_neighbor_images_disjoint
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hPBB : ∀ b c : B, ¬ P.Adj (Sum.inr b) (Sum.inr c))
    (hQBB : ∀ b c : B, ¬ Q.Adj (Sum.inr b) (Sum.inr c)) (b : B) :
    Disjoint ((prefixEmbedding I B O) '' P.neighborSet (Sum.inr b))
      ((suffixEmbedding I B O) '' Q.neighborSet (Sum.inr b)) := by
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
  have huv : prefixEmbedding I B O u = suffixEmbedding I B O v := hu'.trans hv'.symm
  cases u with
  | inr c => exact hPBB b c hu
  | inl i =>
      cases v with
      | inr c => exact hQBB b c hv
      | inl o => simp [prefixEmbedding, suffixEmbedding] at huv

/-- Gluing preserves the neighbor cardinality of every prefix-interior vertex. -/
theorem glue_prefix_neighbor_ncard
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) (i : I) :
    ((glue P Q).neighborSet (Sum.inl i)).ncard =
      (P.neighborSet (Sum.inl i)).ncard := by
  rw [glue_neighborSet_prefix_interior]
  exact Set.ncard_map (prefixEmbedding I B O)

/-- Gluing preserves the neighbor cardinality of every suffix-interior vertex. -/
theorem glue_suffix_neighbor_ncard
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) (o : O) :
    ((glue P Q).neighborSet (Sum.inr (Sum.inr o))).ncard =
      (Q.neighborSet (Sum.inl o)).ncard := by
  rw [glue_neighborSet_suffix_interior]
  exact Set.ncard_map (suffixEmbedding I B O)

/-- The boundary neighbor cardinalities add when neither piece has boundary edges. -/
theorem glue_boundary_neighbor_ncard [Finite I] [Finite B] [Finite O]
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hPBB : ∀ b c : B, ¬ P.Adj (Sum.inr b) (Sum.inr c))
    (hQBB : ∀ b c : B, ¬ Q.Adj (Sum.inr b) (Sum.inr c)) (b : B) :
    ((glue P Q).neighborSet (Sum.inr (Sum.inl b))).ncard =
      (P.neighborSet (Sum.inr b)).ncard + (Q.neighborSet (Sum.inr b)).ncard := by
  rw [glue_neighborSet_boundary,
    Set.ncard_union_eq (glue_boundary_neighbor_images_disjoint P Q hPBB hQBB b)]
  simp only [Set.ncard_map]

/-- Interior degree two and boundary degree one on each side give degree two after gluing. -/
theorem glue_neighbor_ncard_two [Finite I] [Finite B] [Finite O]
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hPBB : ∀ b c : B, ¬ P.Adj (Sum.inr b) (Sum.inr c))
    (hQBB : ∀ b c : B, ¬ Q.Adj (Sum.inr b) (Sum.inr c))
    (hPI : ∀ i : I, (P.neighborSet (Sum.inl i)).ncard = 2)
    (hQI : ∀ o : O, (Q.neighborSet (Sum.inl o)).ncard = 2)
    (hPB : ∀ b : B, (P.neighborSet (Sum.inr b)).ncard = 1)
    (hQB : ∀ b : B, (Q.neighborSet (Sum.inr b)).ncard = 1) :
    ∀ v, ((glue P Q).neighborSet v).ncard = 2 := by
  intro v
  rcases v with i | b | o
  · rw [glue_prefix_neighbor_ncard, hPI]
  · rw [glue_boundary_neighbor_ncard P Q hPBB hQBB, hPB, hQB]
  · rw [glue_suffix_neighbor_ncard, hQI]

#print axioms glue_prefix_neighbor_ncard
#print axioms glue_suffix_neighbor_ncard
#print axioms glue_boundary_neighbor_ncard
#print axioms glue_neighbor_ncard_two

end CylinderFrontier
