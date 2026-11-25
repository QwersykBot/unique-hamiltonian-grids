import FrontierDegrees

/-!
# Neighbor counts when one piece owns boundary edges

The canonical glue preserves the two interior neighbor sets. At a shared
boundary vertex its neighbor set is the union of the two embedded piece
neighbor sets. These images are disjoint precisely when no boundary edge
incident to that vertex belongs to both pieces.

The results below allow either piece to contain boundary-to-boundary edges,
provided no such edge is shared. In particular, the prefix may own all
boundary edges while the suffix has none. Boundary degrees need only sum to
two; they need not be one on each side.

This module proves degree statements only. It adds no connectivity,
Hamiltonian-walk, selected-edge characterization, or counting theorem.
-/

namespace CylinderFrontier

variable {I B O : Type*}

private theorem glue_general_neighborSet_boundary
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

private theorem glue_general_boundary_neighbor_images_disjoint
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hBB : ∀ b c : B,
      ¬ (P.Adj (Sum.inr b) (Sum.inr c) ∧ Q.Adj (Sum.inr b) (Sum.inr c)))
    (b : B) :
    Disjoint ((prefixEmbedding I B O) '' P.neighborSet (Sum.inr b))
      ((suffixEmbedding I B O) '' Q.neighborSet (Sum.inr b)) := by
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
  have huv : prefixEmbedding I B O u = suffixEmbedding I B O v := hu'.trans hv'.symm
  cases u with
  | inl i => cases v <;> simp [prefixEmbedding, suffixEmbedding] at huv
  | inr c =>
      cases v with
      | inl o => simp [prefixEmbedding, suffixEmbedding] at huv
      | inr d =>
          have hcd : c = d := by simpa [prefixEmbedding, suffixEmbedding] using huv
          subst d
          exact hBB b c ⟨hu, hv⟩

/-- Boundary neighbor counts add when the pieces share no boundary edge. -/
theorem glue_boundary_neighbor_ncard_of_no_shared_boundary
    [Finite I] [Finite B] [Finite O]
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hBB : ∀ b c : B,
      ¬ (P.Adj (Sum.inr b) (Sum.inr c) ∧ Q.Adj (Sum.inr b) (Sum.inr c)))
    (b : B) :
    ((glue P Q).neighborSet (Sum.inr (Sum.inl b))).ncard =
      (P.neighborSet (Sum.inr b)).ncard + (Q.neighborSet (Sum.inr b)).ncard := by
  rw [glue_general_neighborSet_boundary,
    Set.ncard_union_eq (glue_general_boundary_neighbor_images_disjoint P Q hBB b)]
  simp only [Set.ncard_map]

/-- The prefix may own arbitrary boundary edges when the suffix has none. -/
theorem glue_boundary_neighbor_ncard_of_suffix_no_boundary
    [Finite I] [Finite B] [Finite O]
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hQBB : ∀ b c : B, ¬ Q.Adj (Sum.inr b) (Sum.inr c)) (b : B) :
    ((glue P Q).neighborSet (Sum.inr (Sum.inl b))).ncard =
      (P.neighborSet (Sum.inr b)).ncard + (Q.neighborSet (Sum.inr b)).ncard := by
  exact glue_boundary_neighbor_ncard_of_no_shared_boundary P Q
    (fun b c h => hQBB b c h.2) b

/-- Interior counts two and boundary sums two give degree two in the canonical glue. -/
theorem glue_neighbor_ncard_two_of_no_shared_boundary
    [Finite I] [Finite B] [Finite O]
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hBB : ∀ b c : B,
      ¬ (P.Adj (Sum.inr b) (Sum.inr c) ∧ Q.Adj (Sum.inr b) (Sum.inr c)))
    (hPI : ∀ i : I, (P.neighborSet (Sum.inl i)).ncard = 2)
    (hQI : ∀ o : O, (Q.neighborSet (Sum.inl o)).ncard = 2)
    (hB : ∀ b : B,
      (P.neighborSet (Sum.inr b)).ncard + (Q.neighborSet (Sum.inr b)).ncard = 2) :
    ∀ v, ((glue P Q).neighborSet v).ncard = 2 := by
  intro v
  rcases v with i | b | o
  · rw [glue_prefix_neighbor_ncard, hPI]
  · rw [glue_boundary_neighbor_ncard_of_no_shared_boundary P Q hBB, hB]
  · rw [glue_suffix_neighbor_ncard, hQI]

/-- Degree two with boundary edges assigned to the prefix and excluded from the suffix. -/
theorem glue_neighbor_ncard_two_of_suffix_no_boundary
    [Finite I] [Finite B] [Finite O]
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B))
    (hQBB : ∀ b c : B, ¬ Q.Adj (Sum.inr b) (Sum.inr c))
    (hPI : ∀ i : I, (P.neighborSet (Sum.inl i)).ncard = 2)
    (hQI : ∀ o : O, (Q.neighborSet (Sum.inl o)).ncard = 2)
    (hB : ∀ b : B,
      (P.neighborSet (Sum.inr b)).ncard + (Q.neighborSet (Sum.inr b)).ncard = 2) :
    ∀ v, ((glue P Q).neighborSet v).ncard = 2 := by
  exact glue_neighbor_ncard_two_of_no_shared_boundary P Q
    (fun b c h => hQBB b c h.2) hPI hQI hB

#print axioms glue_boundary_neighbor_ncard_of_no_shared_boundary
#print axioms glue_boundary_neighbor_ncard_of_suffix_no_boundary
#print axioms glue_neighbor_ncard_two_of_no_shared_boundary
#print axioms glue_neighbor_ncard_two_of_suffix_no_boundary

end CylinderFrontier
