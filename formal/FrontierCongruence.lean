import FrontierSubstitution

/-!
# Suffix reachability congruence and canonical boundary compression

Replacing an attached prefix by another with the same boundary reachability
preserves every reachability query between suffix vertices. In particular, an
attached prefix may be replaced by a graph with empty interior whose boundary
edges join exactly the distinct originally reachable boundary vertices.

The compressed edges represent reachability only. They are not selected
physical edges, and no degree, cycle, or Hamiltonicity property is asserted.
-/

namespace CylinderFrontier

variable {I I' B O : Type*}

/-- Equal boundary relations preserve every suffix-to-suffix reachability query,
without any connectedness assumption on either glued graph. -/
theorem glue_suffix_reachable_iff
    {P : SimpleGraph (I ⊕ B)} {P' : SimpleGraph (I' ⊕ B)}
    (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P) (hP' : TouchesBoundary P')
    (hBoundary : ∀ b c : B, P.Reachable (Sum.inr b) (Sum.inr c) ↔
      P'.Reachable (Sum.inr b) (Sum.inr c)) (x y : O ⊕ B) :
    (glue P Q).Reachable (suffixEmbedding I B O x) (suffixEmbedding I B O y) ↔
      (glue P' Q).Reachable (suffixEmbedding I' B O x) (suffixEmbedding I' B O y) := by
  constructor
  · intro hxy
    simpa only [replacement_suffix] using
      replacement_reachable Q hP (fun b c => (hBoundary b c).mp) hxy
  · intro hxy
    simpa only [replacement_suffix] using
      replacement_reachable Q hP' (fun b c => (hBoundary b c).mpr) hxy

/-- The canonical graph recording only the prefix boundary relation.
Its edges are virtual reachability edges, not physical prefix edges. -/
def boundaryGraph (P : SimpleGraph (I ⊕ B)) : SimpleGraph B :=
  SimpleGraph.fromRel (fun b c => P.Reachable (Sum.inr b) (Sum.inr c))

@[simp] theorem boundaryGraph_adj (P : SimpleGraph (I ⊕ B)) (b c : B) :
    (boundaryGraph P).Adj b c ↔ b ≠ c ∧ P.Reachable (Sum.inr b) (Sum.inr c) := by
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.symm⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- Compression preserves the complete boundary reachability relation, including
reflexive reachability. No attachment hypothesis is needed for this identity. -/
@[simp] theorem boundaryGraph_reachable (P : SimpleGraph (I ⊕ B)) (b c : B) :
    (boundaryGraph P).Reachable b c ↔ P.Reachable (Sum.inr b) (Sum.inr c) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact ((boundaryGraph_adj P _ _).mp h).2.trans ih
  · intro h
    by_cases hbc : b = c
    · subst c
      exact SimpleGraph.Reachable.refl _
    · exact ((boundaryGraph_adj P b c).mpr ⟨hbc, h⟩).reachable

/-- Put the virtual boundary graph into the existing prefix interface with an
empty interior, using the canonical empty-sum equivalence. -/
def compressedPrefix (P : SimpleGraph (I ⊕ B)) : SimpleGraph (Empty ⊕ B) :=
  (boundaryGraph P).comap (Equiv.emptySum Empty B)

@[simp] theorem compressedPrefix_reachable (P : SimpleGraph (I ⊕ B)) (b c : B) :
    (compressedPrefix P).Reachable (Sum.inr b) (Sum.inr c) ↔
      P.Reachable (Sum.inr b) (Sum.inr c) := by
  have h := SimpleGraph.Iso.reachable_iff
    (φ := SimpleGraph.Iso.comap (Equiv.emptySum Empty B) (boundaryGraph P))
    (u := Sum.inr b) (v := Sum.inr c)
  exact h.symm.trans (boundaryGraph_reachable P b c)

/-- The empty compressed interior has no component requiring an anchor. -/
theorem touchesBoundary_compressedPrefix (P : SimpleGraph (I ⊕ B)) :
    TouchesBoundary (compressedPrefix P) := by
  intro i
  exact Empty.elim i

/-- Canonical boundary compression can replace an attached prefix for all
suffix reachability queries under the same physical suffix graph. -/
theorem glue_suffix_reachable_iff_compressedPrefix
    (P : SimpleGraph (I ⊕ B)) (Q : SimpleGraph (O ⊕ B)) (hP : TouchesBoundary P)
    (x y : O ⊕ B) :
    (glue P Q).Reachable (suffixEmbedding I B O x) (suffixEmbedding I B O y) ↔
      (glue (compressedPrefix P) Q).Reachable
        (suffixEmbedding Empty B O x) (suffixEmbedding Empty B O y) :=
  glue_suffix_reachable_iff Q hP (touchesBoundary_compressedPrefix P)
    (fun b c => (compressedPrefix_reachable P b c).symm) x y

#print axioms glue_suffix_reachable_iff
#print axioms boundaryGraph_adj
#print axioms boundaryGraph_reachable
#print axioms compressedPrefix_reachable
#print axioms touchesBoundary_compressedPrefix
#print axioms glue_suffix_reachable_iff_compressedPrefix

end CylinderFrontier
