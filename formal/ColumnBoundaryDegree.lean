import ColumnCutOutgoing
import FrontierDegreesGeneral

/-!
# Degree compatibility for concrete column-cut replacement

The existing column-cut isomorphism transports neighbor cardinalities from
the physical selected graph. The existing suffix-mask theorem and canonical
glue degree sum then show that equal outgoing masks determine equal prefix
boundary degrees in degree-two selected graphs, even at different lengths.

This module adds no transition, connectivity, Hamiltonian, or counting claim.
-/

namespace TriangularCylinder.ColumnCut

open SimpleGraph BoundaryState

theorem glue_parts_neighbor_ncard {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (x : CutVertex m j k) :
    ((CylinderFrontier.glue (prefixPart j k H) (suffixPart j k H)).neighborSet x).ncard =
      (H.neighborSet (vertexEquiv m j k x)).ncard := by
  exact congrArg ENat.toNat (Set.encard_congr ((glueIso hm hH).mapNeighborSet x))

theorem prefixPart_interior_neighbor_ncard {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (x : Vertex m j) :
    ((prefixPart j k H).neighborSet (Sum.inl x)).ncard =
      (H.neighborSet (prefixVertex j k (Sum.inl x))).ncard := by
  rw [← CylinderFrontier.glue_prefix_neighbor_ncard (prefixPart j k H) (suffixPart j k H)]
  exact glue_parts_neighbor_ncard hm hH (Sum.inl x)

theorem suffixPart_interior_neighbor_ncard {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (x : Vertex m k) :
    ((suffixPart j k H).neighborSet (Sum.inl x)).ncard =
      (H.neighborSet (suffixVertex j k (Sum.inl x))).ncard := by
  rw [← CylinderFrontier.glue_suffix_neighbor_ncard (prefixPart j k H) (suffixPart j k H)]
  exact glue_parts_neighbor_ncard hm hH (Sum.inr (Sum.inr x))

theorem parts_boundary_neighbor_ncard_sum {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) (r : Fin m) :
    ((prefixPart j k H).neighborSet (Sum.inr r)).ncard +
      ((suffixPart j k H).neighborSet (Sum.inr r)).ncard =
      (H.neighborSet (r, boundaryCol j k)).ncard := by
  rw [← CylinderFrontier.glue_boundary_neighbor_ncard_of_suffix_no_boundary
    (prefixPart j k H) (suffixPart j k H) (suffixPart_no_boundary_edges H) r]
  exact glue_parts_neighbor_ncard hm hH (Sum.inr (Sum.inl r))

/-- Equal physical outgoing masks determine equal prefix boundary degrees in
two degree-two selected spanning graphs, without a connectivity assumption. -/
theorem prefixPart_boundary_neighbor_ncard_eq_of_masks_eq
    {m j k j' k' : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (hk' : 1 ≤ k')
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    {H' : SimpleGraph (Vertex m (j' + 1 + k'))}
    (hH : H ≤ graph m (j + 1 + k) hm) (hH' : H' ≤ graph m (j' + 1 + k') hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hdeg' : ∀ v, (H'.neighborSet v).ncard = 2)
    (hhor : (stateAt hm hk H).horizontal = (stateAt hm hk' H').horizontal)
    (hdiag : (stateAt hm hk H).diagonal = (stateAt hm hk' H').diagonal)
    (r : Fin m) :
    ((prefixPart j k H).neighborSet (Sum.inr r)).ncard =
      ((prefixPart j' k' H').neighborSet (Sum.inr r)).ncard := by
  have hsum := parts_boundary_neighbor_ncard_sum hm hH r
  have hsum' := parts_boundary_neighbor_ncard_sum hm hH' r
  rw [hdeg] at hsum
  rw [hdeg'] at hsum'
  have hout := suffixPart_boundary_neighbor_ncard_eq_of_masks_eq hm hk hk' hH hH' hhor hdiag r
  omega

/-- A prefix and suffix from different complete degree-two selections still
give degree two when their physical outgoing masks agree. -/
theorem mixed_parts_neighbor_ncard_two
    {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hdegH : ∀ v, (H.neighborSet v).ncard = 2)
    (hdegK : ∀ v, (K.neighborSet v).ncard = 2)
    (hhor : (stateAt hm hOldSuffix H).horizontal = (stateAt hm hk K).horizontal)
    (hdiag : (stateAt hm hOldSuffix H).diagonal = (stateAt hm hk K).diagonal) :
    ∀ v, ((CylinderFrontier.glue (prefixPart j oldSuffix H)
      (suffixPart oldPrefix k K)).neighborSet v).ncard = 2 := by
  apply CylinderFrontier.glue_neighbor_ncard_two_of_suffix_no_boundary
    (prefixPart j oldSuffix H) (suffixPart oldPrefix k K) (suffixPart_no_boundary_edges K)
  · intro x
    rw [prefixPart_interior_neighbor_ncard hm hH x, hdegH]
  · intro x
    rw [suffixPart_interior_neighbor_ncard hm hK x, hdegK]
  · intro r
    rw [prefixPart_boundary_neighbor_ncard_eq_of_masks_eq hm hOldSuffix hk
      hH hK hdegH hdegK hhor hdiag r,
      parts_boundary_neighbor_ncard_sum hm hK r, hdegK]

#print axioms glue_parts_neighbor_ncard
#print axioms prefixPart_interior_neighbor_ncard
#print axioms suffixPart_interior_neighbor_ncard
#print axioms parts_boundary_neighbor_ncard_sum
#print axioms prefixPart_boundary_neighbor_ncard_eq_of_masks_eq
#print axioms mixed_parts_neighbor_ncard_two

end TriangularCylinder.ColumnCut
