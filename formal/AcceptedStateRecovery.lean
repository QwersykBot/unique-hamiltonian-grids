import AcceptedGraph
import AcceptedExtensionality
import ProcessedPrefix

/-!
# Recovering the recorded boundary relation

The initial physical column determines its boundary relation. Each later
column updates that relation from the old H/D masks and the new V mask.
Consequently a connected reconstructed graph has exactly the relation
recorded at every accepted cut. Connectedness is an explicit premise here;
its derivation from the accepted data belongs to the realization argument.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph TriangularEdgeEncoding BoundaryState ColumnCut ProcessedPrefix

/-- The selected graph of any actual ambient walk uses only ambient edges. -/
theorem selectedCycleGraph_le {m L : ℕ} (hm : 3 ≤ m)
    {v : Vertex m L} (C : (graph m L hm).Walk v v) :
    fromEdgeSet C.edgeSet ≤ graph m L hm := by
  rw [← CountedHamiltonian.coe_selectedEdges C]
  exact CountedHamiltonian.selectedGraph_le
    (fun _ he => C.edges_subset_edgeSet (List.mem_toFinset.mp he))

/-- Equal first-column V masks give equal first-cut reachability at any widths. -/
theorem cutState_initial_reach_eq {m n n' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (n + 2))} {K : SimpleGraph (Vertex m (n' + 2))}
    (hH : H ≤ graph m (n + 2) hm) (hK : K ≤ graph m (n' + 2) hm)
    (hV : verticalMask hm H 0 = verticalMask hm K 0) :
    (cutState hm H 0).reach = (cutState hm K 0).reach := by
  have hV' : verticalMask hm (cutGraph H 0) (boundaryCol 0 (cutTail (0 : Fin (n + 1)))) =
      verticalMask hm (cutGraph K 0) (boundaryCol 0 (cutTail (0 : Fin (n' + 1)))) := by
    funext r
    rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
    have h := congrFun hV r
    rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff] at h
    exact h
  exact ColumnStep.firstState_reach_eq_of_verticalMask_eq hm
    (cutTail_pos (0 : Fin (n + 1))) (cutTail_pos (0 : Fin (n' + 1)))
    (cutGraph_le hm hH 0) (cutGraph_le hm hK 0) hV'

/-- The initial recorded relation is exactly that of the reconstructed first column. -/
theorem acceptedGraph_initial_reach {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    (cutState hm (acceptedGraph w) 0).reach = (acceptedCutStates w 0).val.reach := by
  obtain ⟨n', v, C, hC, hstate, hV⟩ := accepted_initial_realized w
  have hnewV : verticalMask hm (acceptedGraph w) 0 =
      verticalMask hm (fromEdgeSet C.edgeSet) 0 := by
    rw [acceptedGraph_vertical]
    exact hV.symm
  exact (cutState_initial_reach_eq hm (acceptedGraph_le w) (selectedCycleGraph_le hm C) hnewV).trans
    (congrArg RawBoundaryState.reach hstate)

/-- Once reconstructed connectedness is established, every recorded reachability
matrix is forced by the actual physical graph, with no global witness chosen. -/
theorem acceptedGraph_reach {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (hconn : (acceptedGraph w).Connected)
    (c : Fin (n + 1)) :
    (cutState hm (acceptedGraph w) c).reach = (acceptedCutStates w c).val.reach := by
  refine Fin.induction (acceptedGraph_initial_reach w) ?_ c
  intro i ih
  obtain ⟨n', i', v, C, hC, hsource, htarget, hV⟩ := accepted_local_realized w i
  have hconnC : (fromEdgeSet C.edgeSet).Connected := by
    simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_connected hC
  have hHor : (cutState hm (acceptedGraph w) i.castSucc).horizontal =
      (cutState hm (fromEdgeSet C.edgeSet) i'.castSucc).horizontal :=
    (acceptedGraph_horizontal w i.castSucc).trans
      (congrArg RawBoundaryState.horizontal hsource).symm
  have hDiag : (cutState hm (acceptedGraph w) i.castSucc).diagonal =
      (cutState hm (fromEdgeSet C.edgeSet) i'.castSucc).diagonal :=
    (acceptedGraph_diagonal w i.castSucc).trans
      (congrArg RawBoundaryState.diagonal hsource).symm
  have hReach : (cutState hm (acceptedGraph w) i.castSucc).reach =
      (cutState hm (fromEdgeSet C.edgeSet) i'.castSucc).reach :=
    ih.trans (congrArg RawBoundaryState.reach hsource).symm
  have hnewV : verticalMask hm (acceptedGraph w) i.succ.castSucc =
      verticalMask hm (fromEdgeSet C.edgeSet) i'.succ.castSucc := by
    rw [acceptedGraph_vertical]
    exact hV.symm
  exact (cutState_next_reach_eq hm (acceptedGraph_le w) (selectedCycleGraph_le hm C)
    hconn hconnC i i' hHor hDiag hReach hnewV).trans
      (congrArg RawBoundaryState.reach htarget)

end TriangularCylinder.Transfer
