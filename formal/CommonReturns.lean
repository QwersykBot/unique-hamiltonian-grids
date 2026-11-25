import SpliceLeftState
import SpliceAssignedParity
import SpliceStateFields
import SelectedCycleDeletion
import TransferWitnesses
import CycleIntervals

/-!
# Actual returns of lengths two and three at the same common state

Self-splice the concrete parity-zero two-column and three-column witnesses
at their selected before-last-to-last row gap. The old left state survives,
and the old right state survives after shifting because the added parity is
zero. The corresponding intervals of the actual joined Hamiltonian cycles
give local-label paths of lengths two and three at `commonCoreState`.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph BoundaryState SplicePrefixCoordinates
open CylinderFrontier.EdgeReplacement

/-- A splice whose total parity increment is zero preserves the complete
old right state. The cut-open inserted graph is connected, and the old
removed edge is selected; no state equality is assumed. -/
theorem stateAt_eq_of_zero_splice {m a j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (GA : SimpleGraph (Vertex m a))
    {v : Vertex m (j + 1 + k)} {w : Vertex m (a + (j + 1 + k))}
    (B : (graph m (j + 1 + k) hm).Walk v v)
    (J : (graph m (a + (j + 1 + k)) hm).Walk w w)
    (hB : B.IsTrail) (hJ : J.IsTrail)
    (a₀ a₁ : Vertex m a) (r s : Fin m) (hGA : GA.Connected)
    (hxy : (fromEdgeSet B.edgeSet).Adj
      (r, firstCol (j + 1 + k) (by omega)) (s, firstCol (j + 1 + k) (by omega)))
    (hsplice : (fromEdgeSet J.edgeSet).comap (columnSumEquiv m a (j + 1 + k)) =
      replacementGraph (fromEdgeSet B.edgeSet) GA
        (r, firstCol (j + 1 + k) (by omega))
        (s, firstCol (j + 1 + k) (by omega)) a₀ a₁)
    (hparity : typeParity hm J = typeParity hm B) :
    stateAt hm hk ((fromEdgeSet J.edgeSet).comap (fullWidthEquiv m a j k)) =
      stateAt hm hk (fromEdgeSet B.edgeSet) := by
  apply RawBoundaryState.ext
  · exact SpliceStateFields.stateAt_horizontal_eq (by omega) GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r s hsplice hm hk
  · exact SpliceStateFields.stateAt_diagonal_eq (by omega) GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r s hsplice hm hk
  · exact SpliceStateFields.stateAt_reach_eq (by omega) GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r s hsplice hm hk hGA hxy
  · simpa only [add_zero] using
      SpliceAssignedParity.stateAt_parity_add_of_splice hm hk GA B J hB hJ
        a₀ a₁ r s hsplice 0 (by simpa only [zero_add] using hparity)

/-- Equal raw states at two actual cuts identify both interval endpoints
with the already defined common core state. -/
theorem common_interval_return {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a b : Fin (n + 1)) (hab : a.val ≤ b.val)
    (ha : cutState hm (fromEdgeSet C.edgeSet) a = commonWitnessState m hm)
    (hb : cutState hm (fromEdgeSet C.edgeSet) b = commonWitnessState m hm) :
    Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) (b.val - a.val)
      (commonCoreState m hm) (commonCoreState m hm)) := by
  have ha' : coreAtCut hm hn C hC a = commonCoreState m hm := Subtype.ext ha
  have hb' : coreAtCut hm hn C hC b = commonCoreState m hm := Subtype.ext hb
  simpa only [ha', hb'] using cycleIntervalPath_nonempty hm hn C hC a b hab

/-- Self-splicing the actual two-column perimeter yields a return of length
two at the common state. Its selected gap is fixed, without row rotation. -/
theorem common_return_two (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) 2
      (commonCoreState m hm) (commonCoreState m hm)) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + 1 := ⟨m - 1, by omega⟩
  have hq : 2 ≤ q := by omega
  let C := perimeterCycle q hq
  let r := beforeLastRow (q + 1) hm
  let s := lastRow (q + 1) hm
  have hgap : NextRow r s := nextRow_beforeLast_last hm
  have hC : C.IsHamiltonianCycle := perimeterCycle_isHamiltonianCycle q hq
  have hleft : s((r, lastCol 2 (by decide)), (s, lastCol 2 (by decide))) ∈ C.edges :=
    perimeterCycle_right_join_edge q hq
  have hright : s((r, firstCol 2 (by decide)), (s, firstCol 2 (by decide))) ∈ C.edges :=
    perimeterCycle_left_join_edge q hq
  obtain ⟨J, hJ, hparity, hsplice, hleftState⟩ :=
    SpliceLeftState.exists_splice_preserving_left_state
      (j := 0) (k := 1) (b := 2) hm (by decide) (by decide)
      r s hgap C C hC hC hleft hright
  let a₀ : Vertex (q + 1) 2 := (r, lastCol 2 (by decide))
  let a₁ : Vertex (q + 1) 2 := (s, lastCol 2 (by decide))
  let GA : SimpleGraph (Vertex (q + 1) 2) :=
    (fromEdgeSet C.edgeSet).deleteEdges {s(a₀, a₁)}
  have hGA : GA.Connected := CylinderFrontier.selected_cycle_delete_edge_connected C hC hleft
  have hxy : (fromEdgeSet C.edgeSet).Adj
      (r, firstCol 2 (by decide)) (s, firstCol 2 (by decide)) :=
    (fromEdgeSet_adj C.edgeSet).mpr
      ⟨hright, (vertical_edge hm r s hgap (firstCol 2 (by decide))).ne⟩
  have hparity' : typeParity hm J = typeParity hm C := by
    simpa only [show typeParity hm C = 0 from perimeterCycle_typeParity q hq,
      zero_add] using hparity
  have hrightState := stateAt_eq_of_zero_splice
    (a := 2) (j := 0) (k := 1) hm (by decide) GA C J
    hC.isCycle.isTrail hJ.isCycle.isTrail a₀ a₁ r s hGA hxy hsplice hparity'
  have hcommon : stateAt (j := 0) (k := 1) hm (by decide) (fromEdgeSet C.edgeSet) =
      commonWitnessState (q + 1) hm := perimeterCycle_stateAt_common q hq
  have hfirst : cutState (n := 2) hm (fromEdgeSet J.edgeSet) 0 =
      commonWitnessState (q + 1) hm := by
    exact hleftState.trans hcommon
  have hlast : cutState (n := 2) hm (fromEdgeSet J.edgeSet) 2 =
      commonWitnessState (q + 1) hm := by
    exact hrightState.trans hcommon
  exact common_interval_return hm (by decide) J hJ (0 : Fin 3) (2 : Fin 3)
    (by decide) hfirst hlast

/-- Self-splicing the actual three-column witness yields a return of length
three at the same common state, using each witness's last cut. -/
theorem common_return_three (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) 3
      (commonCoreState m hm) (commonCoreState m hm)) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + 1 := ⟨m - 1, by omega⟩
  have hq : 2 ≤ q := by omega
  let C := threeWitnessCycle q hq
  let r := beforeLastRow (q + 1) hm
  let s := lastRow (q + 1) hm
  have hgap : NextRow r s := nextRow_beforeLast_last hm
  have hC : C.IsHamiltonianCycle := threeWitnessCycle_isHamiltonianCycle q hq
  have hleft : s((r, lastCol 3 (by decide)), (s, lastCol 3 (by decide))) ∈ C.edges :=
    threeWitnessCycle_right_join_edge q hq
  have hright : s((r, firstCol 3 (by decide)), (s, firstCol 3 (by decide))) ∈ C.edges :=
    threeWitnessCycle_left_join_edge q hq
  obtain ⟨J, hJ, hparity, hsplice, hleftState⟩ :=
    SpliceLeftState.exists_splice_preserving_left_state
      (j := 1) (k := 1) (b := 3) hm (by decide) (by decide)
      r s hgap C C hC hC hleft hright
  let a₀ : Vertex (q + 1) 3 := (r, lastCol 3 (by decide))
  let a₁ : Vertex (q + 1) 3 := (s, lastCol 3 (by decide))
  let GA : SimpleGraph (Vertex (q + 1) 3) :=
    (fromEdgeSet C.edgeSet).deleteEdges {s(a₀, a₁)}
  have hGA : GA.Connected := CylinderFrontier.selected_cycle_delete_edge_connected C hC hleft
  have hxy : (fromEdgeSet C.edgeSet).Adj
      (r, firstCol 3 (by decide)) (s, firstCol 3 (by decide)) :=
    (fromEdgeSet_adj C.edgeSet).mpr
      ⟨hright, (vertical_edge hm r s hgap (firstCol 3 (by decide))).ne⟩
  have hparity' : typeParity hm J = typeParity hm C := by
    simpa only [show typeParity hm C = 0 from threeWitnessCycle_typeParity q hq,
      zero_add] using hparity
  have hrightState := stateAt_eq_of_zero_splice
    (a := 3) (j := 1) (k := 1) hm (by decide) GA C J
    hC.isCycle.isTrail hJ.isCycle.isTrail a₀ a₁ r s hGA hxy hsplice hparity'
  have hcommon : stateAt (j := 1) (k := 1) hm (by decide) (fromEdgeSet C.edgeSet) =
      commonWitnessState (q + 1) hm := threeWitnessCycle_stateAt_common q hq
  have hfirst : cutState (n := 4) hm (fromEdgeSet J.edgeSet) 1 =
      commonWitnessState (q + 1) hm := by
    exact hleftState.trans hcommon
  have hlast : cutState (n := 4) hm (fromEdgeSet J.edgeSet) 4 =
      commonWitnessState (q + 1) hm := by
    exact hrightState.trans hcommon
  exact common_interval_return hm (by decide) J hJ (1 : Fin 5) (4 : Fin 5)
    (by decide) hfirst hlast

#print axioms stateAt_eq_of_zero_splice
#print axioms common_interval_return
#print axioms common_return_two
#print axioms common_return_three

end TriangularCylinder.Transfer
