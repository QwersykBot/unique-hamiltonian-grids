import ColumnFragments
import BoundaryState
import SelectedIff
import ColumnBoundaryDegree

/-!
# Concrete prefix replacement on selected cylinder graphs

The mixed graph keeps the suffix of the second selection and replaces its
prefix by the first selection's prefix, with the same row labels. Geometry
and attachment come from the actual selected cylinder graphs. Equal boundary
reachability transfers connectedness through the checked substitution theorem.
The exact selected-edge characterization supplies the Hamiltonian realization.
Parity preservation is a separate obligation.
-/

namespace TriangularCylinder.PrefixReplacement

open SimpleGraph BoundaryState

def mixedGlue {m j oldSuffix oldPrefix k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    SimpleGraph (ColumnCut.CutVertex m j k) :=
  CylinderFrontier.glue (ColumnCut.prefixPart j oldSuffix H) (ColumnCut.suffixPart oldPrefix k K)

def mixedGraph {m j oldSuffix oldPrefix k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) :
    SimpleGraph (Vertex m (j + 1 + k)) :=
  ColumnFragments.transportedGlue
    (ColumnCut.prefixPart j oldSuffix H) (ColumnCut.suffixPart oldPrefix k K)

def mixedGraphIso {m j oldSuffix oldPrefix k : ℕ}
    (H : SimpleGraph (Vertex m (j + 1 + oldSuffix)))
    (K : SimpleGraph (Vertex m (oldPrefix + 1 + k))) : mixedGlue H K ≃g mixedGraph H K :=
  SimpleGraph.Iso.map (ColumnCut.vertexEquiv m j k) (mixedGlue H K)

theorem mixedGraph_le {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm) :
    mixedGraph H K ≤ graph m (j + 1 + k) hm :=
  ColumnFragments.mixed_cut_parts_le hm hH hK

/-- Attachment and old glued connectedness are derived from the two original
selected graphs; only their encoded boundary relation is compared. -/
theorem mixedGlue_connected {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hconnH : H.Connected) (hconnK : K.Connected)
    (hreach : (stateAt hm hOldSuffix H).reach = (stateAt hm hk K).reach) :
    (mixedGlue H K).Connected := by
  apply CylinderFrontier.glue_connected_of_boundary_imp
    (ColumnCut.suffixPart oldPrefix k K)
    (ColumnCut.prefixPart_touchesBoundary hm hK hconnK)
    (ColumnCut.prefixPart_touchesBoundary hm hH hconnH)
    _ (ColumnCut.glue_parts_connected hm hK hconnK)
  intro r s hrs
  have hr := (stateAt_reach_iff hm hk K r s).mpr hrs
  rw [← hreach] at hr
  exact (stateAt_reach_iff hm hOldSuffix H r s).mp hr

theorem mixedGraph_connected {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hconnH : H.Connected) (hconnK : K.Connected)
    (hreach : (stateAt hm hOldSuffix H).reach = (stateAt hm hk K).reach) :
    (mixedGraph H K).Connected :=
  (mixedGlue_connected hm hOldSuffix hk hH hK hconnH hconnK hreach).map
    (mixedGraphIso H K).toHom (mixedGraphIso H K).toEquiv.surjective

/-- The peer degree-composition theorem supplies degree two in the canonical
glue; the actual vertex bijection transports those neighbor counts. -/
theorem mixedGraph_neighbor_ncard_two {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hdegH : ∀ v, (H.neighborSet v).ncard = 2)
    (hdegK : ∀ v, (K.neighborSet v).ncard = 2)
    (hhor : (stateAt hm hOldSuffix H).horizontal = (stateAt hm hk K).horizontal)
    (hdiag : (stateAt hm hOldSuffix H).diagonal = (stateAt hm hk K).diagonal) :
    ∀ v, ((mixedGraph H K).neighborSet v).ncard = 2 := by
  have hd := ColumnCut.mixed_parts_neighbor_ncard_two hm hOldSuffix hk
    hH hK hdegH hdegK hhor hdiag
  intro v
  obtain ⟨x, rfl⟩ := (mixedGraphIso H K).toEquiv.surjective v
  have heq := congrArg ENat.toNat (Set.encard_congr ((mixedGraphIso H K).mapNeighborSet x))
  exact heq.symm.trans (hd x)

/-- The frozen finite selected-edge characterization yields an actual ambient
Hamiltonian presentation of the entire connected degree-two selected graph. -/
theorem exact_realization_of_connected_two {V : Type*} [Finite V] [DecidableEq V]
    {G J : SimpleGraph V} (hJG : J ≤ G) (hconn : J.Connected)
    (hdeg : ∀ v, (J.neighborSet v).ncard = 2) :
    ∃ v : V, ∃ C : G.Walk v v, C.IsHamiltonianCycle ∧ C.edgeSet = J.edgeSet := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let E : Finset (Sym2 V) := J.edgeSet.toFinset
  have hEeq : (E : Set (Sym2 V)) = J.edgeSet := Set.coe_toFinset _
  have hE : (E : Set (Sym2 V)) ⊆ G.edgeSet := by
    rw [hEeq]
    exact SimpleGraph.edgeSet_mono hJG
  have hselected : fromEdgeSet (E : Set (Sym2 V)) = J := by
    rw [hEeq, fromEdgeSet_edgeSet]
  have hreal : CountedHamiltonian.HasHamiltonianRealization G E :=
    (CountedHamiltonian.realization_iff_connected_two hE).mpr
      (by simpa only [hselected] using And.intro hconn hdeg)
  obtain ⟨v, C, hC, hCE⟩ := hreal
  refine ⟨v, C, hC, ?_⟩
  rw [← CountedHamiltonian.coe_selectedEdges C, hCE, hEeq]

/-- Equal physical outgoing masks and boundary reachability preserve all
graph-theoretic hypotheses of the exact selected-edge characterization. -/
theorem replacement_properties {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hconnH : H.Connected) (hconnK : K.Connected)
    (hdegH : ∀ v, (H.neighborSet v).ncard = 2)
    (hdegK : ∀ v, (K.neighborSet v).ncard = 2)
    (hhor : (stateAt hm hOldSuffix H).horizontal = (stateAt hm hk K).horizontal)
    (hdiag : (stateAt hm hOldSuffix H).diagonal = (stateAt hm hk K).diagonal)
    (hreach : (stateAt hm hOldSuffix H).reach = (stateAt hm hk K).reach) :
    mixedGraph H K ≤ graph m (j + 1 + k) hm ∧ (mixedGraph H K).Connected ∧
      ∀ v, ((mixedGraph H K).neighborSet v).ncard = 2 :=
  ⟨mixedGraph_le hm hH hK,
    mixedGraph_connected hm hOldSuffix hk hH hK hconnH hconnK hreach,
    mixedGraph_neighbor_ncard_two hm hOldSuffix hk hH hK hdegH hdegK hhor hdiag⟩

/-- Concrete prefix replacement has an actual standard Hamiltonian realization
in the new ambient cylinder, with exactly the constructed selected edge set.
No property of the mixed graph is supplied as a hypothesis. -/
theorem replacement_exact_hamiltonian {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hconnH : H.Connected) (hconnK : K.Connected)
    (hdegH : ∀ v, (H.neighborSet v).ncard = 2)
    (hdegK : ∀ v, (K.neighborSet v).ncard = 2)
    (hhor : (stateAt hm hOldSuffix H).horizontal = (stateAt hm hk K).horizontal)
    (hdiag : (stateAt hm hOldSuffix H).diagonal = (stateAt hm hk K).diagonal)
    (hreach : (stateAt hm hOldSuffix H).reach = (stateAt hm hk K).reach) :
    mixedGraph H K ≤ graph m (j + 1 + k) hm ∧ (mixedGraph H K).Connected ∧
      (∀ v, ((mixedGraph H K).neighborSet v).ncard = 2) ∧
      ∃ v : Vertex m (j + 1 + k), ∃ C : (graph m (j + 1 + k) hm).Walk v v,
        C.IsHamiltonianCycle ∧ C.edgeSet = (mixedGraph H K).edgeSet := by
  obtain ⟨hvalid, hconn, hdeg⟩ := replacement_properties hm hOldSuffix hk
    hH hK hconnH hconnK hdegH hdegK hhor hdiag hreach
  exact ⟨hvalid, hconn, hdeg, exact_realization_of_connected_two hvalid hconn hdeg⟩

/-- Full raw-state equality is a convenient sufficient input. Only its
horizontal, diagonal and reachability fields are used in this theorem;
the conclusion makes no parity claim. -/
theorem replacement_of_raw_state_eq {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    (hOldSuffix : 1 ≤ oldSuffix) (hk : 1 ≤ k)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm)
    (hconnH : H.Connected) (hconnK : K.Connected)
    (hdegH : ∀ v, (H.neighborSet v).ncard = 2)
    (hdegK : ∀ v, (K.neighborSet v).ncard = 2)
    (hstate : stateAt hm hOldSuffix H = stateAt hm hk K) :
    mixedGraph H K ≤ graph m (j + 1 + k) hm ∧ (mixedGraph H K).Connected ∧
      (∀ v, ((mixedGraph H K).neighborSet v).ncard = 2) ∧
      ∃ v : Vertex m (j + 1 + k), ∃ C : (graph m (j + 1 + k) hm).Walk v v,
        C.IsHamiltonianCycle ∧ C.edgeSet = (mixedGraph H K).edgeSet :=
  replacement_exact_hamiltonian hm hOldSuffix hk hH hK hconnH hconnK hdegH hdegK
    (congrArg RawBoundaryState.horizontal hstate)
    (congrArg RawBoundaryState.diagonal hstate)
    (congrArg RawBoundaryState.reach hstate)

#print axioms mixedGraph_le
#print axioms mixedGlue_connected
#print axioms mixedGraph_connected
#print axioms mixedGraph_neighbor_ncard_two
#print axioms exact_realization_of_connected_two
#print axioms replacement_properties
#print axioms replacement_exact_hamiltonian
#print axioms replacement_of_raw_state_eq

end TriangularCylinder.PrefixReplacement
