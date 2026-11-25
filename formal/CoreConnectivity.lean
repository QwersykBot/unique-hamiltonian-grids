import CommonReturns
import StateEndVertical
import AuxiliaryParity
import StateInterval

/-!
# Paths between every pair of actual core states

An actual witness for the source state is joined to an aligned auxiliary
whose parity equals that witness's parity. This produces a parity-zero
left block, retaining the source state and a prescribed right end edge.
Joining this same block to an actual target witness preserves the source
state on the left and the shifted target state on the right. The interval
between these two cuts of the same joined Hamiltonian cycle is the desired
path of actual local labels.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph BoundaryState SplicePrefixCoordinates
open CylinderFrontier.EdgeReplacement

/-- The outer right vertical edges survive an exact splice: the only
removed right vertical lies in column zero, before the positive last column. -/
theorem right_last_adj_iff_of_splice {m a b : ℕ} (hb : 2 ≤ b)
    (GA : SimpleGraph (Vertex m a)) (GB : SimpleGraph (Vertex m b))
    (GJ : SimpleGraph (Vertex m (a + b))) (a₀ a₁ : Vertex m a) (r s : Fin m)
    (hsplice : GJ.comap (columnSumEquiv m a b) =
      replacementGraph GB GA (r, firstCol b hb) (s, firstCol b hb) a₀ a₁)
    (q t : Fin m) :
    GJ.Adj (q, lastCol (a + b) (by omega)) (t, lastCol (a + b) (by omega)) ↔
      GB.Adj (q, lastCol b hb) (t, lastCol b hb) := by
  have hlast (z : Fin m) : rightVertex a (z, lastCol b hb) =
      (z, lastCol (a + b) (by omega)) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change a + (b - 1) = a + b - 1
      omega
  rw [← hlast q, ← hlast t]
  change (GJ.comap (columnSumEquiv m a b)).Adj
    (Sum.inr (q, lastCol b hb)) (Sum.inr (t, lastCol b hb)) ↔ _
  rw [hsplice]
  change (GB.Adj (q, lastCol b hb) (t, lastCol b hb) ∧
    ¬ (((q, lastCol b hb) = (r, firstCol b hb) ∧
        (t, lastCol b hb) = (s, firstCol b hb)) ∨
      ((q, lastCol b hb) = (s, firstCol b hb) ∧
        (t, lastCol b hb) = (r, firstCol b hb)))) ↔ _
  have hne (z : Fin m) : (q, lastCol b hb) ≠ (z, firstCol b hb) := by
    intro h
    have hc := congrArg (fun x : Vertex m b => x.2.val) h
    change b - 1 = 0 at hc
    omega
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rintro (⟨he, _⟩ | ⟨he, _⟩)
    · exact hne r he
    · exact hne s he

/-- Left-state preservation allows the old cylinder width to be presented
independently of its cut split. The graph identity is unchanged. -/
theorem stateAt_left_eq_of_splice_width {m j k a b : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hb : 2 ≤ b) (ha : j + 1 + k = a)
    (A : SimpleGraph (Vertex m a)) (B : SimpleGraph (Vertex m b))
    (J : SimpleGraph (Vertex m (a + b))) (r s : Fin m)
    (hsplice : J.comap (columnSumEquiv m a b) =
      replacementGraph B
        (A.deleteEdges {s((r, lastCol a (by omega)), (s, lastCol a (by omega)))})
        (r, firstCol b hb) (s, firstCol b hb)
        (r, lastCol a (by omega)) (s, lastCol a (by omega))) :
    stateAt (j := j) (k := k + b) hm (by omega)
        (J.comap (widthEquiv (by omega : j + 1 + (k + b) = a + b))) =
      stateAt hm hk (A.comap (widthEquiv ha)) := by
  subst a
  simpa only [SpliceLeftState.joinedLeftGraph, SpliceLeftState.leftWidthEquiv,
    widthEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id] using
    SpliceLeftState.stateAt_eq_of_graph_identity hk hb A B J r s hsplice hm

/-- Every ordered pair of actual nonfull core states is joined by a finite
path of actual local labels. All auxiliary, Hamiltonian, parity, and endpoint
facts are constructed here from the two occurrence witnesses. -/
theorem core_path_nonempty {m : ℕ} (hm : 3 ≤ m) (σ τ : CoreState hm) :
    ∃ n : ℕ, Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) n σ τ) := by
  classical
  obtain ⟨j₁, k₁, hk₁, v₁, C₁, hC₁, hσ⟩ := σ.property.1
  obtain ⟨j₂, k₂, hk₂, v₂, C₂, hC₂, hτ⟩ := τ.property.1
  have hnonfull₁ : ¬ FullOutgoing (stateAt hm hk₁ (fromEdgeSet C₁.edgeSet)) := by
    rw [hσ]
    exact σ.property.2
  have hnonfull₂ : ¬ FullOutgoing (stateAt hm hk₂ (fromEdgeSet C₂.edgeSet)) := by
    rw [hτ]
    exact τ.property.2
  obtain ⟨_, r₁, s₁, hgap₁, hC₁right⟩ :=
    StateEndVertical.exists_selected_end_edges_of_nonfull_stateAt hm hk₁ C₁ hC₁ hnonfull₁
  obtain ⟨⟨r₂, s₂, hgap₂, hC₂left⟩, _⟩ :=
    StateEndVertical.exists_selected_end_edges_of_nonfull_stateAt hm hk₂ C₂ hC₂ hnonfull₂
  obtain ⟨u, hu, vU, U, hU, hUp, hUleft, hUright⟩ :=
    exists_aligned_auxiliary_of_parity m hm (typeParity hm C₁)
      r₁ s₁ r₂ s₂ hgap₁ hgap₂
  obtain ⟨M, hM, hMp, hspliceM, hσM⟩ :=
    SpliceLeftState.exists_splice_preserving_left_state hm hk₁ hu
      r₁ s₁ hgap₁ C₁ U hC₁ hU hC₁right hUleft
  have hMpzero : typeParity hm M = 0 := by
    simpa only [hUp, ZModModule.add_self] using hMp
  have hUrightAdj : (fromEdgeSet U.edgeSet).Adj
      (r₂, lastCol u hu) (s₂, lastCol u hu) :=
    (fromEdgeSet_adj U.edgeSet).mpr
      ⟨hUright, (vertical_edge hm r₂ s₂ hgap₂ (lastCol u hu)).ne⟩
  have hMrightAdj := (right_last_adj_iff_of_splice hu
    ((fromEdgeSet C₁.edgeSet).deleteEdges
      {s((r₁, lastCol (j₁ + 1 + k₁) (by omega)),
        (s₁, lastCol (j₁ + 1 + k₁) (by omega)))})
    (fromEdgeSet U.edgeSet) (fromEdgeSet M.edgeSet)
    (r₁, lastCol (j₁ + 1 + k₁) (by omega))
    (s₁, lastCol (j₁ + 1 + k₁) (by omega)) r₁ s₁ hspliceM r₂ s₂).mpr hUrightAdj
  have hMright : s((r₂, lastCol ((j₁ + 1 + k₁) + u) (by omega)),
      (s₂, lastCol ((j₁ + 1 + k₁) + u) (by omega))) ∈ M.edges := hMrightAdj.1
  obtain ⟨J, hJ, hJp, hJedges⟩ := exists_splice_of_selected_edges hm
    (by omega) (by omega) r₂ s₂ hgap₂ M C₂ hM hC₂ hMright hC₂left
  have hspliceJ := SpliceSelectedGraph.selected_splice_comap hm (by omega) (by omega)
    r₂ s₂ M C₂ J hJedges
  have hσJstep := stateAt_left_eq_of_splice_width
    (j := j₁) (k := k₁ + u) hm (by omega) (by omega) (by omega)
    (fromEdgeSet M.edgeSet) (fromEdgeSet C₂.edgeSet) (fromEdgeSet J.edgeSet)
    r₂ s₂ hspliceJ
  have hσJ : stateAt (j := j₁) (k := (k₁ + u) + (j₂ + 1 + k₂)) hm (by omega)
      ((fromEdgeSet J.edgeSet).comap (widthEquiv (by omega))) = σ.val :=
    hσJstep.trans (hσM.trans hσ)
  let a₀ : Vertex m ((j₁ + 1 + k₁) + u) :=
    (r₂, lastCol ((j₁ + 1 + k₁) + u) (by omega))
  let a₁ : Vertex m ((j₁ + 1 + k₁) + u) :=
    (s₂, lastCol ((j₁ + 1 + k₁) + u) (by omega))
  let GA : SimpleGraph (Vertex m ((j₁ + 1 + k₁) + u)) :=
    (fromEdgeSet M.edgeSet).deleteEdges {s(a₀, a₁)}
  have hGA : GA.Connected := CylinderFrontier.selected_cycle_delete_edge_connected M hM hMright
  have hC₂leftAdj : (fromEdgeSet C₂.edgeSet).Adj
      (r₂, firstCol (j₂ + 1 + k₂) (by omega))
      (s₂, firstCol (j₂ + 1 + k₂) (by omega)) :=
    (fromEdgeSet_adj C₂.edgeSet).mpr
      ⟨hC₂left, (vertical_edge hm r₂ s₂ hgap₂ (firstCol (j₂ + 1 + k₂) (by omega))).ne⟩
  have hJpzero : typeParity hm J = typeParity hm C₂ := by
    simpa only [hMpzero, zero_add] using hJp
  have hτJstep := stateAt_eq_of_zero_splice hm hk₂ GA C₂ J
    hC₂.isCycle.isTrail hJ.isCycle.isTrail a₀ a₁ r₂ s₂ hGA hC₂leftAdj hspliceJ hJpzero
  have hτJ : stateAt (j := ((j₁ + 1 + k₁) + u) + j₂) (k := k₂) hm hk₂
      ((fromEdgeSet J.edgeSet).comap (widthEquiv (by omega))) = τ.val := by
    simpa only [StateWidthTransport.fullWidthEquiv_eq_widthEquiv] using hτJstep.trans hτ
  refine ⟨(((j₁ + 1 + k₁) + u) + j₂) - j₁, ?_⟩
  exact path_between_stateAt (j := j₁) (k := (k₁ + u) + (j₂ + 1 + k₂))
    (j' := ((j₁ + 1 + k₁) + u) + j₂) (k' := k₂) hm (by omega)
    (by omega) hk₂ (by omega) (by omega) (by omega) J hJ σ τ hσJ hτJ

#print axioms right_last_adj_iff_of_splice
#print axioms stateAt_left_eq_of_splice_width
#print axioms core_path_nonempty

end TriangularCylinder.Transfer
