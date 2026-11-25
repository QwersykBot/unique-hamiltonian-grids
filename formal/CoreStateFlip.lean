import StateEndVertical
import SpliceAssignedParity
import SpliceStateFields

/-!
# Actual core states are closed under parity flip

The reusable same-splice theorem assembles the four state-field identities.
For occurrence closure, an actual three-column auxiliary of parity one is
spliced onto the same Hamiltonian witness. Thus the parity increment used
by the closure theorem is derived from a concrete cycle construction.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph BoundaryState SplicePrefixCoordinates
open CylinderFrontier.EdgeReplacement

/-- The same exact splice flips the full old state when its total parity
increment is one. This applies to every old cut of the same pair of trails. -/
theorem stateAt_flip_of_splice {m a j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
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
    (hparity : typeParity hm J = 1 + typeParity hm B) :
    stateAt hm hk ((fromEdgeSet J.edgeSet).comap (fullWidthEquiv m a j k)) =
      RawBoundaryState.flip (stateAt hm hk (fromEdgeSet B.edgeSet)) := by
  apply RawBoundaryState.ext
  · exact SpliceStateFields.stateAt_horizontal_eq (by omega) GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r s hsplice hm hk
  · exact SpliceStateFields.stateAt_diagonal_eq (by omega) GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r s hsplice hm hk
  · exact SpliceStateFields.stateAt_reach_eq (by omega) GA
      (fromEdgeSet B.edgeSet) (fromEdgeSet J.edgeSet) a₀ a₁ r s hsplice hm hk hGA hxy
  · exact SpliceAssignedParity.stateAt_parity_add_of_splice hm hk GA B J hB hJ
      a₀ a₁ r s hsplice 1 hparity

/-- Flipping the parity coordinate of a nonfull occurring state gives another
actual occurrence, witnessed by a concrete three-column left splice. -/
theorem occurs_flip_of_nonfull {m : ℕ} (hm : 3 ≤ m) {σ : RawBoundaryState m}
    (hocc : Occurs hm σ) (hnonfull : ¬ FullOutgoing σ) :
    Occurs hm (RawBoundaryState.flip σ) := by
  classical
  rcases hocc with ⟨j, k, hk, v, B, hB, rfl⟩
  have hb : 2 ≤ j + 1 + k := by omega
  have ha : 2 ≤ 3 := by decide
  obtain ⟨⟨r, s, hrs, hBfirst⟩, _⟩ :=
    StateEndVertical.exists_selected_end_edges_of_nonfull_stateAt hm hk B hB hnonfull
  obtain ⟨u, A, hA, hAparity, _, hAright⟩ :=
    exists_aligned_three_column_auxiliary m hm r s r s hrs hrs
  obtain ⟨J, hJ, hparity, hset⟩ :=
    exists_splice_of_selected_edges hm ha hb r s hrs A B hA hB hAright hBfirst
  let a₀ : Vertex m 3 := (r, lastCol 3 ha)
  let a₁ : Vertex m 3 := (s, lastCol 3 ha)
  let GA : SimpleGraph (Vertex m 3) :=
    (fromEdgeSet A.edgeSet).deleteEdges {s(a₀, a₁)}
  let GB := fromEdgeSet B.edgeSet
  let GJ := fromEdgeSet J.edgeSet
  have hGA : GA.Connected :=
    CylinderFrontier.selected_cycle_delete_edge_connected A hA hAright
  have hxy : GB.Adj (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb) :=
    (fromEdgeSet_adj B.edgeSet).mpr
      ⟨hBfirst, (vertical_edge hm r s hrs (firstCol (j + 1 + k) hb)).ne⟩
  have hsplice : GJ.comap (columnSumEquiv m 3 (j + 1 + k)) =
      replacementGraph GB GA
        (r, firstCol (j + 1 + k) hb) (s, firstCol (j + 1 + k) hb) a₀ a₁ :=
    SpliceSelectedGraph.selected_splice_comap hm ha hb r s A B J hset
  have hparity' : typeParity hm J = 1 + typeParity hm B := by
    simpa only [hAparity] using hparity
  have hflip : stateAt (j := 3 + j) hm hk (GJ.comap (fullWidthEquiv m 3 j k)) =
      RawBoundaryState.flip (stateAt hm hk GB) :=
    stateAt_flip_of_splice hm hk GA B J hB.isCycle.isTrail hJ.isCycle.isTrail
      a₀ a₁ r s hGA hxy hsplice hparity'
  rw [← hflip]
  exact StateWidthTransport.occurs_joined_state hm hk J hJ

/-- The actual core-state flip changes only the raw parity coordinate. -/
def coreFlip {m : ℕ} (hm : 3 ≤ m) (σ : CoreState hm) : CoreState hm :=
  ⟨RawBoundaryState.flip σ.val,
    occurs_flip_of_nonfull hm σ.property.1 σ.property.2,
    by
      intro hfull
      exact σ.property.2 hfull⟩

@[simp] theorem coreFlip_val {m : ℕ} (hm : 3 ≤ m) (σ : CoreState hm) :
    (coreFlip hm σ).val = RawBoundaryState.flip σ.val := rfl

theorem coreFlip_involutive {m : ℕ} (hm : 3 ≤ m) :
    Function.Involutive (coreFlip hm) := by
  intro σ
  apply Subtype.ext
  exact RawBoundaryState.flip_involutive σ.val

theorem coreFlip_ne {m : ℕ} (hm : 3 ≤ m) (σ : CoreState hm) :
    coreFlip hm σ ≠ σ := by
  intro h
  exact RawBoundaryState.flip_ne σ.val (congrArg Subtype.val h)

/-- The flip is its own inverse on the actual core-state type. -/
def coreFlipEquiv {m : ℕ} (hm : 3 ≤ m) : CoreState hm ≃ CoreState hm where
  toFun := coreFlip hm
  invFun := coreFlip hm
  left_inv := coreFlip_involutive hm
  right_inv := coreFlip_involutive hm

@[simp] theorem coreFlipEquiv_apply {m : ℕ} (hm : 3 ≤ m) (σ : CoreState hm) :
    coreFlipEquiv hm σ = coreFlip hm σ := rfl

#print axioms stateAt_flip_of_splice
#print axioms occurs_flip_of_nonfull
#print axioms coreFlip
#print axioms coreFlip_val
#print axioms coreFlip_involutive
#print axioms coreFlip_ne
#print axioms coreFlipEquiv
#print axioms coreFlipEquiv_apply

end TriangularCylinder.Transfer
