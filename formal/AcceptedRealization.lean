import CompletionTransport
import AcceptedGraph
import AcceptedExtensionality

/-!
# Hamiltonian realization of arbitrary accepted physical data

The induction retains a genuine ambient Hamiltonian completion of every
processed accepted prefix, its exact selected prefix graph, and its three
non-parity state fields. Local witnesses extend this prefix, and the terminal
witness closes it at the requested width. No parity premise or parity
conclusion is used to obtain the exact Hamiltonian edge selection.
-/

namespace TriangularCylinder.AcceptedRealization

open SimpleGraph ColumnCut ColumnFragments BoundaryState Transfer
open PrefixReplacement FragmentRecovery ProcessedPrefix CompletionTransport

/-- A selected ambient graph with an explicit standard Hamiltonian realization. -/
structure Genuine {m L : ℕ} (hm : 3 ≤ m) (H : SimpleGraph (Vertex m L)) : Prop where
  valid : H ≤ graph m L hm
  connected : H.Connected
  two : ∀ v, (H.neighborSet v).ncard = 2
  realized : ∃ v, ∃ C : (graph m L hm).Walk v v,
    C.IsHamiltonianCycle ∧ C.edgeSet = H.edgeSet

theorem genuine_of_conditions {m L : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m L)} (hH : H ≤ graph m L hm) (hc : H.Connected)
    (hd : ∀ v, (H.neighborSet v).ncard = 2) : Genuine hm H :=
  ⟨hH, hc, hd, exact_realization_of_connected_two hH hc hd⟩

theorem genuine_of_cycle {m L : ℕ} (hm : 3 ≤ m) {v : Vertex m L}
    (C : (graph m L hm).Walk v v) (hC : C.IsHamiltonianCycle) :
    Genuine hm (fromEdgeSet C.edgeSet) := by
  apply genuine_of_conditions hm (cycle_selectedGraph_le hm C)
  · simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_connected hC
  · intro x
    simpa only [CountedHamiltonian.coe_selectedEdges] using
      CountedHamiltonian.hamiltonian_selected_ncard hC x

theorem genuine_widthEquiv {m a b : ℕ} (hm : 3 ≤ m) (h : a = b)
    {H : SimpleGraph (Vertex m b)} (hH : Genuine hm H) :
    Genuine hm (H.comap (widthEquiv h)) := by
  subst b
  simpa only [widthEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id] using hH

theorem genuine_advance {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + (k + 1)))} (hH : Genuine hm H) :
    Genuine hm (advanceGraph H) :=
  genuine_of_conditions hm (advanceGraph_le hm hH.valid)
    (advanceGraph_connected hH.connected) (advanceGraph_ncard_two hH.two)

theorem genuine_mixed {m j k d t : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (ht : 1 ≤ t)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    {K : SimpleGraph (Vertex m (d + 1 + t))}
    (hH : Genuine hm H) (hK : Genuine hm K)
    (hHor : (stateAt hm hk H).horizontal = (stateAt hm ht K).horizontal)
    (hDiag : (stateAt hm hk H).diagonal = (stateAt hm ht K).diagonal)
    (hReach : (stateAt hm hk H).reach = (stateAt hm ht K).reach) :
    Genuine hm (mixedGraph H K) := by
  obtain ⟨hv, hc, hd, hr⟩ := replacement_exact_hamiltonian hm hk ht
    hH.valid hK.valid hH.connected hK.connected hH.two hK.two hHor hDiag hReach
  exact ⟨hv, hc, hd, hr⟩

theorem split_boundary_vertical {m n k : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1))
    (h : c.val + 1 + k = n + 2) :
    verticalMask hm (H.comap (widthEquiv h)) (boundaryCol c.val k) =
      verticalMask hm H c.castSucc := by
  funext r
  rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
  rfl

theorem split_next_vertical {m n k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    (H : SimpleGraph (Vertex m (n + 2))) (c : Fin (n + 1))
    (h : c.val + 1 + k = n + 2) :
    verticalMask hm (H.comap (widthEquiv h)) (nextCol hk) = verticalMask hm H c.succ := by
  funext r
  rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
  rfl

/-- A completion keeps every processed physical edge and the current physical
outgoing masks and reachability relation. The remaining suffix may vary. -/
def PrefixCompletion {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (c : Fin (n + 1)) : Prop :=
  ∃ k : ℕ, ∃ hk : 1 ≤ k, ∃ H : SimpleGraph (Vertex m (c.val + 1 + k)),
    Genuine hm H ∧
    prefixPart c.val k H = prefixPart c.val (cutTail c) (cutGraph (acceptedGraph w) c) ∧
    (stateAt hm hk H).horizontal = (acceptedCutStates w c).val.horizontal ∧
    (stateAt hm hk H).diagonal = (acceptedCutStates w c).val.diagonal ∧
    (stateAt hm hk H).reach = (acceptedCutStates w c).val.reach

theorem prefixCompletion_zero {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : PrefixCompletion w 0 := by
  obtain ⟨q, v, C, hC, hState, hV⟩ := accepted_initial_realized w
  let G := fromEdgeSet C.edgeSet
  let c : Fin (q + 1) := 0
  let H := cutGraph G c
  have hG : Genuine hm G := genuine_of_cycle hm C hC
  have hH : Genuine hm H := genuine_widthEquiv hm (cutWidth_eq c) hG
  have hstate : stateAt hm (cutTail_pos c) H = (acceptedCutStates w 0).val := hState
  have hvH : verticalMask hm H (boundaryCol 0 (cutTail c)) = acceptedVerticalMasks w 0 :=
    (split_boundary_vertical hm G c (cutWidth_eq c)).trans hV
  have hvR : verticalMask hm (cutGraph (acceptedGraph w) 0) (boundaryCol 0 (cutTail 0)) =
      acceptedVerticalMasks w 0 :=
    (split_boundary_vertical hm (acceptedGraph w) 0 (cutWidth_eq 0)).trans
      (congrFun (acceptedGraph_vertical w) 0)
  refine ⟨cutTail c, cutTail_pos c, H, hH, ?_,
    congrArg RawBoundaryState.horizontal hstate,
    congrArg RawBoundaryState.diagonal hstate, congrArg RawBoundaryState.reach hstate⟩
  exact ColumnStep.firstPrefix_eq_of_verticalMask_eq hm hH.valid
    (cutGraph_le hm (acceptedGraph_le w) 0) (hvH.trans hvR.symm)

/-- Extend one completed accepted prefix using the actual local-label witness. -/
theorem prefixCompletion_succ {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (i : Fin n)
    (hprev : PrefixCompletion w i.castSucc) : PrefixCompletion w i.succ := by
  obtain ⟨k, hk, H, hH, hP, hHor, hDiag, hReach⟩ := hprev
  obtain ⟨q, d, v, C, hC, hSource, hTarget, hV⟩ := accepted_local_realized w i
  let G := fromEdgeSet C.edgeSet
  let t := q - d.val
  have ht : 1 ≤ t := by have hd := d.isLt; dsimp [t]; omega
  have hw : d.val + 1 + (t + 1) = q + 2 := by have hd := d.isLt; dsimp [t]; omega
  have hw' : d.succ.val + 1 + t = q + 2 := by
    change d.val + 1 + 1 + t = q + 2
    omega
  let K : SimpleGraph (Vertex m (d.val + 1 + (t + 1))) := G.comap (widthEquiv hw)
  have hK : Genuine hm K := genuine_widthEquiv hm hw (genuine_of_cycle hm C hC)
  have hKS : stateAt hm (by omega) K = (acceptedCutStates w i.castSucc).val :=
    (stateAt_split_eq_cutState hm (by omega) G d.castSucc hw).trans hSource
  have hKT : stateAt hm ht (advanceGraph K) = (acceptedCutStates w i.succ).val := by
    change stateAt hm ht (advanceGraph (G.comap (widthEquiv hw))) = _
    rw [advance_comap_widthEquiv G hw hw']
    exact (stateAt_split_eq_cutState hm ht G d.succ hw').trans hTarget
  let M := mixedGraph H K
  have hM : Genuine hm M := genuine_mixed hm hk (by omega) hH hK
    (hHor.trans (congrArg RawBoundaryState.horizontal hKS).symm)
    (hDiag.trans (congrArg RawBoundaryState.diagonal hKS).symm)
    (hReach.trans (congrArg RawBoundaryState.reach hKS).symm)
  have hQ : suffixPart i.val (t + 1) M = suffixPart d.val (t + 1) K :=
    suffixPart_mixedGraph H K
  have hQnext := advance_suffix_eq hQ
  have hNewV : verticalMask hm M (nextCol (by omega)) =
      verticalMask hm K (nextCol (by omega)) := next_vertical_eq_of_suffix_eq hm hQ
  have hMH : (stateAt hm (by omega) M).horizontal = (stateAt hm (by omega) K).horizontal :=
    stateAt_mixedGraph_horizontal hm (by omega) H K
  have hMD : (stateAt hm (by omega) M).diagonal = (stateAt hm (by omega) K).diagonal :=
    stateAt_mixedGraph_diagonal hm (by omega) H K
  have hMR : (stateAt hm (by omega) M).reach = (stateAt hm (by omega) K).reach :=
    (stateAt_mixedGraph_reach hm hk (by omega) H K).trans
      (hReach.trans (congrArg RawBoundaryState.reach hKS).symm)
  have hNextH : (stateAt hm ht (advanceGraph M)).horizontal =
      (acceptedCutStates w i.succ).val.horizontal :=
    (stateAt_horizontal_eq_of_suffixPart_eq hm ht _ _ hQnext).trans
      (congrArg RawBoundaryState.horizontal hKT)
  have hNextD : (stateAt hm ht (advanceGraph M)).diagonal =
      (acceptedCutStates w i.succ).val.diagonal :=
    (stateAt_diagonal_eq_of_suffixPart_eq hm ht _ _ hQnext).trans
      (congrArg RawBoundaryState.diagonal hKT)
  have hNextR : (stateAt hm ht (advanceGraph M)).reach =
      (acceptedCutStates w i.succ).val.reach :=
    (advance_reach_eq hm ht ht hM.valid hK.valid hM.connected hK.connected
      hMH hMD hMR hNewV).trans (congrArg RawBoundaryState.reach hKT)
  let R := acceptedGraph w
  let u := cutTail i.succ
  have hu : 1 ≤ u := cutTail_pos i.succ
  have hrw : i.val + 1 + (u + 1) = n + 2 := by
    have h := cutWidth_eq i.succ
    change i.val + 1 + 1 + u = n + 2 at h
    omega
  let Rold : SimpleGraph (Vertex m (i.val + 1 + (u + 1))) := R.comap (widthEquiv hrw)
  have hRold : Rold ≤ graph m (i.val + 1 + (u + 1)) hm := by
    calc
      Rold ≤ (graph m (n + 2) hm).comap (widthEquiv hrw) :=
        SimpleGraph.comap_monotone (widthEquiv hrw).toEmbedding (acceptedGraph_le w)
      _ = _ := widthEquiv_graph_comap hm hrw
  have hRP : prefixPart i.val (u + 1) Rold =
      prefixPart i.val (cutTail i.castSucc) (cutGraph R i.castSucc) :=
    prefixPart_split_eq_cutGraph R i.castSucc hrw
  have hRH : (stateAt hm (by omega) Rold).horizontal =
      (acceptedCutStates w i.castSucc).val.horizontal :=
    (congrArg RawBoundaryState.horizontal
      (stateAt_split_eq_cutState hm (by omega) R i.castSucc hrw)).trans
      (acceptedGraph_horizontal w i.castSucc)
  have hRD : (stateAt hm (by omega) Rold).diagonal =
      (acceptedCutStates w i.castSucc).val.diagonal :=
    (congrArg RawBoundaryState.diagonal
      (stateAt_split_eq_cutState hm (by omega) R i.castSucc hrw)).trans
      (acceptedGraph_diagonal w i.castSucc)
  have hRV : verticalMask hm Rold (nextCol (by omega)) = acceptedVerticalMasks w i.succ.castSucc :=
    (split_next_vertical hm (by omega) R i.castSucc hrw).trans
      (congrFun (acceptedGraph_vertical w) i.succ.castSucc)
  have hKV : verticalMask hm K (nextCol (by omega)) = acceptedVerticalMasks w i.succ.castSucc :=
    (split_next_vertical hm (by omega) G d.castSucc hw).trans hV
  have hpnext : nextPrefix M = nextPrefix Rold := nextPrefix_eq_of_old_data hm hM.valid hRold
    ((prefixPart_mixedGraph H K).trans (hP.trans hRP.symm))
    (hMH.trans ((congrArg RawBoundaryState.horizontal hKS).trans hRH.symm))
    (hMD.trans ((congrArg RawBoundaryState.diagonal hKS).trans hRD.symm))
    (hNewV.trans (hKV.trans hRV.symm))
  have hpR : prefixPart (i.val + 1) u (advanceGraph Rold) =
      prefixPart i.succ.val (cutTail i.succ) (cutGraph R i.succ) := by
    change prefixPart (i.val + 1) u (advanceGraph (R.comap (widthEquiv hrw))) = _
    rw [advance_comap_widthEquiv R hrw (cutWidth_eq i.succ)]
    rfl
  exact ⟨t, ht, advanceGraph M, genuine_advance hm hM,
    (advance_prefix_eq_of_nextPrefix_eq hpnext).trans hpR, hNextH, hNextD, hNextR⟩

/-- Every accepted prefix admits a genuine Hamiltonian completion. -/
theorem prefixCompletion_all {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (c : Fin (n + 1)) : PrefixCompletion w c := by
  induction c using Fin.induction with
  | zero => exact prefixCompletion_zero w
  | succ i ih => exact prefixCompletion_succ w i ih

/-- The terminal witness completes the exact reconstructed graph at the
requested width. This includes accepted paths of length zero. -/
theorem acceptedGraph_genuine {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : Genuine hm (acceptedGraph w) := by
  obtain ⟨k, hk, H, hH, hP, hHor, hDiag, hReach⟩ := prefixCompletion_all w (Fin.last n)
  obtain ⟨q, v, C, hC, hState, hV, _⟩ := accepted_terminal_realized w
  let K := fromEdgeSet C.edgeSet
  have hK : Genuine hm K := genuine_of_cycle hm C hC
  have hKS : (stateAt (j := q) (k := 1) hm (by decide) K) =
      (acceptedCutStates w (Fin.last n)).val :=
    (stateAt_split_eq_cutState hm (by decide) K (Fin.last q) (by rfl)).trans hState
  let M := mixedGraph (oldPrefix := q) (k := 1) H K
  have hM : Genuine hm M := genuine_mixed hm hk (by decide) hH hK
    (hHor.trans (congrArg RawBoundaryState.horizontal hKS).symm)
    (hDiag.trans (congrArg RawBoundaryState.diagonal hKS).symm)
    (hReach.trans (congrArg RawBoundaryState.reach hKS).symm)
  let R := acceptedGraph w
  have hR : R ≤ graph m (n + 2) hm := acceptedGraph_le w
  have hRP : prefixPart n 1 R =
      prefixPart n (cutTail (Fin.last n)) (cutGraph R (Fin.last n)) :=
    prefixPart_split_eq_cutGraph R (Fin.last n) (k := 1) (by rfl)
  have hPH : prefixPart n 1 M = prefixPart n 1 R :=
    (prefixPart_mixedGraph (oldPrefix := q) (k := 1) H K).trans (hP.trans hRP.symm)
  have hRH : (stateAt (j := n) (k := 1) hm (by decide) R).horizontal =
      (acceptedCutStates w (Fin.last n)).val.horizontal :=
    (congrArg RawBoundaryState.horizontal
      (stateAt_split_eq_cutState hm (by decide) R (Fin.last n) (by rfl))).trans
      (acceptedGraph_horizontal w (Fin.last n))
  have hRD : (stateAt (j := n) (k := 1) hm (by decide) R).diagonal =
      (acceptedCutStates w (Fin.last n)).val.diagonal :=
    (congrArg RawBoundaryState.diagonal
      (stateAt_split_eq_cutState hm (by decide) R (Fin.last n) (by rfl))).trans
      (acceptedGraph_diagonal w (Fin.last n))
  have hMH : (stateAt (j := n) (k := 1) hm (by decide) M).horizontal =
      (stateAt (j := n) (k := 1) hm (by decide) R).horizontal :=
    (stateAt_mixedGraph_horizontal (oldPrefix := q) (k := 1) hm (by decide) H K).trans
      ((congrArg RawBoundaryState.horizontal hKS).trans hRH.symm)
  have hMD : (stateAt (j := n) (k := 1) hm (by decide) M).diagonal =
      (stateAt (j := n) (k := 1) hm (by decide) R).diagonal :=
    (stateAt_mixedGraph_diagonal (oldPrefix := q) (k := 1) hm (by decide) H K).trans
      ((congrArg RawBoundaryState.diagonal hKS).trans hRD.symm)
  have hMV : verticalMask hm M (nextCol (j := n) (k := 1) (by decide)) =
      verticalMask hm R (nextCol (j := n) (k := 1) (by decide)) :=
    (next_vertical_eq_of_suffix_eq (k := 0) hm
      (suffixPart_mixedGraph (oldPrefix := q) (k := 1) H K)).trans
      (hV.trans (congrFun (acceptedGraph_vertical w) (Fin.last (n + 1))).symm)
  have hQS : suffixPart n 1 M = suffixPart n 1 R :=
    ColumnStep.oneColumn_suffix_eq_of_masks_eq hm hM.valid hR hMH hMD hMV
  have hMR : M = R := by
    have hc : M.comap (vertexEquiv m n 1) = R.comap (vertexEquiv m n 1) := by
      rw [← glue_parts_eq_comap (j := n) (k := 1) hm hM.valid,
        ← glue_parts_eq_comap (j := n) (k := 1) hm hR, hPH, hQS]
    ext x y
    obtain ⟨a, rfl⟩ := (vertexEquiv m n 1).surjective x
    obtain ⟨b, rfl⟩ := (vertexEquiv m n 1).surjective y
    change (M.comap (vertexEquiv m n 1)).Adj a b ↔ (R.comap (vertexEquiv m n 1)).Adj a b
    rw [hc]
  change Genuine hm R
  rw [← hMR]
  exact hM

/-- Every accepted object has an actual standard Hamiltonian realization
with exactly its reconstructed undirected physical edge finset. -/
theorem acceptedEdges_hasHamiltonianRealization {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    CountedHamiltonian.HasHamiltonianRealization (graph m (n + 2) hm) (acceptedEdges w) := by
  obtain ⟨v, C, hC, hE⟩ := (acceptedGraph_genuine w).realized
  refine ⟨v, C, hC, ?_⟩
  apply Finset.coe_injective
  rw [CountedHamiltonian.coe_selectedEdges, hE, acceptedGraph_edgeSet]

theorem acceptedGraph_connected {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) : (acceptedGraph w).Connected :=
  (acceptedGraph_genuine w).connected

theorem acceptedGraph_neighbor_ncard_two {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (v : Vertex m (n + 2)) :
    ((acceptedGraph w).neighborSet v).ncard = 2 :=
  (acceptedGraph_genuine w).two v

#print axioms genuine_of_conditions
#print axioms genuine_of_cycle
#print axioms genuine_widthEquiv
#print axioms genuine_advance
#print axioms genuine_mixed
#print axioms split_boundary_vertical
#print axioms split_next_vertical
#print axioms prefixCompletion_zero
#print axioms prefixCompletion_succ
#print axioms prefixCompletion_all
#print axioms acceptedGraph_genuine
#print axioms acceptedEdges_hasHamiltonianRealization
#print axioms acceptedGraph_connected
#print axioms acceptedGraph_neighbor_ncard_two

end TriangularCylinder.AcceptedRealization
