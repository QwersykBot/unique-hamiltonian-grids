import ColumnStepConnectivity
import ColumnFragments

/-!
# Consecutive processed prefixes in actual longer cylinders

The full processed-column graph is identified with its canonical initial
column interval. This normalization preserves the old prefix graph, its
physical outgoing masks, and the newly processed vertical mask. The checked
one-column connectivity update then applies at arbitrary consecutive cuts
of connected selected cylinder graphs, including graphs of different widths.
No processed prefix is assumed connected, and no parity claim is made.
-/

namespace TriangularCylinder.ProcessedPrefix

open SimpleGraph ColumnCut ColumnFragments BoundaryState Transfer

/-- The complete processed-column coordinates form an actual bijection. -/
def prefixCoordEquiv (m j : ℕ) : (Vertex m j ⊕ Fin m) ≃ Vertex m (j + 1) where
  toFun := prefixCoord j
  invFun x := if h : x.2.val < j then Sum.inl (x.1, ⟨x.2.val, h⟩) else Sum.inr x.1
  left_inv x := by
    cases x with
    | inl x => simp [prefixCoord, x.2.isLt]
    | inr r => simp [prefixCoord]
  right_inv x := by
    dsimp
    split_ifs with h
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        change j = x.2.val
        have hx := x.2.isLt
        omega

/-- Include the initial j+1 columns without changing any row or column label. -/
def columnInclusion {m : ℕ} (j k : ℕ) (x : Vertex m (j + 1)) :
    Vertex m (j + 1 + k) :=
  (x.1, ⟨x.2.val, by have hx := x.2.isLt; omega⟩)

theorem columnInclusion_prefixCoord {m j k : ℕ} (x : Vertex m j ⊕ Fin m) :
    columnInclusion j k (prefixCoord j x) = prefixVertex j k x := by
  cases x <;> rfl

/-- The selected graph on exactly the processed initial column interval. -/
def normalizedPrefix {m : ℕ} (j k : ℕ)
    (H : SimpleGraph (Vertex m (j + 1 + k))) : SimpleGraph (Vertex m (j + 1)) :=
  H.comap (columnInclusion j k)

/-- The normalization is isomorphic to the entire actual prefix restriction. -/
def normalizedPrefixIso {m j k : ℕ} (H : SimpleGraph (Vertex m (j + 1 + k))) :
    prefixPart j k H ≃g normalizedPrefix j k H where
  toEquiv := prefixCoordEquiv m j
  map_rel_iff' := by
    intro x y
    change H.Adj (columnInclusion j k (prefixCoord j x))
      (columnInclusion j k (prefixCoord j y)) ↔ H.Adj (prefixVertex j k x) (prefixVertex j k y)
    rw [columnInclusion_prefixCoord, columnInclusion_prefixCoord]

/-- Restricting to the initial interval preserves actual ambient validity. -/
theorem normalizedPrefix_le {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) :
    normalizedPrefix j k H ≤ graph m (j + 1) hm := by
  intro x y hxy
  have hf := forward_iff_of_coordinate_shift (d := 0)
    (x := x) (y := y) (x' := columnInclusion j k x) (y' := columnInclusion j k y)
    rfl rfl (by simp [columnInclusion]) (by simp [columnInclusion])
  have hb := forward_iff_of_coordinate_shift (d := 0)
    (x := y) (y := x) (x' := columnInclusion j k y) (y' := columnInclusion j k x)
    rfl rfl (by simp [columnInclusion]) (by simp [columnInclusion])
  exact (or_congr hf hb).mp (hH hxy)

/-- Width equality changes only the finite type, preserving the ambient graph. -/
theorem widthEquiv_graph_comap {m a b : ℕ} (hm : 3 ≤ m) (h : a = b) :
    (graph m b hm).comap (widthEquiv (m := m) h) = graph m a hm := by
  subst b
  rfl

theorem cutGraph_le {m n : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (n + 2))} (hH : H ≤ graph m (n + 2) hm)
    (c : Fin (n + 1)) : cutGraph H c ≤ graph m (c.val + 1 + cutTail c) hm := by
  calc
    cutGraph H c ≤ (graph m (n + 2) hm).comap (widthEquiv (cutWidth_eq c)) :=
      SimpleGraph.comap_monotone (widthEquiv (cutWidth_eq c)).toEmbedding hH
    _ = graph m (c.val + 1 + cutTail c) hm := widthEquiv_graph_comap hm _

/-- The fixed-width cut graph is only a change of finite column type. -/
def cutGraphIso {m n : ℕ} (H : SimpleGraph (Vertex m (n + 2)))
    (c : Fin (n + 1)) : cutGraph H c ≃g H :=
  SimpleGraph.Iso.comap (widthEquiv (cutWidth_eq c)) H

theorem cutGraph_connected {m n : ℕ}
    {H : SimpleGraph (Vertex m (n + 2))} (hH : H.Connected) (c : Fin (n + 1)) :
    (cutGraph H c).Connected :=
  hH.map (cutGraphIso H c).symm.toHom (cutGraphIso H c).symm.toEquiv.surjective

/-- The actual processed graph through the new column of a consecutive-cut step. -/
def stepPrefix {m n : ℕ} (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) :
    SimpleGraph (Vertex m (i.val + 2)) :=
  normalizedPrefix (i.val + 1) (cutTail i.succ) (cutGraph H i.succ)

theorem stepPrefix_le {m n : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (n + 2))} (hH : H ≤ graph m (n + 2) hm)
    (i : Fin n) : stepPrefix H i ≤ graph m (i.val + 2) hm :=
  normalizedPrefix_le hm (cutGraph_le hm hH i.succ)

/-- The old prefix inside the normalized graph is exactly the old actual
prefix, including every selected edge in the old boundary column. -/
theorem stepPrefix_old_prefix {m n : ℕ} (H : SimpleGraph (Vertex m (n + 2)))
    (i : Fin n) :
    prefixPart i.val 1 (stepPrefix H i) =
      prefixPart i.val (cutTail i.castSucc) (cutGraph H i.castSucc) := by
  ext x y
  cases x <;> cases y <;> rfl

/-- Actual connectedness supplies attachment for the old normalized prefix. -/
theorem stepPrefix_old_attached {m n : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (n + 2))} (hH : H ≤ graph m (n + 2) hm)
    (hconn : H.Connected) (i : Fin n) :
    CylinderFrontier.TouchesBoundary (prefixPart i.val 1 (stepPrefix H i)) := by
  rw [stepPrefix_old_prefix]
  exact prefixPart_touchesBoundary hm (cutGraph_le hm hH i.castSucc)
    (cutGraph_connected hconn i.castSucc)

/-- Old physical horizontal choices survive normalization unchanged. -/
theorem stepPrefix_old_horizontal {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) :
    (stateAt (j := i.val) (k := 1) hm (by decide) (stepPrefix H i)).horizontal =
      (cutState hm H i.castSucc).horizontal := by
  funext r
  rw [Bool.eq_iff_iff, stateAt_horizontal_iff, cutState_horizontal_iff]
  rfl

/-- Old physical diagonal choices survive normalization unchanged. -/
theorem stepPrefix_old_diagonal {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) :
    (stateAt (j := i.val) (k := 1) hm (by decide) (stepPrefix H i)).diagonal =
      (cutState hm H i.castSucc).diagonal := by
  funext r
  rw [Bool.eq_iff_iff, stateAt_diagonal_iff, cutState_diagonal_iff]
  rfl

/-- The old actual boundary relation survives normalization unchanged. -/
theorem stepPrefix_old_reach {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) :
    (stateAt (j := i.val) (k := 1) hm (by decide) (stepPrefix H i)).reach =
      (cutState hm H i.castSucc).reach := by
  funext r s
  rw [Bool.eq_iff_iff, stateAt_reach_iff, cutState_reach_iff, stepPrefix_old_prefix]
  rfl

/-- The newly processed column has exactly its original physical vertical mask. -/
theorem stepPrefix_new_vertical {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) :
    verticalMask hm (stepPrefix H i) (nextCol (j := i.val) (k := 1) (by decide)) =
      verticalMask hm H i.succ.castSucc := by
  funext r
  rw [Bool.eq_iff_iff, verticalMask_iff, verticalMask_iff]
  rfl

/-- Reachability in the actual new prefix is exactly reachability in its
normalized processed-column graph, at the corresponding new boundary rows. -/
theorem stepPrefix_new_reachable_iff {m n : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m (n + 2))) (i : Fin n) (r s : Fin m) :
    (cutState hm H i.succ).reach r s = true ↔
      (stepPrefix H i).Reachable (r, nextCol (j := i.val) (k := 1) (by decide))
        (s, nextCol (j := i.val) (k := 1) (by decide)) := by
  rw [cutState_reach_iff]
  exact (SimpleGraph.Iso.reachable_iff
    (φ := normalizedPrefixIso (cutGraph H i.succ))
    (u := Sum.inr r) (v := Sum.inr s)).symm

/-- At arbitrary consecutive cuts of connected selected cylinders, the old
physical H/D masks, old boundary relation, and new physical V mask determine
the new boundary relation. Widths and positions may differ. -/
theorem cutState_next_reach_eq {m n n' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (n + 2))} {K : SimpleGraph (Vertex m (n' + 2))}
    (hH : H ≤ graph m (n + 2) hm) (hK : K ≤ graph m (n' + 2) hm)
    (hconnH : H.Connected) (hconnK : K.Connected) (i : Fin n) (i' : Fin n')
    (hHor : (cutState hm H i.castSucc).horizontal = (cutState hm K i'.castSucc).horizontal)
    (hDiag : (cutState hm H i.castSucc).diagonal = (cutState hm K i'.castSucc).diagonal)
    (hReach : (cutState hm H i.castSucc).reach = (cutState hm K i'.castSucc).reach)
    (hV : verticalMask hm H i.succ.castSucc = verticalMask hm K i'.succ.castSucc) :
    (cutState hm H i.succ).reach = (cutState hm K i'.succ).reach := by
  have hHor' := (stepPrefix_old_horizontal hm H i).trans
    (hHor.trans (stepPrefix_old_horizontal hm K i').symm)
  have hDiag' := (stepPrefix_old_diagonal hm H i).trans
    (hDiag.trans (stepPrefix_old_diagonal hm K i').symm)
  have hReach' := (stepPrefix_old_reach hm H i).trans
    (hReach.trans (stepPrefix_old_reach hm K i').symm)
  have hV' := (stepPrefix_new_vertical hm H i).trans
    (hV.trans (stepPrefix_new_vertical hm K i').symm)
  funext r s
  rw [Bool.eq_iff_iff, stepPrefix_new_reachable_iff, stepPrefix_new_reachable_iff]
  exact ColumnStep.nextColumn_reachable_iff hm
    (stepPrefix_le hm hH i) (stepPrefix_le hm hK i')
    (stepPrefix_old_attached hm hH hconnH i) (stepPrefix_old_attached hm hK hconnK i')
    hHor' hDiag' hReach' hV' r s

/-- Full equality of old raw states is a convenient sufficient input; only
the H/D and reachability fields are used in this connectivity conclusion. -/
theorem cutState_next_reach_eq_of_state_eq {m n n' : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (n + 2))} {K : SimpleGraph (Vertex m (n' + 2))}
    (hH : H ≤ graph m (n + 2) hm) (hK : K ≤ graph m (n' + 2) hm)
    (hconnH : H.Connected) (hconnK : K.Connected) (i : Fin n) (i' : Fin n')
    (hState : cutState hm H i.castSucc = cutState hm K i'.castSucc)
    (hV : verticalMask hm H i.succ.castSucc = verticalMask hm K i'.succ.castSucc) :
    (cutState hm H i.succ).reach = (cutState hm K i'.succ).reach :=
  cutState_next_reach_eq hm hH hK hconnH hconnK i i'
    (congrArg RawBoundaryState.horizontal hState)
    (congrArg RawBoundaryState.diagonal hState)
    (congrArg RawBoundaryState.reach hState) hV

#print axioms columnInclusion_prefixCoord
#print axioms normalizedPrefix_le
#print axioms widthEquiv_graph_comap
#print axioms cutGraph_le
#print axioms cutGraph_connected
#print axioms stepPrefix_le
#print axioms stepPrefix_old_prefix
#print axioms stepPrefix_old_attached
#print axioms stepPrefix_old_horizontal
#print axioms stepPrefix_old_diagonal
#print axioms stepPrefix_old_reach
#print axioms stepPrefix_new_vertical
#print axioms stepPrefix_new_reachable_iff
#print axioms cutState_next_reach_eq
#print axioms cutState_next_reach_eq_of_state_eq

end TriangularCylinder.ProcessedPrefix
