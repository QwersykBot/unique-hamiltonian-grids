import CycleIntervals
import CompletionTransport

/-!
# Paths between two concrete stateAt occurrences in one cycle

The physical cylinder width and both cut splits may be presented with
different natural-number expressions. Converting the two split encoders
to the actual indexed cut sequence gives a path of exactly the difference
of cut positions. Every intermediate label comes from this same cycle.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph BoundaryState CompletionTransport

/-- Two ordered encoded cuts of one actual longer cycle give an exact labelled path. -/
theorem path_between_stateAt {m L j k j' k' : ℕ} (hm : 3 ≤ m) (hL : 3 ≤ L)
    (hk : 1 ≤ k) (hk' : 1 ≤ k') (hw : j + 1 + k = L) (hw' : j' + 1 + k' = L)
    (horder : j ≤ j') {v : Vertex m L} (C : (graph m L hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (s t : CoreState hm)
    (hs : stateAt hm hk ((fromEdgeSet C.edgeSet).comap (widthEquiv hw)) = s.val)
    (ht : stateAt hm hk' ((fromEdgeSet C.edgeSet).comap (widthEquiv hw')) = t.val) :
    Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) (j' - j) s t) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 2 := ⟨L - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  let a : Fin (n + 1) := ⟨j, by omega⟩
  let b : Fin (n + 1) := ⟨j', by omega⟩
  have ha : coreAtCut hm hn C hC a = s := by
    apply Subtype.ext
    exact (stateAt_split_eq_cutState hm hk (fromEdgeSet C.edgeSet) a hw).symm.trans hs
  have hb : coreAtCut hm hn C hC b = t := by
    apply Subtype.ext
    exact (stateAt_split_eq_cutState hm hk' (fromEdgeSet C.edgeSet) b hw').symm.trans ht
  have hp := cycleIntervalPath_nonempty hm hn C hC a b horder
  rw [ha, hb] at hp
  exact hp

end TriangularCylinder.Transfer
