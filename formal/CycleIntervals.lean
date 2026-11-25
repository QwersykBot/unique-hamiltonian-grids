import ActualTransfer
import FiniteTransferPaths

/-!
# Exact labelled paths along intervals of one actual cycle

Restrict the actual cut sequence to two ordered nonterminal cuts. Every
local label is supplied by the same Hamiltonian cycle, in increasing column
order. The length is exactly the difference of cut values, including zero.
Endpoint transport changes only proofs, and uniform label observations
retain the selected physical vertical masks of the original cycle.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph

/-- Include an interval's cut indices into the actual full cut sequence. -/
def cutIntervalIndex {n : ℕ} (a b : Fin (n + 1)) (hab : a.val ≤ b.val)
    (i : Fin (b.val - a.val + 1)) : Fin (n + 1) :=
  ⟨a.val + i.val, by have hi := i.isLt; have hb := b.isLt; omega⟩

@[simp] theorem cutIntervalIndex_val {n : ℕ} (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) (i : Fin (b.val - a.val + 1)) :
    (cutIntervalIndex a b hab i).val = a.val + i.val := rfl

@[simp] theorem cutIntervalIndex_zero {n : ℕ} (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) : cutIntervalIndex a b hab 0 = a := by
  apply Fin.ext
  simp only [cutIntervalIndex_val, Fin.val_zero, Nat.add_zero]

@[simp] theorem cutIntervalIndex_last {n : ℕ} (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) : cutIntervalIndex a b hab (Fin.last (b.val - a.val)) = b := by
  apply Fin.ext
  simp only [cutIntervalIndex_val, Fin.val_last]
  omega

/-- Each interval step is an actual step between consecutive full cut indices. -/
def cutIntervalStep {n : ℕ} (a b : Fin (n + 1)) (hab : a.val ≤ b.val)
    (i : Fin (b.val - a.val)) : Fin n :=
  ⟨a.val + i.val, by have hi := i.isLt; have hb := b.isLt; omega⟩

@[simp] theorem cutIntervalStep_val {n : ℕ} (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) (i : Fin (b.val - a.val)) :
    (cutIntervalStep a b hab i).val = a.val + i.val := rfl

@[simp] theorem cutIntervalIndex_castSucc {n : ℕ} (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) (i : Fin (b.val - a.val)) :
    cutIntervalIndex a b hab i.castSucc = (cutIntervalStep a b hab i).castSucc := rfl

@[simp] theorem cutIntervalIndex_succ {n : ℕ} (a b : Fin (n + 1))
    (hab : a.val ≤ b.val) (i : Fin (b.val - a.val)) :
    cutIntervalIndex a b hab i.succ = (cutIntervalStep a b hab i).succ := rfl

private def transportEndpoints {S : Type*} {E : S → S → Type*}
    {l : ℕ} {s t s' t' : S} (hs : s = s') (ht : t = t')
    (path : CylinderTransfer.LabelledPath E l s t) :
    CylinderTransfer.LabelledPath E l s' t' := by
  cases hs
  cases ht
  exact path

private theorem observe_transportEndpoints {S : Type*} {E : S → S → Type*} {W : Type*}
    (value : ∀ s t, E s t → W) {l : ℕ} {s t s' t' : S} (hs : s = s') (ht : t = t')
    (path : CylinderTransfer.LabelledPath E l s t) :
    CylinderTransfer.LabelledPath.observe value (transportEndpoints hs ht path) =
      CylinderTransfer.LabelledPath.observe value path := by
  cases hs
  cases ht
  rfl

/-- The actual cycle supplies a path of exactly `b.val-a.val` labels from cut `a` to cut `b`. -/
noncomputable def cycleIntervalPath {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a b : Fin (n + 1)) (hab : a.val ≤ b.val) :
    CylinderTransfer.LabelledPath (LocalLabel hm) (b.val - a.val)
      (coreAtCut hm hn C hC a) (coreAtCut hm hn C hC b) :=
  transportEndpoints
    (congrArg (coreAtCut hm hn C hC) (cutIntervalIndex_zero a b hab))
    (congrArg (coreAtCut hm hn C hC) (cutIntervalIndex_last a b hab))
    (CylinderTransfer.LabelledPath.ofSequence (LocalLabel hm) (b.val - a.val)
      (fun i => coreAtCut hm hn C hC (cutIntervalIndex a b hab i))
      (fun i => localLabelOfCycle hm hn C hC (cutIntervalStep a b hab i)))

/-- Every uniform observation retains precisely the original cycle's corresponding local label. -/
theorem cycleIntervalPath_observe {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a b : Fin (n + 1)) (hab : a.val ≤ b.val)
    {W : Type*} (value : ∀ s t, LocalLabel hm s t → W) :
    CylinderTransfer.LabelledPath.observe value (cycleIntervalPath hm hn C hC a b hab) =
      fun i => value _ _ (localLabelOfCycle hm hn C hC (cutIntervalStep a b hab i)) := by
  unfold cycleIntervalPath
  rw [observe_transportEndpoints, CylinderTransfer.LabelledPath.observe_ofSequence]
  rfl

/-- The interval observes the actual V mask in column `a.val+i.val+1`, in that order. -/
theorem cycleIntervalPath_verticalMasks {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a b : Fin (n + 1)) (hab : a.val ≤ b.val) :
    CylinderTransfer.LabelledPath.observe (fun _ _ e => e.val)
      (cycleIntervalPath hm hn C hC a b hab) =
      fun i => verticalMask hm (SimpleGraph.fromEdgeSet C.edgeSet)
        (cutIntervalStep a b hab i).succ.castSucc := by
  rw [cycleIntervalPath_observe]
  rfl

/-- The target observation is the next actual cut in the same interval. -/
theorem cycleIntervalPath_targetStates {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a b : Fin (n + 1)) (hab : a.val ≤ b.val) :
    CylinderTransfer.LabelledPath.observe (fun _ t _ => t)
      (cycleIntervalPath hm hn C hC a b hab) =
      fun i => coreAtCut hm hn C hC (cutIntervalIndex a b hab i.succ) := by
  rw [cycleIntervalPath_observe]
  rfl

/-- Ordered cuts of an actual cycle therefore give an exact-length inhabited transfer path. -/
theorem cycleIntervalPath_nonempty {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a b : Fin (n + 1)) (hab : a.val ≤ b.val) :
    Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) (b.val - a.val)
      (coreAtCut hm hn C hC a) (coreAtCut hm hn C hC b)) :=
  ⟨cycleIntervalPath hm hn C hC a b hab⟩

/-- Coincident cuts give the required zero-length path, with no local label added. -/
theorem cycleIntervalPath_nonempty_self {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {v : Vertex m (n + 2)} (C : (graph m (n + 2) hm).Walk v v)
    (hC : C.IsHamiltonianCycle) (a : Fin (n + 1)) :
    Nonempty (CylinderTransfer.LabelledPath (LocalLabel hm) 0
      (coreAtCut hm hn C hC a) (coreAtCut hm hn C hC a)) := by
  simpa only [Nat.sub_self] using cycleIntervalPath_nonempty hm hn C hC a a (Nat.le_refl _)

end TriangularCylinder.Transfer
