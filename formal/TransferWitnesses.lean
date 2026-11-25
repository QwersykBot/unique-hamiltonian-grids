import ActualTransfer
import CommonWitnessState

/-!
# Actual initial and zero-parity terminal choices

The concrete common witness state lies in the nonfull occurring-state core.
The already constructed two-column perimeter cycle supplies both an initial
vertical-mask label and a terminal label of total parity zero at that state.
No transfer return, support connectivity, or parity-flip closure is assumed.
-/

namespace TriangularCylinder.Transfer

open SimpleGraph BoundaryState

/-- The concrete common state is not the full outgoing H/D configuration. -/
theorem commonWitnessState_not_full (m : ℕ) (hm : 3 ≤ m) :
    ¬ FullOutgoing (commonWitnessState m hm) := by
  intro h
  have hd := (h (⟨0, by omega⟩ : Fin m)).2
  cases hd

/-- The same concrete common state, with actual occurrence and nonfullness. -/
noncomputable def commonCoreState (m : ℕ) (hm : 3 ≤ m) : CoreState hm :=
  ⟨commonWitnessState m hm, commonWitnessState_occurs m hm,
    commonWitnessState_not_full m hm⟩

@[simp] theorem commonCoreState_val (m : ℕ) (hm : 3 ≤ m) :
    (commonCoreState m hm).val = commonWitnessState m hm := rfl

/-- At the sole cut of two columns, the indexed wrapper is the original encoder. -/
theorem cutState_two_columns {m : ℕ} (hm : 3 ≤ m)
    (H : SimpleGraph (Vertex m 2)) :
    cutState (n := 0) hm H 0 = stateAt (j := 0) (k := 1) hm (by decide) H := by
  change stateAt (j := 0) (k := 1) hm (by decide) (H.comap id) = _
  rw [SimpleGraph.comap_id]

/-- The actual perimeter cycle supplies an initial choice at the common state. -/
theorem initialLabel_common_nonempty (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (InitialLabel hm (commonCoreState m hm)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  let C := perimeterCycle n hn
  refine ⟨⟨verticalMask hm (fromEdgeSet C.edgeSet) 0, ?_⟩⟩
  refine ⟨0, _, C, perimeterCycle_isHamiltonianCycle n hn, ?_, rfl⟩
  rw [cutState_two_columns]
  exact perimeterCycle_stateAt_common n hn

/-- The same actual cycle supplies a terminal choice of total parity zero. -/
theorem terminalZeroLabel_common_nonempty (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (TerminalLabel hm 0 (commonCoreState m hm)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  let C := perimeterCycle n hn
  refine ⟨⟨verticalMask hm (fromEdgeSet C.edgeSet) (Fin.last 1), ?_⟩⟩
  refine ⟨0, _, C, perimeterCycle_isHamiltonianCycle n hn, ?_, rfl, ?_⟩
  · change cutState hm (fromEdgeSet C.edgeSet) 0 = _
    rw [cutState_two_columns]
    exact perimeterCycle_stateAt_common n hn
  · exact perimeterCycle_typeParity n hn

theorem initialChoices_nonempty (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (Σ s : CoreState hm, InitialLabel hm s) := by
  obtain ⟨a⟩ := initialLabel_common_nonempty m hm
  exact ⟨⟨commonCoreState m hm, a⟩⟩

theorem terminalZeroChoices_nonempty (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (Σ s : CoreState hm, TerminalLabel hm 0 s) := by
  obtain ⟨a⟩ := terminalZeroLabel_common_nonempty m hm
  exact ⟨⟨commonCoreState m hm, a⟩⟩

end TriangularCylinder.Transfer
