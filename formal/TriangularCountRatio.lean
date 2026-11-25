import AcceptedRatio
import CountedTransferEquivalence
import CoreConnectivity
import CoreLabelFlip

/-!
# Asymptotic equality of the actual triangular-cylinder parity counts

For each fixed circumference at least three, the existing counts of
undirected Hamiltonian edge selections in the two meridian-parity classes
have ratio tending to one. The denominator is proved positive eventually.
All transfer hypotheses are supplied by the concrete core-state and label
constructions. The finite count correspondence is used only for lengths
at least three, and the finite shift is removed at the filter level.

This theorem concerns combinatorial meridian parity. Its identification
with annular contractibility, the circumference-two multigraph convention,
and an absolute spectral asymptotic expansion are separate claims.
-/

namespace TriangularCylinder.Transfer

open CountedHamiltonian Filter
open scoped Topology

noncomputable local instance {m : ℕ} (hm : 3 ≤ m) : DecidableEq (CoreState hm) :=
  Classical.decEq _

/-- Actual undirected Hamiltonian parity counts are eventually nonzero in
the denominator class and have ratio tending to one at every fixed m≥3. -/
theorem triangular_parity_ratio_limit (m : ℕ) (hm : 3 ≤ m) :
    (∀ᶠ L in atTop, 0 < parityCount m L hm 1) ∧
      Tendsto (fun L =>
        (parityCount m L hm 0 : ℝ) / (parityCount m L hm 1 : ℝ))
        atTop (𝓝 1) := by
  have hAccepted := CylinderTransfer.accepted_ratio_limit
    (S := CoreState hm) (LocalLabel hm) (InitialLabel hm)
    (TerminalLabel hm 0) (TerminalLabel hm 1)
    (coreFlipEquiv hm) (coreFlip_involutive hm)
    (fun s t => (localLabelFlipEquiv hm s t).symm)
    (fun s => by
      simpa only [ZModModule.add_self] using terminalLabelFlipEquiv hm (1 : ZMod 2) s)
    (core_path_nonempty hm) (commonCoreState m hm)
    (common_return_two m hm) (common_return_three m hm)
    (initialChoices_nonempty m hm) (terminalZeroChoices_nonempty m hm)
  have hPositiveShift : ∀ᶠ n in atTop, 0 < parityCount m (n + 2) hm 1 := by
    filter_upwards [hAccepted.1, eventually_ge_atTop (1 : ℕ)] with n hp hn
    rw [parityCount_eq_card_accepted hm hn 1]
    exact Nat.cast_pos.mp hp
  have hPositive : ∀ᶠ L in atTop, 0 < parityCount m L hm 1 := by
    have hMap : ∀ᶠ L in Filter.map (fun n : ℕ => n + 2) atTop,
        0 < parityCount m L hm 1 := Filter.eventually_map.mpr hPositiveShift
    simpa only [Filter.map_add_atTop_eq_nat] using hMap
  have hRatioEq :
      (fun n => (Fintype.card (AcceptedObject hm 0 n) : ℝ) /
          (Fintype.card (AcceptedObject hm 1 n) : ℝ)) =ᶠ[atTop]
      (fun n => (parityCount m (n + 2) hm 0 : ℝ) /
          (parityCount m (n + 2) hm 1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [parityCount_eq_card_accepted hm hn 0, parityCount_eq_card_accepted hm hn 1]
  exact ⟨hPositive,
    (Filter.tendsto_add_atTop_iff_nat 2).mp ((Filter.tendsto_congr' hRatioEq).mp hAccepted.2)⟩

/-- The reciprocal orientation, odd over even, with eventual positivity of
its denominator. This matches the manuscript's displayed count ratio. -/
theorem triangular_parity_ratio_limit_reciprocal (m : ℕ) (hm : 3 ≤ m) :
    (∀ᶠ L in atTop, 0 < parityCount m L hm 0) ∧
      Tendsto (fun L =>
        (parityCount m L hm 1 : ℝ) / (parityCount m L hm 0 : ℝ))
        atTop (𝓝 1) := by
  have h := triangular_parity_ratio_limit m hm
  have hRatioPos : ∀ᶠ L in atTop,
      0 < (parityCount m L hm 0 : ℝ) / (parityCount m L hm 1 : ℝ) :=
    h.2.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, hRatioPos] with L hden hratio
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right (Nat.cast_pos.mpr hden)).mp hratio)
  · simpa only [inv_div, inv_one] using h.2.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

end TriangularCylinder.Transfer
