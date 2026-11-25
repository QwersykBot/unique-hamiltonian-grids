import WeightedCountTransfer
import WeightedCylinderSymmetry
import WeightedCylinderBounds
import CoreConnectivity
import AcceptedRatio

/-!
# Uniform relative imbalance for actual physical weighted counts

For fixed circumference and common positive edge bounds, one block length
and contraction constant work for every cylinder length and every admissible
physical weight field. Weights may vary independently by row and column.
Only actual ambient edges are bounded; no translation symmetry is assumed.
-/

namespace TriangularCylinder.Transfer

open CylinderTransfer CylinderMatrixContraction WeightedCylinderBounds
open scoped BigOperators Matrix

/-- Uniform geometric relative imbalance for the existing edge-product
weighted counts. Constants are chosen before the length and weight field. -/
theorem exists_weightedParityCount_geometric_imbalance {m : ℕ} (hm : 3 ≤ m)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ L : ℕ, 3 ≤ L → ∀ w : Sym2 (Vertex m L) → ℝ,
        (∀ e ∈ (graph m L hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M) →
        |weightedParityCount hm 0 w - weightedParityCount hm 1 w| ≤
          rho ^ ((L - 2) / N) *
            (weightedParityCount hm 0 w + weightedParityCount hm 1 w) := by
  classical
  let T : Matrix (CoreState hm) (CoreState hm) ℝ := realTransitionMatrix (LocalLabel hm)
  have hT : ∀ s t, 0 ≤ T s t := fun _ _ => Nat.cast_nonneg _
  have hconnected : ∀ s t, ∃ n, 0 < (T ^ n) s t := by
    intro s t
    obtain ⟨n, hn⟩ := core_path_nonempty hm s t
    exact ⟨n, (realTransitionMatrix_pow_pos_iff (LocalLabel hm) n s t).mpr hn⟩
  have htwo : 0 < (T ^ 2) (commonCoreState m hm) (commonCoreState m hm) :=
    (realTransitionMatrix_pow_pos_iff (LocalLabel hm) 2 _ _).mpr (common_return_two m hm)
  have hthree : 0 < (T ^ 3) (commonCoreState m hm) (commonCoreState m hm) :=
    (realTransitionMatrix_pow_pos_iff (LocalLabel hm) 3 _ _).mpr (common_return_three m hm)
  obtain ⟨ha, hab⟩ := constants_pos_le m (M := M) hepsilon
  obtain ⟨N, hN, rho, hrho₀, hrho₁, hbound⟩ :=
    uniform_finite_imbalance_of_support hT hconnected (commonCoreState m hm)
      htwo hthree (coreFlipEquiv hm) (coreFlip_involutive hm) ha hab
  refine ⟨N, hN, rho, hrho₀, hrho₁, ?_⟩
  intro L hL
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 2 := ⟨L - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  intro w hw
  let f := initialPhysicalVector hm w
  let g := terminalPhysicalVector hm 0 w
  have hg₁ : terminalPhysicalVector hm 1 w = fun s => g (coreFlipEquiv hm s) := by
    funext s
    exact weightedTerminalVector_one_eq_zero_flip hm w s
  have hcount₀ : weightedParityCount hm 0 w =
      f ⬝ᵥ ((List.ofFn (localPhysicalMatrix hm w)).prod *ᵥ g) :=
    weightedParityCount_eq_ordered_transfer hm hn 0 w
  have hcount₁ : weightedParityCount hm 1 w =
      f ⬝ᵥ ((List.ofFn (localPhysicalMatrix hm w)).prod *ᵥ
        fun s => g (coreFlipEquiv hm s)) := by
    simpa only [hg₁] using weightedParityCount_eq_ordered_transfer hm hn 1 w
  have hfinite := hbound (List.ofFn (localPhysicalMatrix hm w))
    (by
      intro B hB s t
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hB
      exact weightedTransitionMatrix_nonneg hm w hepsilon hw i s t)
    (by
      intro B hB s t hst
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hB
      exact weightedTransitionMatrix_lower hm w hepsilon hw i s t hst)
    (by
      intro B hB s t
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hB
      exact weightedTransitionMatrix_upper hm w hepsilon hw i s t)
    (by
      intro B hB s t
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hB
      exact weightedTransitionMatrix_flip hm w i s t)
    f g
    (fun s => weightedInitialVector_nonneg hm w hepsilon hw s)
    (fun s => weightedTerminalVector_nonneg hm w hepsilon hw 0 s)
  simpa only [List.length_ofFn, ← hcount₀, ← hcount₁, Nat.add_sub_cancel_right]
    using hfinite

end TriangularCylinder.Transfer
