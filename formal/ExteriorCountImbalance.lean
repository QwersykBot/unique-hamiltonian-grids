import ExteriorEncoding
import ExteriorSymmetry
import WindowProduct
import CoreConnectivity
import AcceptedRatio

/-!
# Uniform parity imbalance after fixing the physical exterior

For fixed circumference and common positive global bounds on physical edge
activities, the constants are uniform over the length, free interval,
complete exterior prescription and activity field. The free local slots
`[a,b)` own `H_i,D_i,V_(i+1)`. All other physical edges have both their
selected and absent values prescribed by the same `σ` for both parities.

The counted objects are the original fixed-labelled unordered Hamiltonian
edge selections. Impossible prescriptions are allowed. This is a finite
unnormalized mass inequality; neither positive mass nor a normalized law
on the redundant total-geometry prescription type is asserted.
-/

namespace TriangularCylinder.Transfer

open CylinderTransfer CylinderMatrixContraction WeightedCylinderBounds TriangularEdgeEncoding
open scoped BigOperators Matrix

/-- Uniform geometric relative imbalance for actual physical weighted counts
with a complete exterior prescription. Constants are chosen before the
length, free interval, prescription and physical activity field. -/
theorem exists_exteriorParityCount_geometric_imbalance {m : ℕ} (hm : 3 ≤ m)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ a b : ℕ, a ≤ b → b ≤ n →
      ∀ σ : ColumnGeometry m (n + 2), ∀ w : Sym2 (Vertex m (n + 2)) → ℝ,
        (∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M) →
        |exteriorParityCount hm 0 w σ a b - exteriorParityCount hm 1 w σ a b| ≤
          rho ^ ((b - a) / N) *
            (exteriorParityCount hm 0 w σ a b + exteriorParityCount hm 1 w σ a b) := by
  classical
  let T : Matrix (CoreState hm) (CoreState hm) ℝ := realTransitionMatrix (LocalLabel hm)
  have hT : ∀ s t, 0 ≤ T s t := fun _ _ => Nat.cast_nonneg _
  have hconnected : ∀ s t, ∃ k, 0 < (T ^ k) s t := by
    intro s t
    obtain ⟨k, hk⟩ := core_path_nonempty hm s t
    exact ⟨k, (realTransitionMatrix_pow_pos_iff (LocalLabel hm) k s t).mpr hk⟩
  have htwo : 0 < (T ^ 2) (commonCoreState m hm) (commonCoreState m hm) :=
    (realTransitionMatrix_pow_pos_iff (LocalLabel hm) 2 _ _).mpr (common_return_two m hm)
  have hthree : 0 < (T ^ 3) (commonCoreState m hm) (commonCoreState m hm) :=
    (realTransitionMatrix_pow_pos_iff (LocalLabel hm) 3 _ _).mpr (common_return_three m hm)
  obtain ⟨hlo, hlohi⟩ := constants_pos_le m (M := M) hepsilon
  obtain ⟨N, hN, rho, hrho₀, hrho₁, hbound⟩ :=
    uniform_window_imbalance_of_support hT hconnected (commonCoreState m hm)
      htwo hthree (coreFlipEquiv hm) (coreFlip_involutive hm) hlo hlohi
  refine ⟨N, hN, rho, hrho₀, hrho₁, ?_⟩
  intro n hn a b hab hbn σ w hw
  let f := exteriorInitialVector hm w σ
  let g := exteriorTerminalVector hm 0 w σ
  have hg₁ : exteriorTerminalVector hm 1 w σ = fun s => g (coreFlipEquiv hm s) := by
    funext s
    exact exteriorTerminalVector_one_eq_zero_flip hm w σ s
  have hcount₀ : exteriorParityCount hm 0 w σ a b =
      f ⬝ᵥ ((List.ofFn (exteriorLocalMatrix hm w σ a b)).prod *ᵥ g) :=
    exteriorParityCount_eq_orderedProduct hm hn 0 w σ a b hbn
  have hcount₁ : exteriorParityCount hm 1 w σ a b =
      f ⬝ᵥ ((List.ofFn (exteriorLocalMatrix hm w σ a b)).prod *ᵥ
        fun s => g (coreFlipEquiv hm s)) := by
    simpa only [hg₁] using
      exteriorParityCount_eq_orderedProduct hm hn 1 w σ a b hbn
  have hfinite := hbound n a b hab hbn (exteriorLocalMatrix hm w σ a b)
    (fun i s t => exteriorLocalMatrix_nonneg hm w σ hepsilon hw a b i s t)
    (fun i s t => exteriorLocalMatrix_flip hm w σ a b i s t)
    (by
      intro i hai hib s t hst
      rw [exteriorLocalMatrix_eq_unfiltered hm w σ a b i ⟨hai, hib⟩]
      exact weightedTransitionMatrix_lower hm w hepsilon hw i s t hst)
    (by
      intro i hai hib s t
      rw [exteriorLocalMatrix_eq_unfiltered hm w σ a b i ⟨hai, hib⟩]
      exact weightedTransitionMatrix_upper hm w hepsilon hw i s t)
    f g
    (fun s => exteriorInitialVector_nonneg hm w σ hepsilon hw s)
    (fun s => exteriorTerminalVector_nonneg hm w σ hepsilon hw 0 s)
  simpa only [← hcount₀, ← hcount₁] using hfinite

#print axioms exists_exteriorParityCount_geometric_imbalance

end TriangularCylinder.Transfer
