import WeightedCountImbalance
import WeightedCountPositivity
import TriangularCountRatio

/-!
# Parity-ratio limits for arbitrary length-dependent physical weights

The weight field may change arbitrarily with the total column count. Common
positive lower and finite upper bounds are required only eventually and only
on actual graph edges. Both endpoint counts are proved positive eventually;
the two ratio limits follow from the frozen scalar imbalance theorem.
-/

namespace TriangularCylinder.Transfer

open Filter CylinderMatrixContraction
open scoped Topology

/-- Actual edge-product parity counts have both ratio orientations tending
to one, under eventual common edge bounds and with eventual positivity of
both counts. No consistency between weight fields at different lengths is
required. -/
theorem weighted_parity_ratio_limits (m : ℕ) (hm : 3 ≤ m)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon)
    (w : ∀ L : ℕ, Sym2 (Vertex m L) → ℝ)
    (hw : ∀ᶠ L in atTop,
      ∀ e ∈ (graph m L hm).edgeSet, epsilon ≤ w L e ∧ w L e ≤ M) :
    (∀ᶠ L in atTop,
      0 < weightedParityCount hm 0 (w L) ∧ 0 < weightedParityCount hm 1 (w L)) ∧
      Tendsto (fun L => weightedParityCount hm 0 (w L) / weightedParityCount hm 1 (w L))
        atTop (𝓝 1) ∧
      Tendsto (fun L => weightedParityCount hm 1 (w L) / weightedParityCount hm 0 (w L))
        atTop (𝓝 1) := by
  let A : ℕ → ℝ := fun L => weightedParityCount hm 0 (w L)
  let B : ℕ → ℝ := fun L => weightedParityCount hm 1 (w L)
  have hpositive : ∀ᶠ L in atTop, 0 < A L ∧ 0 < B L := by
    filter_upwards [hw, (triangular_parity_ratio_limit_reciprocal m hm).1,
      (triangular_parity_ratio_limit m hm).1] with L hweight h₀ h₁
    have hwpos : ∀ e ∈ (graph m L hm).edgeSet, 0 < w L e :=
      fun e he => hepsilon.trans_le (hweight e he).1
    exact ⟨(weightedParityCount_pos_iff hm 0 (w L) hwpos).mpr h₀,
      (weightedParityCount_pos_iff hm 1 (w L) hwpos).mpr h₁⟩
  obtain ⟨N, hN, rho, hrho₀, hrho₁, hfinite⟩ :=
    exists_weightedParityCount_geometric_imbalance hm (M := M) hepsilon
  have hNpos : 0 < N := by omega
  have htotal : ∀ᶠ L in atTop, 0 < A L + B L := by
    filter_upwards [hpositive] with L hL
    exact add_pos hL.1 hL.2
  have hbound : ∀ᶠ L in atTop,
      |A L - B L| ≤ rho ^ ((L - 2) / N) * (A L + B L) := by
    filter_upwards [hw, eventually_ge_atTop (3 : ℕ)] with L hweight hL
    exact hfinite L hL (w L) hweight
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (htotal.and hbound)
  have hshift : Tendsto (fun n => A (n + L₀) / B (n + L₀)) atTop (𝓝 1) := by
    apply ratio_tendsto_one_of_geometric_imbalance hrho₀ hrho₁
      ((bulk_block_count_tendsto N hNpos).comp (tendsto_add_atTop_nat L₀))
    · intro n
      exact (hL₀ (n + L₀) (Nat.le_add_left _ _)).1
    · intro n
      exact (hL₀ (n + L₀) (Nat.le_add_left _ _)).2
  have hratio : Tendsto (fun L => A L / B L) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat L₀).mp hshift
  refine ⟨hpositive, hratio, ?_⟩
  simpa only [inv_div, inv_one] using hratio.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)

end TriangularCylinder.Transfer
