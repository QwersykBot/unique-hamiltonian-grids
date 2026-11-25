import CanonicalExteriorObservation
import ExteriorCountImbalance
import FiniteParityObservation

/-!
# Normalized physical exterior observations

Canonical codes describe every selected and absent exterior edge exactly
once. Their masses partition the original physical weighted parity count,
so the normalization below uses the original class partition functions.
Impossible codes remain in the sum with zero mass.

One complete contraction block in the free interval and positive pooled
physical mass force both class totals to be positive. The resulting total
variation bound is uniform over the position of the interval and all common
activity fields within the fixed positive bounds.
-/

open scoped BigOperators

namespace TriangularCylinder.Transfer

open CountedHamiltonian TriangularEdgeEncoding

/-- Nonnegative actual physical activities give nonnegative exterior mass,
without requiring a valid interval or a realizable exterior prescription. -/
theorem exteriorParityCount_nonneg {m n : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (σ : ColumnGeometry m (n + 2)) (a b : ℕ)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, 0 ≤ w e) :
    0 ≤ exteriorParityCount hm p w σ a b := by
  classical
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg
  · exact Finset.prod_nonneg
      (fun e he => hw e (selection_edge_mem (graph m (n + 2) hm) s.val he))
  · unfold exteriorIndicator
    split <;> norm_num

/-- The two parity classes induce close laws on the uniquely coded physical
exterior. Their denominators are the original weighted parity counts, not
sums over redundant free-bit descriptions. Constants precede the length,
interval and shared field; positivity of both denominators is a conclusion. -/
theorem exists_exteriorParityCount_totalVariation_bound {m : ℕ} (hm : 3 ≤ m)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ a b : ℕ, a ≤ b → b ≤ n → N ≤ b - a →
      ∀ w : Sym2 (Vertex m (n + 2)) → ℝ,
        (∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M) →
        0 < weightedParityCount hm 0 w + weightedParityCount hm 1 w →
        0 < weightedParityCount hm 0 w ∧
        0 < weightedParityCount hm 1 w ∧
        (1 / 2 : ℝ) *
          (∑ σ : CanonicalExteriorCode m n a b,
            |exteriorParityCount hm 0 w σ.val a b / weightedParityCount hm 0 w -
              exteriorParityCount hm 1 w σ.val a b / weightedParityCount hm 1 w|) ≤
          rho ^ ((b - a) / N) := by
  classical
  obtain ⟨N, hN, rho, hrho0, hrho1, hbound⟩ :=
    exists_exteriorParityCount_geometric_imbalance hm (M := M) hepsilon
  refine ⟨N, hN, rho, hrho0, hrho1, ?_⟩
  intro n hn a b hab hbn hlong w hw htotal
  have hw0 : ∀ e ∈ (graph m (n + 2) hm).edgeSet, 0 ≤ w e :=
    fun e he => hepsilon.le.trans (hw e he).1
  have hmasses (p : ZMod 2) (σ : CanonicalExteriorCode m n a b) :
      0 ≤ exteriorParityCount hm p w σ.val a b :=
    exteriorParityCount_nonneg hm p w σ.val a b hw0
  have htotal' : 0 < ∑ σ : CanonicalExteriorCode m n a b,
      (exteriorParityCount hm 0 w σ.val a b + exteriorParityCount hm 1 w σ.val a b) := by
    simpa only [Finset.sum_add_distrib, sum_exteriorParityCount] using htotal
  have hk : 0 < (b - a) / N := Nat.div_pos hlong (by omega)
  have hresult := FiniteParityObservation.totals_pos_and_totalVariation_le
    (hmasses 0) (hmasses 1) (pow_nonneg hrho0 _)
    (pow_lt_one₀ hrho0 hrho1 (ne_of_gt hk)) htotal'
    (fun σ => hbound n hn a b hab hbn σ.val w hw)
  simpa only [sum_exteriorParityCount] using hresult

end TriangularCylinder.Transfer
