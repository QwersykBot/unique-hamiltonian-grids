import NoisyCylinderLikelihood
import FiniteParityObservation
import Mathlib.Tactic.FieldSimp

/-!
# Normalized physical report masses

The fixed-report likelihood masses come from actual undirected Hamiltonian
selections. Their relative imbalance bounds the posterior under the common
edge-product prior. A finite family of reports also gives two separately
normalized report laws whose total variation is small.

The latter statement needs no probability-measure framework or normalization
of the likelihood factors: it is an exact finite-mass result. To interpret the
reports as a specified observation channel, those factors must be its actual
conditionally independent likelihoods. Separately imposing equal prior mass
on the two parity classes is not the posterior convention in the first result.
-/

open scoped BigOperators

namespace FiniteParityObservation

/-- Normalize a relative two-class imbalance using its positive pooled mass.
This is the posterior under the pooled mass, not an equal-class-prior update. -/
theorem posterior_bias_of_imbalance {a b delta : ℝ}
    (htotal : 0 < a + b) (hbound : |a - b| ≤ delta * (a + b)) :
    |a / (a + b) - (1 / 2 : ℝ)| ≤ delta / 2 := by
  have hden : 0 < 2 * (a + b) := mul_pos (by norm_num) htotal
  have heq : a / (a + b) - (1 / 2 : ℝ) = (a - b) / (2 * (a + b)) := by
    field_simp [ne_of_gt htotal]
    ring
  rw [heq, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |a - b| ≤ delta * (a + b) := hbound
    _ = delta / 2 * (2 * (a + b)) := by ring

end FiniteParityObservation

namespace TriangularCylinder.Transfer

/-- Uniform posterior parity balance for each positive-mass report. The
constants precede the length, common prior activity, and likelihood fields. -/
theorem exists_noisyParityMass_posterior_bias {m : ℕ} (hm : 3 ≤ m)
    {activityLower activityUpper ratioLower ratioUpper : ℝ}
    (hactivity : 0 < activityLower) (hratio : 0 < ratioLower) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ L : ℕ, 3 ≤ L → ∀ w q1 q0 : Sym2 (Vertex m L) → ℝ,
        (∀ e ∈ (graph m L hm).edgeSet,
          activityLower ≤ w e ∧ w e ≤ activityUpper) →
        (∀ e ∈ (graph m L hm).edgeSet, 0 < q0 e) →
        (∀ e ∈ (graph m L hm).edgeSet,
          ratioLower ≤ q1 e / q0 e ∧ q1 e / q0 e ≤ ratioUpper) →
        0 < noisyParityMass hm 0 w q1 q0 + noisyParityMass hm 1 w q1 q0 →
        |noisyParityMass hm 0 w q1 q0 /
            (noisyParityMass hm 0 w q1 q0 + noisyParityMass hm 1 w q1 q0) -
              (1 / 2 : ℝ)| ≤ rho ^ ((L - 2) / N) / 2 := by
  obtain ⟨N, hN, rho, hrho0, hrho1, hbound⟩ :=
    exists_noisyParityMass_geometric_imbalance hm
      (activityUpper := activityUpper) (ratioUpper := ratioUpper) hactivity hratio
  refine ⟨N, hN, rho, hrho0, hrho1, ?_⟩
  intro L hL w q1 q0 hw hq0 hratios htotal
  exact FiniteParityObservation.posterior_bias_of_imbalance htotal
    (hbound L hL w q1 q0 hw hq0 hratios)

/-- Uniform total variation for any finite family of physical report masses.
Both class totals are proved positive from positive pooled report mass once
one complete contraction block is available. The report alphabet, likelihoods,
and common base activity are all chosen after the constants. -/
theorem exists_noisyParityMass_report_totalVariation_bound {m : ℕ} (hm : 3 ≤ m)
    {activityLower activityUpper ratioLower ratioUpper : ℝ}
    (hactivity : 0 < activityLower) (hratio : 0 < ratioLower) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ L : ℕ, 3 ≤ L → N ≤ L - 2 →
      ∀ (X : Type) [Fintype X],
      ∀ (w : Sym2 (Vertex m L) → ℝ)
        (q1 q0 : X → Sym2 (Vertex m L) → ℝ),
        (∀ e ∈ (graph m L hm).edgeSet,
          activityLower ≤ w e ∧ w e ≤ activityUpper) →
        (∀ x e, e ∈ (graph m L hm).edgeSet → 0 < q0 x e) →
        (∀ x e, e ∈ (graph m L hm).edgeSet →
          ratioLower ≤ q1 x e / q0 x e ∧ q1 x e / q0 x e ≤ ratioUpper) →
        0 < ∑ x, (noisyParityMass hm 0 w (q1 x) (q0 x) +
          noisyParityMass hm 1 w (q1 x) (q0 x)) →
        (0 < ∑ x, noisyParityMass hm 0 w (q1 x) (q0 x)) ∧
        (0 < ∑ x, noisyParityMass hm 1 w (q1 x) (q0 x)) ∧
        (1 / 2 : ℝ) *
          (∑ x, |noisyParityMass hm 0 w (q1 x) (q0 x) /
              (∑ y, noisyParityMass hm 0 w (q1 y) (q0 y)) -
            noisyParityMass hm 1 w (q1 x) (q0 x) /
              (∑ y, noisyParityMass hm 1 w (q1 y) (q0 y))|) ≤
          rho ^ ((L - 2) / N) := by
  classical
  obtain ⟨N, hN, rho, hrho0, hrho1, hbound⟩ :=
    exists_noisyParityMass_geometric_imbalance hm
      (activityUpper := activityUpper) (ratioUpper := ratioUpper) hactivity hratio
  refine ⟨N, hN, rho, hrho0, hrho1, ?_⟩
  intro L hL hlong X _ w q1 q0 hw hq0 hratios htotal
  have hw0 : ∀ e ∈ (graph m L hm).edgeSet, 0 ≤ w e :=
    fun e he => hactivity.le.trans (hw e he).1
  have hq1 : ∀ x e, e ∈ (graph m L hm).edgeSet → 0 ≤ q1 x e := by
    intro x e he
    have hratio0 : 0 ≤ q1 x e / q0 x e := hratio.le.trans (hratios x e he).1
    have hmul := mul_nonneg hratio0 (hq0 x e he).le
    simpa only [div_mul_cancel₀ _ (ne_of_gt (hq0 x e he))] using hmul
  have hmasses (p : ZMod 2) (x : X) : 0 ≤ noisyParityMass hm p w (q1 x) (q0 x) :=
    noisyParityMass_nonneg hm p w (q1 x) (q0 x) hw0 (hq1 x)
      (fun e he => (hq0 x e he).le)
  have hk : 0 < (L - 2) / N := Nat.div_pos hlong (by omega)
  exact FiniteParityObservation.totals_pos_and_totalVariation_le
    (hmasses 0) (hmasses 1) (pow_nonneg hrho0 _)
    (pow_lt_one₀ hrho0 hrho1 (ne_of_gt hk)) htotal
    (fun x => hbound L hL w (q1 x) (q0 x) hw (hq0 x) (hratios x))

end TriangularCylinder.Transfer
