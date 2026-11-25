import MatrixContraction.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Scalar and matrix-family ratio limits

These are consequences of the checked finite imbalance estimate. No cylinder
state/cycle correspondence or block-positivity theorem is assumed to have been
formalized here.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace CylinderMatrixContraction

/-- A vanishing relative imbalance forces either normalized endpoint to one half. -/
theorem probability_tendsto_half_of_imbalance
    {z₀ z₁ ε : ℕ → ℝ}
    (htotal : ∀ n, 0 < z₀ n + z₁ n)
    (himbalance : ∀ n, |z₀ n - z₁ n| ≤ ε n * (z₀ n + z₁ n))
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => z₀ n / (z₀ n + z₁ n)) atTop (𝓝 (1 / 2)) := by
  have habs : Tendsto (fun n => |z₀ n / (z₀ n + z₁ n) - 1 / 2|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun n => probability_deviation_bound (htotal n) (himbalance n))
    simpa using hε.div_const 2
  have hdiff : Tendsto (fun n => z₀ n / (z₀ n + z₁ n) - 1 / 2) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (1 / 2 : ℝ)

/-- The real ratio limit follows from a vanishing relative imbalance and
a positive total. It does not assume that either endpoint has a growth rate. -/
theorem ratio_tendsto_one_of_imbalance
    {z₀ z₁ ε : ℕ → ℝ}
    (htotal : ∀ n, 0 < z₀ n + z₁ n)
    (himbalance : ∀ n, |z₀ n - z₁ n| ≤ ε n * (z₀ n + z₁ n))
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => z₀ n / z₁ n) atTop (𝓝 1) := by
  have h₀ := probability_tendsto_half_of_imbalance htotal himbalance hε
  have htotal' : ∀ n, 0 < z₁ n + z₀ n := by
    intro n
    simpa only [add_comm] using htotal n
  have himbalance' : ∀ n, |z₁ n - z₀ n| ≤ ε n * (z₁ n + z₀ n) := by
    intro n
    simpa only [abs_sub_comm, add_comm] using himbalance n
  have h₁ : Tendsto (fun n => z₁ n / (z₀ n + z₁ n)) atTop (𝓝 (1 / 2)) := by
    simpa only [add_comm] using
      probability_tendsto_half_of_imbalance htotal' himbalance' hε
  have hhalf : (1 / 2 : ℝ) ≠ 0 := div_ne_zero one_ne_zero two_ne_zero
  have hquot := h₀.div h₁ hhalf
  change Tendsto (fun n => z₀ n / (z₀ n + z₁ n) / (z₁ n / (z₀ n + z₁ n)))
    atTop (𝓝 ((1 / 2 : ℝ) / (1 / 2))) at hquot
  have heq : (fun n => z₀ n / (z₀ n + z₁ n) / (z₁ n / (z₀ n + z₁ n))) =
      (fun n => z₀ n / z₁ n) := by
    funext n
    exact div_div_div_cancel_right₀ (ne_of_gt (htotal n)) _ _
  rw [heq] at hquot
  simpa only [div_self hhalf] using hquot

/-- The number of positive blocks may grow along any sequence tending to infinity. -/
theorem ratio_tendsto_one_of_geometric_imbalance
    {z₀ z₁ : ℕ → ℝ} {k : ℕ → ℕ} {ρ : ℝ}
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hk : Tendsto k atTop atTop)
    (htotal : ∀ n, 0 < z₀ n + z₁ n)
    (himbalance : ∀ n, |z₀ n - z₁ n| ≤ ρ ^ k n * (z₀ n + z₁ n)) :
    Tendsto (fun n => z₀ n / z₁ n) atTop (𝓝 1) :=
  ratio_tendsto_one_of_imbalance htotal himbalance
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ₁).comp hk)

/-- The elementary block-count growth used when two columns are endpoints.
Natural-number division is the floor of the nonnegative quotient. -/
theorem bulk_block_count_tendsto (N : ℕ) (hN : 0 < N) :
    Tendsto (fun L : ℕ => (L - 2) / N) atTop atTop :=
  (Nat.tendsto_div_const_atTop (ne_of_gt hN)).comp (tendsto_sub_atTop_nat 2)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fully generic matrix-family ratio limit. Every environment, residual,
and boundary may depend on `n`. Uniform positive block bounds, the common
involution, a positive total, and divergence of the number of blocks suffice. -/
theorem matrix_family_ratio_tendsto_one
    (u : Equiv.Perm ι) (hu : Function.Involutive u)
    (blocks : ℕ → List (Matrix ι ι ℝ)) (R : ℕ → Matrix ι ι ℝ)
    (f g : ℕ → ι → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsym : ∀ n B, B ∈ blocks n → SymmetricUnder u B)
    (hlower : ∀ n B, B ∈ blocks n → ∀ i j, a ≤ B i j)
    (hupper : ∀ n B, B ∈ blocks n → ∀ i j, B i j ≤ b)
    (hRsym : ∀ n, SymmetricUnder u (R n))
    (hR : ∀ n i j, 0 ≤ R n i j)
    (hf : ∀ n i, 0 ≤ f n i) (hg : ∀ n i, 0 ≤ g n i)
    (htotal : ∀ n, 0 <
      (f n ⬝ᵥ (((blocks n).prod * R n) *ᵥ g n)) +
      (f n ⬝ᵥ (((blocks n).prod * R n) *ᵥ (fun i => g n (u i)))))
    (hlength : Tendsto (fun n => (blocks n).length) atTop atTop) :
    Tendsto (fun n =>
      (f n ⬝ᵥ (((blocks n).prod * R n) *ᵥ g n)) /
      (f n ⬝ᵥ (((blocks n).prod * R n) *ᵥ (fun i => g n (u i)))))
      atTop (𝓝 1) := by
  apply ratio_tendsto_one_of_geometric_imbalance (rho_nonneg ha hab)
    (rho_lt_one ha hab) hlength htotal
  intro n
  exact endpoint_contraction u hu (blocks n) (R n) ha hab (hsym n)
    (hlower n) (hupper n) (hRsym n) (hR n) (hf n) (hg n)

end CylinderMatrixContraction
