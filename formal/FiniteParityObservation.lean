import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A sharp finite total-variation bound from relative imbalance

Two nonnegative masses on a finite type obey the same pointwise relative
imbalance bound. If their pooled total is positive and the imbalance is less
than one, both totals are positive, and normalizing the two masses gives total
variation at most the original imbalance. No probability or measure interface
is used; zero-mass atoms and zero imbalance are included.
-/

open scoped BigOperators

namespace FiniteParityObservation

private theorem scaled_abs_cross_le {δ H D h d : ℝ}
    (hδ : 0 ≤ δ) (hD : |D| ≤ δ * H) (hd : |d| ≤ δ * h) :
    δ * |H * d - D * h| ≤ δ ^ 2 * H * h - D * d := by
  obtain ⟨hDlo, hDhi⟩ := abs_le.mp hD
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  have hplus : 0 ≤ (δ * H + D) * (δ * h - d) :=
    mul_nonneg (by linarith) (by linarith)
  have hminus : 0 ≤ (δ * H - D) * (δ * h + d) :=
    mul_nonneg (by linarith) (by linarith)
  have hcross : |δ * (H * d - D * h)| ≤ δ ^ 2 * H * h - D * d := by
    apply abs_le.mpr
    constructor
    · nlinarith only [hminus]
    · nlinarith only [hplus]
  simpa only [abs_mul, abs_of_nonneg hδ] using hcross

/-- A pointwise relative imbalance below one forces positive class totals and
bounds the total variation between their separately normalized masses by the
same constant. The constant is sharp, already for two atoms. -/
theorem totals_pos_and_totalVariation_le
    {X : Type*} [Fintype X] {a b : X → ℝ} {δ : ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (htotal : 0 < ∑ x, (a x + b x))
    (hpoint : ∀ x, |a x - b x| ≤ δ * (a x + b x)) :
    (0 < ∑ x, a x) ∧ (0 < ∑ x, b x) ∧
      (1 / 2 : ℝ) * (∑ x, |a x / (∑ y, a y) - b x / (∑ y, b y)|) ≤ δ := by
  classical
  let A := ∑ x, a x
  let B := ∑ x, b x
  have htotal' : 0 < A + B := by
    simpa only [Finset.sum_add_distrib] using htotal
  have hglobal : |A - B| ≤ δ * (A + B) := by
    calc
      |A - B| = |∑ x, (a x - b x)| := by
        simp only [Finset.sum_sub_distrib, A, B]
      _ ≤ ∑ x, |a x - b x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, δ * (a x + b x) :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = δ * (A + B) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, A, B]
  have hgap : 0 < (1 - δ) * (A + B) :=
    mul_pos (sub_pos.mpr hδ1) htotal'
  have hA : 0 < A := by
    apply lt_of_le_of_ne (Finset.sum_nonneg (fun x _ => ha x))
    intro hzero
    have hlo := (abs_le.mp hglobal).1
    nlinarith
  have hB : 0 < B := by
    apply lt_of_le_of_ne (Finset.sum_nonneg (fun x _ => hb x))
    intro hzero
    have hhi := (abs_le.mp hglobal).2
    nlinarith
  refine ⟨hA, hB, ?_⟩
  by_cases hδeq : δ = 0
  · have heq : a = b := by
      funext x
      apply sub_eq_zero.mp
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [hδeq, zero_mul] using hpoint x)
        (abs_nonneg _)
    simp only [heq, sub_self, abs_zero, Finset.sum_const_zero, mul_zero, hδeq, le_refl]
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδeq)
    let T := ∑ x, |a x * B - A * b x|
    have hcross (x : X) :
        (A + B) * (a x - b x) - (A - B) * (a x + b x) =
          2 * (a x * B - A * b x) := by ring
    have hscaled : δ * (2 * T) ≤ δ ^ 2 * (A + B) ^ 2 - (A - B) ^ 2 := by
      calc
        δ * (2 * T) =
            ∑ x, δ * |(A + B) * (a x - b x) - (A - B) * (a x + b x)| := by
          simp only [hcross, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
            T, Finset.mul_sum]
        _ ≤ ∑ x, (δ ^ 2 * (A + B) * (a x + b x) - (A - B) * (a x - b x)) :=
          Finset.sum_le_sum (fun x _ => scaled_abs_cross_le hδ0 hglobal (hpoint x))
        _ = δ ^ 2 * (A + B) ^ 2 - (A - B) ^ 2 := by
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_add_distrib, Finset.sum_sub_distrib]
          change δ ^ 2 * (A + B) * (A + B) - (A - B) * (A - B) = _
          ring
    have hδsq : 0 ≤ 1 - δ ^ 2 := by nlinarith
    have hcorrection : 0 ≤ (1 - δ ^ 2) * (A - B) ^ 2 :=
      mul_nonneg hδsq (sq_nonneg _)
    have hscaled' : δ * T ≤ δ * (2 * δ * A * B) := by
      nlinarith only [hscaled, hcorrection]
    have hT : T ≤ 2 * δ * A * B := (mul_le_mul_left hδpos).mp hscaled'
    have hquot : (∑ x, |a x / A - b x / B|) = T / (A * B) := by
      calc
        (∑ x, |a x / A - b x / B|) =
            ∑ x, |a x * B - A * b x| / (A * B) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [div_sub_div _ _ (ne_of_gt hA) (ne_of_gt hB), abs_div,
            abs_of_pos (mul_pos hA hB)]
        _ = T / (A * B) := by simp only [T, div_eq_mul_inv, Finset.sum_mul]
    have hnorm : T / (A * B) ≤ 2 * δ :=
      (div_le_iff₀ (mul_pos hA hB)).mpr (by nlinarith only [hT])
    change (1 / 2 : ℝ) * (∑ x, |a x / A - b x / B|) ≤ δ
    rw [hquot]
    nlinarith only [hnorm]

end FiniteParityObservation
