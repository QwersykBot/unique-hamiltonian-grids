import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite ordered matrix-product contraction on an odd subspace

This internal supporting formalization is independent of any cylinder state
space or transfer construction. Matrices are arbitrary real matrices on a
finite type. The list order is preserved throughout; distinct matrices are
never required to commute with one another.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace CylinderMatrixContraction

variable {ι : Type*} [Fintype ι]

/-- Invariance under simultaneous relabelling of both indices. For an
involutory permutation this is equivalent to commuting with that permutation. -/
def SymmetricUnder (u : Equiv.Perm ι) (B : Matrix ι ι ℝ) : Prop :=
  ∀ i j, B (u i) (u j) = B i j

/-- The minus-one subspace for the permutation action. -/
def OddUnder (u : Equiv.Perm ι) (z : ι → ℝ) : Prop :=
  ∀ i, z (u i) = -z i

/-- The original ordered product, evaluated from the right. -/
def act (blocks : List (Matrix ι ι ℝ)) (z : ι → ℝ) : ι → ℝ :=
  blocks.foldr (fun B v => B *ᵥ v) z

theorem odd_sum_zero (u : Equiv.Perm ι) {z : ι → ℝ}
    (hz : OddUnder u z) : ∑ i, z i = 0 := by
  have heq : (∑ i, z i) = -(∑ i, z i) := by
    calc
      (∑ i, z i) = ∑ i, z (u i) := (Equiv.sum_comp u z).symm
      _ = ∑ i, -z i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hz i
      _ = -(∑ i, z i) := Finset.sum_neg_distrib
  linarith

theorem mulVec_odd (u : Equiv.Perm ι) {B : Matrix ι ι ℝ} {z : ι → ℝ}
    (hB : SymmetricUnder u B) (hz : OddUnder u z) :
    OddUnder u (B *ᵥ z) := by
  intro i
  change (∑ j, B (u i) j * z j) = -(∑ j, B i j * z j)
  calc
    (∑ j, B (u i) j * z j) = ∑ j, B (u i) (u j) * z (u j) :=
      (Equiv.sum_comp u (fun j => B (u i) j * z j)).symm
    _ = ∑ j, -(B i j * z j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hB i j, hz j]
      ring
    _ = -(∑ j, B i j * z j) := Finset.sum_neg_distrib

/-- Subtracting a constant all-ones matrix has no effect on an odd vector. -/
theorem subtract_constant_mulVec (u : Equiv.Perm ι) (B : Matrix ι ι ℝ)
    (a : ℝ) {z : ι → ℝ} (hz : OddUnder u z) :
    (fun i j => B i j - a) *ᵥ z = B *ᵥ z := by
  ext i
  change (∑ j, (B i j - a) * z j) = ∑ j, B i j * z j
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    odd_sum_zero u hz, mul_zero, sub_zero]

theorem mulVec_nonneg {B : Matrix ι ι ℝ} {z : ι → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (hz : ∀ i, 0 ≤ z i) :
    ∀ i, 0 ≤ (B *ᵥ z) i := by
  intro i
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hB i j) (hz j))

theorem mulVec_mono {B : Matrix ι ι ℝ} {x y : ι → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (hxy : ∀ i, x i ≤ y i) :
    ∀ i, (B *ᵥ x) i ≤ (B *ᵥ y) i := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hB i j))

theorem abs_mulVec_le {B : Matrix ι ι ℝ} {x y : ι → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (hxy : ∀ i, |x i| ≤ y i) :
    ∀ i, |(B *ᵥ x) i| ≤ (B *ᵥ y) i := by
  intro i
  change |∑ j, B i j * x j| ≤ ∑ j, B i j * y j
  calc
    |∑ j, B i j * x j| ≤ ∑ j, |B i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, B i j * |x j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hB i j)]
    _ ≤ ∑ j, B i j * y j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hB i j))

theorem mulVec_scalar (B : Matrix ι ι ℝ) (c : ℝ) (z : ι → ℝ) :
    B *ᵥ (fun i => c * z i) = fun i => c * (B *ᵥ z) i := by
  ext i
  change (∑ j, B i j * (c * z j)) = c * ∑ j, B i j * z j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The entrywise estimate that produces the contraction factor. -/
theorem subtract_le_scaled {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hxb : x ≤ b) : x - a ≤ (1 - a / b) * x := by
  have hmul : a * x ≤ a * b := mul_le_mul_of_nonneg_left hxb ha
  have hdiv : a * x / b ≤ a := (div_le_iff₀ hb).2 hmul
  calc
    x - a ≤ x - a * x / b := by linarith
    _ = (1 - a / b) * x := by ring

theorem rho_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ 1 - a / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  exact sub_nonneg.mpr ((div_le_one₀ hb).2 hab)

theorem rho_lt_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 - a / b < 1 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have : 0 < a / b := div_pos ha hb
  linarith

/-- A single positive block contracts its odd vectors relative to its action
on their absolute values. The contraction is derived, not assumed. -/
theorem single_block_contraction (u : Equiv.Perm ι) {B : Matrix ι ι ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ i j, a ≤ B i j) (hupper : ∀ i j, B i j ≤ b)
    {z : ι → ℝ} (hz : OddUnder u z) :
    ∀ i, |(B *ᵥ z) i| ≤ (1 - a / b) * (B *ᵥ (fun j => |z j|)) i := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hC : ∀ i j, 0 ≤ B i j - a := fun i j => sub_nonneg.mpr (hlower i j)
  intro i
  calc
    |(B *ᵥ z) i| = |((fun i j => B i j - a) *ᵥ z) i| := by
      rw [subtract_constant_mulVec u B a hz]
    _ ≤ ((fun i j => B i j - a) *ᵥ (fun j => |z j|)) i :=
      abs_mulVec_le hC (fun _ => le_rfl) i
    _ ≤ (1 - a / b) * (B *ᵥ (fun j => |z j|)) i := by
      change (∑ j, (B i j - a) * |z j|) ≤
        (1 - a / b) * ∑ j, B i j * |z j|
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        (B i j - a) * |z j| ≤ ((1 - a / b) * B i j) * |z j| :=
          mul_le_mul_of_nonneg_right
            (subtract_le_scaled ha.le hb (hupper i j)) (abs_nonneg _)
        _ = (1 - a / b) * (B i j * |z j|) := by ring

theorem act_odd (u : Equiv.Perm ι) (blocks : List (Matrix ι ι ℝ))
    (hsym : ∀ B ∈ blocks, SymmetricUnder u B) {z : ι → ℝ}
    (hz : OddUnder u z) : OddUnder u (act blocks z) := by
  revert hsym
  induction blocks with
  | nil => intro _; simpa [act] using hz
  | cons B blocks ih =>
    intro hsym
    have htail : ∀ C ∈ blocks, SymmetricUnder u C := by
      intro C hC
      exact hsym C (List.mem_cons_of_mem B hC)
    simpa [act] using mulVec_odd u (hsym B (by simp)) (ih htail)

/-- Any finite ordered list of positive blocks has exponential contraction
on its common odd subspace. -/
theorem ordered_blocks_contraction (u : Equiv.Perm ι)
    (blocks : List (Matrix ι ι ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsym : ∀ B ∈ blocks, SymmetricUnder u B)
    (hlower : ∀ B ∈ blocks, ∀ i j, a ≤ B i j)
    (hupper : ∀ B ∈ blocks, ∀ i j, B i j ≤ b)
    {z y : ι → ℝ} (hz : OddUnder u z) (hzy : ∀ i, |z i| ≤ y i) :
    ∀ i, |act blocks z i| ≤ (1 - a / b) ^ blocks.length * act blocks y i := by
  have hrho : 0 ≤ 1 - a / b := rho_nonneg ha hab
  revert hsym hlower hupper
  induction blocks with
  | nil =>
    intro _ _ _ i
    simpa [act] using hzy i
  | cons B blocks ih =>
    intro hsym hlower hupper i
    have hmem : B ∈ B :: blocks := by simp
    have hsymtail : ∀ C ∈ blocks, SymmetricUnder u C := by
      intro C hC
      exact hsym C (List.mem_cons_of_mem B hC)
    have hlowertail : ∀ C ∈ blocks, ∀ i j, a ≤ C i j := by
      intro C hC
      exact hlower C (List.mem_cons_of_mem B hC)
    have huppertail : ∀ C ∈ blocks, ∀ i j, C i j ≤ b := by
      intro C hC
      exact hupper C (List.mem_cons_of_mem B hC)
    have hBnonneg : ∀ i j, 0 ≤ B i j := fun i j => ha.le.trans (hlower B hmem i j)
    have htailodd : OddUnder u (act blocks z) := act_odd u blocks hsymtail hz
    have htailbound := ih hsymtail hlowertail huppertail
    change |(B *ᵥ act blocks z) i| ≤
      (1 - a / b) ^ (blocks.length + 1) * (B *ᵥ act blocks y) i
    calc
      |(B *ᵥ act blocks z) i| ≤
          (1 - a / b) * (B *ᵥ (fun j => |act blocks z j|)) i :=
        single_block_contraction u ha hab (hlower B hmem) (hupper B hmem) htailodd i
      _ ≤ (1 - a / b) *
          (B *ᵥ (fun j => (1 - a / b) ^ blocks.length * act blocks y j)) i :=
        mul_le_mul_of_nonneg_left (mulVec_mono hBnonneg htailbound i) hrho
      _ = (1 - a / b) ^ (blocks.length + 1) * (B *ᵥ act blocks y) i := by
        rw [mulVec_scalar, pow_succ]
        ring

theorem abs_dotProduct_le {f x y : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hxy : ∀ i, |x i| ≤ y i) :
    |f ⬝ᵥ x| ≤ f ⬝ᵥ y := by
  change |∑ i, f i * x i| ≤ ∑ i, f i * y i
  calc
    |∑ i, f i * x i| ≤ ∑ i, |f i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, f i * |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hf i)]
    _ ≤ ∑ i, f i * y i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hf i))

theorem dotProduct_scalar (f z : ι → ℝ) (c : ℝ) :
    f ⬝ᵥ (fun i => c * z i) = c * (f ⬝ᵥ z) := by
  change (∑ i, f i * (c * z i)) = c * ∑ i, f i * z i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full finite ordered-product estimate, including a nonnegative
symmetry-preserving residual matrix and a nonnegative left boundary. -/
theorem ordered_product_contraction (u : Equiv.Perm ι)
    (blocks : List (Matrix ι ι ℝ)) (R : Matrix ι ι ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsym : ∀ B ∈ blocks, SymmetricUnder u B)
    (hlower : ∀ B ∈ blocks, ∀ i j, a ≤ B i j)
    (hupper : ∀ B ∈ blocks, ∀ i j, B i j ≤ b)
    (hRsym : SymmetricUnder u R) (hR : ∀ i j, 0 ≤ R i j)
    {f d h : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hd : OddUnder u d) (hdh : ∀ i, |d i| ≤ h i) :
    |f ⬝ᵥ act blocks (R *ᵥ d)| ≤
      (1 - a / b) ^ blocks.length * (f ⬝ᵥ act blocks (R *ᵥ h)) := by
  have hbound := ordered_blocks_contraction u blocks ha hab hsym hlower hupper
    (mulVec_odd u hRsym hd) (abs_mulVec_le hR hdh)
  calc
    |f ⬝ᵥ act blocks (R *ᵥ d)| ≤
        f ⬝ᵥ (fun i => (1 - a / b) ^ blocks.length * act blocks (R *ᵥ h) i) :=
      abs_dotProduct_le hf hbound
    _ = (1 - a / b) ^ blocks.length * (f ⬝ᵥ act blocks (R *ᵥ h)) :=
      dotProduct_scalar _ _ _

theorem act_eq_prod [DecidableEq ι] (blocks : List (Matrix ι ι ℝ)) (z : ι → ℝ) :
    act blocks z = blocks.prod *ᵥ z := by
  induction blocks with
  | nil => simp [act]
  | cons B blocks ih =>
    change B *ᵥ act blocks z = (B * blocks.prod) *ᵥ z
    rw [ih, Matrix.mulVec_mulVec]

omit [Fintype ι] in
theorem endpoint_difference_odd (u : Equiv.Perm ι) (hu : Function.Involutive u)
    (g : ι → ℝ) : OddUnder u (g - fun i => g (u i)) := by
  intro i
  change g (u i) - g (u (u i)) = -(g i - g (u i))
  rw [hu i]
  ring

omit [Fintype ι] in
theorem endpoint_difference_abs_le (u : Equiv.Perm ι) {g : ι → ℝ}
    (hg : ∀ i, 0 ≤ g i) : ∀ i, |(g - fun j => g (u j)) i| ≤
      (g + fun j => g (u j)) i := by
  intro i
  change |g i - g (u i)| ≤ g i + g (u i)
  exact abs_le.mpr ⟨by linarith [hg i, hg (u i)], by linarith [hg i, hg (u i)]⟩

/-- Matrix notation for the final endpoint estimate. `blocks.prod * R`
is the product in exactly the supplied order. -/
theorem endpoint_contraction [DecidableEq ι]
    (u : Equiv.Perm ι) (hu : Function.Involutive u)
    (blocks : List (Matrix ι ι ℝ)) (R : Matrix ι ι ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsym : ∀ B ∈ blocks, SymmetricUnder u B)
    (hlower : ∀ B ∈ blocks, ∀ i j, a ≤ B i j)
    (hupper : ∀ B ∈ blocks, ∀ i j, B i j ≤ b)
    (hRsym : SymmetricUnder u R) (hR : ∀ i j, 0 ≤ R i j)
    {f g : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    |(f ⬝ᵥ ((blocks.prod * R) *ᵥ g)) -
        (f ⬝ᵥ ((blocks.prod * R) *ᵥ (fun i => g (u i))))| ≤
      (1 - a / b) ^ blocks.length *
        ((f ⬝ᵥ ((blocks.prod * R) *ᵥ g)) +
          (f ⬝ᵥ ((blocks.prod * R) *ᵥ (fun i => g (u i))))) := by
  have hc := ordered_product_contraction u blocks R ha hab hsym hlower hupper
    hRsym hR hf (endpoint_difference_odd u hu g) (endpoint_difference_abs_le u hg)
  simpa only [act_eq_prod, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_add,
    dotProduct_sub, dotProduct_add] using hc

/-- Normalizing a relative imbalance gives the half-probability estimate.
The total must be positive; no division by a zero total is made. -/
theorem probability_deviation_bound {z₀ z₁ ε : ℝ}
    (htotal : 0 < z₀ + z₁)
    (himbalance : |z₀ - z₁| ≤ ε * (z₀ + z₁)) :
    |z₀ / (z₀ + z₁) - 1 / 2| ≤ ε / 2 := by
  have hupper : z₀ / (z₀ + z₁) ≤ (1 + ε) / 2 := by
    apply (div_le_iff₀ htotal).2
    nlinarith [le_abs_self (z₀ - z₁)]
  have hlower : (1 - ε) / 2 ≤ z₀ / (z₀ + z₁) := by
    apply (le_div_iff₀ htotal).2
    nlinarith [neg_abs_le (z₀ - z₁)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The denominator of the ratio is positive once the relative imbalance
bound is less than one. -/
theorem right_endpoint_pos {z₀ z₁ ε : ℝ}
    (htotal : 0 < z₀ + z₁) (hε : ε < 1)
    (himbalance : |z₀ - z₁| ≤ ε * (z₀ + z₁)) : 0 < z₁ := by
  have hprod : 0 < (1 - ε) * (z₀ + z₁) := mul_pos (sub_pos.mpr hε) htotal
  nlinarith [le_abs_self (z₀ - z₁)]

/-- The finite quantitative ratio estimate, separate from the matrix theorem. -/
theorem ratio_deviation_bound {z₀ z₁ ε : ℝ}
    (htotal : 0 < z₀ + z₁) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (himbalance : |z₀ - z₁| ≤ ε * (z₀ + z₁)) :
    |z₀ / z₁ - 1| ≤ 2 * ε / (1 - ε) := by
  have hz₁ : 0 < z₁ := right_endpoint_pos htotal hε₁ himbalance
  have hgap : (1 - ε) * (z₀ + z₁) ≤ 2 * z₁ := by
    nlinarith [le_abs_self (z₀ - z₁)]
  calc
    |z₀ / z₁ - 1| = |(z₀ - z₁) / z₁| := by
      rw [sub_div, div_self (ne_of_gt hz₁)]
    _ = |z₀ - z₁| / z₁ := by rw [abs_div, abs_of_pos hz₁]
    _ ≤ (ε * (z₀ + z₁)) / z₁ := div_le_div_of_nonneg_right himbalance hz₁.le
    _ ≤ 2 * ε / (1 - ε) := by
      apply (div_le_div_iff₀ hz₁ (sub_pos.mpr hε₁)).2
      have hscaled := mul_le_mul_of_nonneg_left hgap hε₀
      nlinarith

end CylinderMatrixContraction
