import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Eventual positive powers from connectivity and two return lengths

The assumptions below do not include primitivity or a common positive
exponent. Positivity is constructed by concatenating positive-weight paths
through one distinguished state and padding with returns of lengths two and
three at that same state.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace CylinderMatrixContraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem matrix_one_entries_nonneg : ∀ i j : ι, 0 ≤ (1 : Matrix ι ι ℝ) i j := by
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.one_apply, h]

omit [DecidableEq ι] in
theorem matrix_mul_entries_nonneg {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ (A * B) i j := by
  intro i j
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))

theorem matrix_pow_entries_nonneg {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j) (n : ℕ) : ∀ i j, 0 ≤ (T ^ n) i j := by
  induction n with
  | zero => simpa only [pow_zero] using (matrix_one_entries_nonneg (ι := ι))
  | succ n ih =>
    rw [pow_succ]
    exact matrix_mul_entries_nonneg ih hT

omit [DecidableEq ι] in
/-- One positive summand makes the chosen product entry positive. -/
theorem matrix_mul_entry_pos {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    {x y z : ι} (hxy : 0 < A x y) (hyz : 0 < B y z) :
    0 < (A * B) x z := by
  change 0 < ∑ k, A x k * B k z
  exact lt_of_lt_of_le (mul_pos hxy hyz)
    (Finset.single_le_sum (fun k _ => mul_nonneg (hA x k) (hB k z)) (Finset.mem_univ y))

/-- Concatenation of two positive-weight paths, expressed in matrix powers. -/
theorem matrix_pow_add_entry_pos {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j) {m n : ℕ} {x y z : ι}
    (hxy : 0 < (T ^ m) x y) (hyz : 0 < (T ^ n) y z) :
    0 < (T ^ (m + n)) x z := by
  rw [pow_add]
  exact matrix_mul_entry_pos (matrix_pow_entries_nonneg hT m)
    (matrix_pow_entries_nonneg hT n) hxy hyz

/-- Positive returns of lengths two and three at one state generate every
return length at least two. -/
theorem returns_of_lengths_two_three {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j) (v : ι)
    (h₂ : 0 < (T ^ 2) v v) (h₃ : 0 < (T ^ 3) v v) :
    ∀ n : ℕ, 2 ≤ n → 0 < (T ^ n) v v := by
  have hall : ∀ k : ℕ, 0 < (T ^ (k + 2)) v v := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simpa using h₂
    | one => simpa using h₃
    | more k hk _ =>
      exact matrix_pow_add_entry_pos hT hk h₂
  intro n hn
  simpa only [Nat.sub_add_cancel hn] using hall (n - 2)

/-- Strong connectivity of the positive-entry support, stated equivalently
as the existence of some positive power entry for each ordered pair. Together
with the two returns, it implies eventual strict positivity of every entry.
No primitive exponent is assumed. -/
theorem eventual_positive_powers {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (hconnected : ∀ x y : ι, ∃ n : ℕ, 0 < (T ^ n) x y)
    (v : ι) (h₂ : 0 < (T ^ 2) v v) (h₃ : 0 < (T ^ 3) v v) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ x y : ι, 0 < (T ^ n) x y := by
  let toV : ι → ℕ := fun x => Classical.choose (hconnected x v)
  let fromV : ι → ℕ := fun y => Classical.choose (hconnected v y)
  have hto : ∀ x : ι, 0 < (T ^ toV x) x v :=
    fun x => Classical.choose_spec (hconnected x v)
  have hfrom : ∀ y : ι, 0 < (T ^ fromV y) v y :=
    fun y => Classical.choose_spec (hconnected v y)
  let N : ℕ := (∑ x, toV x) + (∑ y, fromV y) + 2
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro n hn x y
  have hto_le : toV x ≤ ∑ i, toV i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (toV i)) (Finset.mem_univ x)
  have hfrom_le : fromV y ≤ ∑ i, fromV i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (fromV i)) (Finset.mem_univ y)
  have hextra : 2 ≤ n - (toV x + fromV y) := by
    dsimp [N] at hn
    omega
  have hreturn := returns_of_lengths_two_three hT v h₂ h₃
    (n - (toV x + fromV y)) hextra
  have hpositive := matrix_pow_add_entry_pos hT
    (matrix_pow_add_entry_pos hT (hto x) hreturn) (hfrom y)
  have heq : (toV x + (n - (toV x + fromV y))) + fromV y = n := by omega
  simpa only [heq] using hpositive

omit [DecidableEq ι] in
/-- Entrywise monotonicity of multiplication under the needed nonnegativity
conditions. Matrix order is unchanged. -/
theorem matrix_mul_entries_mono {A B C D : Matrix ι ι ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (hAC : ∀ i j, A i j ≤ C i j) (hBD : ∀ i j, B i j ≤ D i j) :
    ∀ i j, (A * B) i j ≤ (C * D) i j := by
  intro i j
  exact Finset.sum_le_sum (fun k _ => mul_le_mul (hAC i k) (hBD k j) (hB k j) (hC i k))

theorem matrix_list_prod_entries_nonneg (blocks : List (Matrix ι ι ℝ))
    (hblocks : ∀ B ∈ blocks, ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ blocks.prod i j := by
  revert hblocks
  induction blocks with
  | nil =>
    intro _
    simpa only [List.prod_nil] using (matrix_one_entries_nonneg (ι := ι))
  | cons B blocks ih =>
    intro hblocks
    rw [List.prod_cons]
    exact matrix_mul_entries_nonneg (hblocks B (by simp))
      (ih (fun C hC => hblocks C (List.mem_cons_of_mem B hC)))

/-- A common entrywise lower comparison propagates through any ordered list. -/
theorem matrix_pow_le_list_prod (M : Matrix ι ι ℝ) (blocks : List (Matrix ι ι ℝ))
    (hM : ∀ i j, 0 ≤ M i j)
    (hblocks : ∀ B ∈ blocks, ∀ i j, 0 ≤ B i j)
    (hlower : ∀ B ∈ blocks, ∀ i j, M i j ≤ B i j) :
    ∀ i j, (M ^ blocks.length) i j ≤ blocks.prod i j := by
  revert hblocks hlower
  induction blocks with
  | nil => intro _ _ i j; simp
  | cons B blocks ih =>
    intro hblocks hlower
    rw [List.length_cons, pow_succ', List.prod_cons]
    exact matrix_mul_entries_mono (matrix_pow_entries_nonneg hM blocks.length)
      (hblocks B (by simp)) (hlower B (by simp))
      (ih (fun C hC => hblocks C (List.mem_cons_of_mem B hC))
        (fun C hC => hlower C (List.mem_cons_of_mem B hC)))

/-- A common entrywise upper comparison propagates through any ordered list. -/
theorem matrix_list_prod_le_pow (M : Matrix ι ι ℝ) (blocks : List (Matrix ι ι ℝ))
    (hM : ∀ i j, 0 ≤ M i j)
    (hblocks : ∀ B ∈ blocks, ∀ i j, 0 ≤ B i j)
    (hupper : ∀ B ∈ blocks, ∀ i j, B i j ≤ M i j) :
    ∀ i j, blocks.prod i j ≤ (M ^ blocks.length) i j := by
  revert hblocks hupper
  induction blocks with
  | nil => intro _ _ i j; simp
  | cons B blocks ih =>
    intro hblocks hupper
    rw [List.length_cons, pow_succ', List.prod_cons]
    have htail : ∀ C ∈ blocks, ∀ i j, 0 ≤ C i j :=
      fun C hC => hblocks C (List.mem_cons_of_mem B hC)
    exact matrix_mul_entries_mono (matrix_list_prod_entries_nonneg blocks htail)
      hM (hupper B (by simp))
      (ih htail (fun C hC => hupper C (List.mem_cons_of_mem B hC)))

/-- A scalar factor at each step multiplies a length-`n` product by its `n`th power. -/
theorem scaled_matrix_pow_apply (T : Matrix ι ι ℝ) (c : ℝ) (n : ℕ) :
    ∀ i j, ((Matrix.of (fun i j => c * T i j)) ^ n) i j =
      c ^ n * (T ^ n) i j := by
  induction n with
  | zero => intro i j; simp
  | succ n ih =>
    intro i j
    simp only [pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Uniform positive block bounds for all ordered lists of a fixed length.
Each factor is nonnegative, is at least `a` on the reference matrix's positive
support, and is everywhere at most `b`. Extra positive entries are allowed,
so in particular this applies to factors with exactly the common support.

The length and both bounds are derived from support connectivity and the
two returns; no common positive block or exponent is assumed. -/
theorem uniform_positive_blocks_of_support {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (hconnected : ∀ x y : ι, ∃ n : ℕ, 0 < (T ^ n) x y)
    (v : ι) (h₂ : 0 < (T ^ 2) v v) (h₃ : 0 < (T ^ 3) v v)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧
      ∀ blocks : List (Matrix ι ι ℝ), blocks.length = N →
        (∀ B ∈ blocks, ∀ i j, 0 ≤ B i j) →
        (∀ B ∈ blocks, ∀ i j, 0 < T i j → a ≤ B i j) →
        (∀ B ∈ blocks, ∀ i j, B i j ≤ b) →
        ∀ i j, lower ≤ blocks.prod i j ∧ blocks.prod i j ≤ upper := by
  obtain ⟨N, hN₂, hN⟩ := eventual_positive_powers hT hconnected v h₂ h₃
  let M : ℝ := 1 + ∑ p : ι × ι, T p.1 p.2
  have hsum : 0 ≤ ∑ p : ι × ι, T p.1 p.2 :=
    Finset.sum_nonneg (fun p _ => hT p.1 p.2)
  have hM : 0 < M := by dsimp [M]; linarith
  have hTupper : ∀ i j, T i j ≤ M := by
    intro i j
    have hle : T i j ≤ ∑ p : ι × ι, T p.1 p.2 :=
      Finset.single_le_sum (fun p _ => hT p.1 p.2) (Finset.mem_univ (i, j))
    dsimp [M]
    linarith
  let c : ℝ := a / M
  have hc : 0 < c := div_pos ha hM
  let S : Matrix ι ι ℝ := fun i j => c * T i j
  have hS : ∀ i j, 0 ≤ S i j := fun i j => mul_nonneg hc.le (hT i j)
  have hSpos : ∀ i j, 0 < (S ^ N) i j := by
    intro i j
    change 0 < ((Matrix.of (fun i j => c * T i j)) ^ N) i j
    rw [scaled_matrix_pow_apply]
    exact mul_pos (pow_pos hc N) (hN N le_rfl i j)
  let H : Matrix ι ι ℝ := fun _ _ => b
  have hH : ∀ i j, 0 ≤ H i j := fun _ _ => ha.le.trans hab
  have hpairs : (Finset.univ : Finset (ι × ι)).Nonempty :=
    ⟨(v, v), Finset.mem_univ _⟩
  let lower : ℝ := Finset.univ.inf' hpairs (fun p : ι × ι => (S ^ N) p.1 p.2)
  have hlowerpos : 0 < lower :=
    (Finset.lt_inf'_iff hpairs).2 (fun p _ => hSpos p.1 p.2)
  let upper : ℝ := max lower (∑ p : ι × ι, (H ^ N) p.1 p.2)
  refine ⟨N, hN₂, lower, upper, hlowerpos, le_max_left _ _, ?_⟩
  intro blocks hlength hblocks hlower hupper i j
  have hSle : ∀ B ∈ blocks, ∀ i j, S i j ≤ B i j := by
    intro B hB i j
    by_cases hij : 0 < T i j
    · calc
        S i j = c * T i j := rfl
        _ ≤ c * M := mul_le_mul_of_nonneg_left (hTupper i j) hc.le
        _ = a := div_mul_cancel₀ a (ne_of_gt hM)
        _ ≤ B i j := hlower B hB i j hij
    · have hzero : T i j = 0 := le_antisymm (le_of_not_gt hij) (hT i j)
      simpa only [S, hzero, mul_zero] using hblocks B hB i j
  have hlowerprod := matrix_pow_le_list_prod S blocks hS hblocks hSle
  have hupperprod := matrix_list_prod_le_pow H blocks hH hblocks hupper
  rw [hlength] at hlowerprod hupperprod
  have hlowerentry : lower ≤ (S ^ N) i j :=
    Finset.inf'_le (fun p : ι × ι => (S ^ N) p.1 p.2) (Finset.mem_univ (i, j))
  have hupperentry : (H ^ N) i j ≤ ∑ p : ι × ι, (H ^ N) p.1 p.2 :=
    Finset.single_le_sum (fun p _ => matrix_pow_entries_nonneg hH N p.1 p.2)
      (Finset.mem_univ (i, j))
  exact ⟨hlowerentry.trans (hlowerprod i j),
    (hupperprod i j).trans (hupperentry.trans (le_max_right _ _))⟩

end CylinderMatrixContraction
