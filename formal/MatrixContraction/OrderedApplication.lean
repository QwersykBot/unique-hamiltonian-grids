import MatrixContraction.Basic
import MatrixContraction.Limits
import MatrixContraction.PositiveBlocks

/-!
# Ordered factor families: support assumptions imply a ratio limit

This module constructs the block/residual partition of each original factor
list. It imports the checked positivity, contraction, and limit arguments;
it does not assume positive blocks or an externally supplied decomposition.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter

namespace CylinderMatrixContraction

/-- The first `k` consecutive chunks, each requested to have length `N`.
The specifications below establish full length whenever `k*N ≤ xs.length`. -/
def fullChunks {α : Type*} (N : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | k + 1, xs => xs.take N :: fullChunks N k (xs.drop N)

theorem fullChunks_length {α : Type*} (N k : ℕ) (xs : List α) :
    (fullChunks N k xs).length = k := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => simp only [fullChunks, List.length_cons, ih]

/-- Concatenating the chunks and the remaining suffix recovers the exact
original list, preserving all factor order. -/
theorem fullChunks_flatten_append_drop {α : Type*} (N k : ℕ) (xs : List α) :
    (fullChunks N k xs).flatten ++ xs.drop (k * N) = xs := by
  induction k generalizing xs with
  | zero => simp [fullChunks]
  | succ k ih =>
    simp only [fullChunks, List.flatten_cons, List.append_assoc]
    have hdrop : xs.drop ((k + 1) * N) = (xs.drop N).drop (k * N) := by
      simp only [List.drop_drop, Nat.succ_mul, Nat.add_comm]
    rw [hdrop, ih]
    exact List.take_append_drop N xs

/-- Every full chunk has the requested length and contains only original
factors. The condition is derived from division in the application below. -/
theorem fullChunks_spec {α : Type*} (N k : ℕ) (xs : List α)
    (hfit : k * N ≤ xs.length) :
    ∀ ys ∈ fullChunks N k xs, ys.length = N ∧ ∀ x ∈ ys, x ∈ xs := by
  induction k generalizing xs with
  | zero => intro ys hy; simp [fullChunks] at hy
  | succ k ih =>
    have hN : N ≤ xs.length := by
      simp only [Nat.succ_mul] at hfit
      omega
    have htail : k * N ≤ (xs.drop N).length := by
      simp only [List.length_drop, Nat.succ_mul] at *
      omega
    intro ys hy
    rcases List.mem_cons.mp hy with hys | hys
    · subst ys
      exact ⟨List.length_take_of_le hN, fun x hx => List.mem_of_mem_take hx⟩
    · obtain ⟨hlen, hmem⟩ := ih (xs.drop N) htail ys hys
      exact ⟨hlen, fun x hx => List.mem_of_mem_drop (hmem x hx)⟩

/-- The actual suffix after all complete chunks. -/
def factorResidual {α : Type*} (N : ℕ) (xs : List α) : List α :=
  xs.drop ((xs.length / N) * N)

/-- Products of all complete consecutive chunks, in their original order. -/
def chunkProducts {M : Type*} [Monoid M] (N : ℕ) (xs : List M) : List M :=
  (fullChunks N (xs.length / N) xs).map List.prod

theorem chunkProducts_length {M : Type*} [Monoid M] (N : ℕ) (xs : List M) :
    (chunkProducts N xs).length = xs.length / N := by
  simp only [chunkProducts, List.length_map, fullChunks_length]

theorem factorResidual_length_lt {α : Type*} {N : ℕ} (hN : 0 < N) (xs : List α) :
    (factorResidual N xs).length < N := by
  simp only [factorResidual, List.length_drop, ← Nat.mod_eq_sub_div_mul]
  exact Nat.mod_lt _ hN

/-- The ordered matrix/monoid product is unchanged by the constructed partition. -/
theorem chunkProducts_mul_residual {M : Type*} [Monoid M] (N : ℕ) (xs : List M) :
    (chunkProducts N xs).prod * (factorResidual N xs).prod = xs.prod := by
  have h := congrArg List.prod (fullChunks_flatten_append_drop N (xs.length / N) xs)
  simpa only [List.prod_append, List.prod_flatten, chunkProducts, factorResidual] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem symmetricUnder_one (u : Equiv.Perm ι) :
    SymmetricUnder u (1 : Matrix ι ι ℝ) := by
  intro i j
  simp [Matrix.one_apply]

omit [DecidableEq ι] in
theorem symmetricUnder_mul (u : Equiv.Perm ι) {A B : Matrix ι ι ℝ}
    (hA : SymmetricUnder u A) (hB : SymmetricUnder u B) :
    SymmetricUnder u (A * B) := by
  intro i j
  change (∑ k, A (u i) k * B k (u j)) = ∑ k, A i k * B k j
  calc
    (∑ k, A (u i) k * B k (u j)) =
        ∑ k, A (u i) (u k) * B (u k) (u j) :=
      (Equiv.sum_comp u (fun k => A (u i) k * B k (u j))).symm
    _ = ∑ k, A i k * B k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hA i k, hB k j]

theorem symmetricUnder_list_prod (u : Equiv.Perm ι)
    (factors : List (Matrix ι ι ℝ))
    (hsym : ∀ B ∈ factors, SymmetricUnder u B) :
    SymmetricUnder u factors.prod := by
  revert hsym
  induction factors with
  | nil => intro _; simpa only [List.prod_nil] using symmetricUnder_one u
  | cons B factors ih =>
    intro hsym
    rw [List.prod_cons]
    exact symmetricUnder_mul u (hsym B (by simp))
      (ih (fun C hC => hsym C (List.mem_cons_of_mem B hC)))

/-- A uniform finite imbalance estimate for every original ordered factor
list. Both the positive block length and contraction factor are derived from
support connectivity, the two returns, and the entry bounds. -/
theorem uniform_finite_imbalance_of_support {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (hconnected : ∀ x y : ι, ∃ n : ℕ, 0 < (T ^ n) x y)
    (v : ι) (h₂ : 0 < (T ^ 2) v v) (h₃ : 0 < (T ^ 3) v v)
    (u : Equiv.Perm ι) (hu : Function.Involutive u)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ factors : List (Matrix ι ι ℝ),
        (∀ B ∈ factors, ∀ i j, 0 ≤ B i j) →
        (∀ B ∈ factors, ∀ i j, 0 < T i j → a ≤ B i j) →
        (∀ B ∈ factors, ∀ i j, B i j ≤ b) →
        (∀ B ∈ factors, SymmetricUnder u B) →
        ∀ f g : ι → ℝ, (∀ i, 0 ≤ f i) → (∀ i, 0 ≤ g i) →
          |(f ⬝ᵥ (factors.prod *ᵥ g)) -
            (f ⬝ᵥ (factors.prod *ᵥ (fun i => g (u i))))| ≤
          ρ ^ (factors.length / N) *
            ((f ⬝ᵥ (factors.prod *ᵥ g)) +
              (f ⬝ᵥ (factors.prod *ᵥ (fun i => g (u i))))) := by
  obtain ⟨N, hN, lower, upper, hlower, hlower_upper, hpositive⟩ :=
    uniform_positive_blocks_of_support hT hconnected v h₂ h₃ ha hab
  refine ⟨N, hN, 1 - lower / upper, rho_nonneg hlower hlower_upper,
    rho_lt_one hlower hlower_upper, ?_⟩
  intro factors hnonneg hsupport hupper hsym f g hf hg
  let blocks := chunkProducts N factors
  let R := (factorResidual N factors).prod
  have hblockData : ∀ B ∈ blocks, SymmetricUnder u B ∧
      ∀ i j, lower ≤ B i j ∧ B i j ≤ upper := by
    intro B hB
    change B ∈ (fullChunks N (factors.length / N) factors).map List.prod at hB
    obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hB
    obtain ⟨hyslen, hysmem⟩ := fullChunks_spec N (factors.length / N) factors
      (Nat.div_mul_le_self _ _) ys hys
    have hysnonneg : ∀ C ∈ ys, ∀ i j, 0 ≤ C i j :=
      fun C hC => hnonneg C (hysmem C hC)
    have hyssupport : ∀ C ∈ ys, ∀ i j, 0 < T i j → a ≤ C i j :=
      fun C hC => hsupport C (hysmem C hC)
    have hysupper : ∀ C ∈ ys, ∀ i j, C i j ≤ b :=
      fun C hC => hupper C (hysmem C hC)
    exact ⟨symmetricUnder_list_prod u ys (fun C hC => hsym C (hysmem C hC)),
      hpositive ys hyslen hysnonneg hyssupport hysupper⟩
  have hRnonneg : ∀ i j, 0 ≤ R i j :=
    matrix_list_prod_entries_nonneg (factorResidual N factors)
      (fun B hB => hnonneg B (List.mem_of_mem_drop hB))
  have hRsym : SymmetricUnder u R :=
    symmetricUnder_list_prod u (factorResidual N factors)
      (fun B hB => hsym B (List.mem_of_mem_drop hB))
  have hc := endpoint_contraction u hu blocks R hlower hlower_upper
    (fun B hB => (hblockData B hB).1)
    (fun B hB i j => ((hblockData B hB).2 i j).1)
    (fun B hB i j => ((hblockData B hB).2 i j).2)
    hRsym hRnonneg hf hg
  have hprod : blocks.prod * R = factors.prod := chunkProducts_mul_residual N factors
  have hlen : blocks.length = factors.length / N := chunkProducts_length N factors
  simpa only [hprod, hlen] using hc

/-- The complete generic ordered-factor application. The original factor
list lengths tend to infinity; the block partition, positive block bounds,
residual properties, and divergent block count are all derived internally.
Every list and boundary vector may vary with `n`. -/
theorem ordered_factor_family_ratio_tendsto_one {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (hconnected : ∀ x y : ι, ∃ k : ℕ, 0 < (T ^ k) x y)
    (v : ι) (h₂ : 0 < (T ^ 2) v v) (h₃ : 0 < (T ^ 3) v v)
    (u : Equiv.Perm ι) (hu : Function.Involutive u)
    (factors : ℕ → List (Matrix ι ι ℝ)) (f g : ℕ → ι → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hnonneg : ∀ n B, B ∈ factors n → ∀ i j, 0 ≤ B i j)
    (hsupport : ∀ n B, B ∈ factors n → ∀ i j, 0 < T i j → a ≤ B i j)
    (hupper : ∀ n B, B ∈ factors n → ∀ i j, B i j ≤ b)
    (hsym : ∀ n B, B ∈ factors n → SymmetricUnder u B)
    (hf : ∀ n i, 0 ≤ f n i) (hg : ∀ n i, 0 ≤ g n i)
    (htotal : ∀ n, 0 <
      (f n ⬝ᵥ ((factors n).prod *ᵥ g n)) +
      (f n ⬝ᵥ ((factors n).prod *ᵥ (fun i => g n (u i)))))
    (hlength : Tendsto (fun n => (factors n).length) atTop atTop) :
    Tendsto (fun n =>
      (f n ⬝ᵥ ((factors n).prod *ᵥ g n)) /
      (f n ⬝ᵥ ((factors n).prod *ᵥ (fun i => g n (u i)))))
      atTop (𝓝 1) := by
  obtain ⟨N, hN, ρ, hρ₀, hρ₁, hbound⟩ :=
    uniform_finite_imbalance_of_support hT hconnected v h₂ h₃ u hu ha hab
  have hNpos : 0 < N := by omega
  have hk : Tendsto (fun n => (factors n).length / N) atTop atTop :=
    (Nat.tendsto_div_const_atTop (ne_of_gt hNpos)).comp hlength
  apply ratio_tendsto_one_of_geometric_imbalance hρ₀ hρ₁ hk htotal
  intro n
  exact hbound (factors n) (hnonneg n) (hsupport n) (hupper n) (hsym n)
    (f n) (g n) (hf n) (hg n)

end CylinderMatrixContraction
