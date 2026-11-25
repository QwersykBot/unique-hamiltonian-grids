import MatrixContraction.OrderedApplication

/-!
# Contraction from a bounded interval of an ordered matrix product

Only the factors in the selected interval require the common support lower
bound and entry upper bound. Exterior factors may vanish. Their nonnegativity
allows absorption into the endpoint vectors, and suffix symmetry preserves
the involution relating the two terminal vectors.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace CylinderMatrixContraction

private theorem window_split {α : Type*} (xs : List α) (start stop : ℕ)
    (hstart : start ≤ stop) :
    xs.take start ++ ((xs.drop start).take (stop - start) ++ xs.drop stop) = xs := by
  have hsum : start + (stop - start) = stop := by omega
  have hdrop : xs.drop stop = (xs.drop start).drop (stop - start) := by
    rw [List.drop_drop, hsum]
  rw [hdrop, List.take_append_drop, List.take_append_drop]

private theorem mem_window_ofFn {α : Type*} {n start stop : ℕ}
    (K : Fin n → α) (hstart : start ≤ stop) (hstop : stop ≤ n) {x : α}
    (hx : x ∈ ((List.ofFn K).drop start).take (stop - start)) :
    ∃ i : Fin n, start ≤ i.val ∧ i.val < stop ∧ K i = x := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_take, List.length_drop, List.length_ofFn] at hk
  have hkn : start + k < n := by omega
  refine ⟨⟨start + k, hkn⟩, Nat.le_add_right _ _, ?_, ?_⟩
  · change start + k < stop
    omega
  · simpa only [List.getElem_take, List.getElem_drop, List.getElem_ofFn] using heq

private theorem symmetric_mulVec_comp {ι : Type*} [Fintype ι]
    (u : Equiv.Perm ι) (hu : Function.Involutive u)
    {B : Matrix ι ι ℝ} (hB : SymmetricUnder u B) (g : ι → ℝ) :
    B *ᵥ (fun i => g (u i)) = fun i => (B *ᵥ g) (u i) := by
  ext i
  change (∑ j, B i j * g (u j)) = ∑ j, B (u i) j * g j
  calc
    _ = ∑ j, B i (u j) * g (u (u j)) :=
      (Equiv.sum_comp u (fun j => B i j * g (u j))).symm
    _ = ∑ j, B (u i) j * g j := by
      apply Finset.sum_congr rfl
      intro j _
      have hij : B i (u j) = B (u i) j := by
        simpa only [hu i] using hB (u i) j
      rw [hu j, hij]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Uniform endpoint imbalance using support and entry bounds only on the
half-open factor interval `[start, stop)`. The constants are chosen before
the length, interval, factors, and endpoint vectors. All factors are
nonnegative and commute with the same involution, but exterior factors
need no support lower bound or uniform upper bound. -/
theorem uniform_window_imbalance_of_support {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (hconnected : ∀ x y : ι, ∃ n : ℕ, 0 < (T ^ n) x y)
    (v : ι) (h₂ : 0 < (T ^ 2) v v) (h₃ : 0 < (T ^ 3) v v)
    (u : Equiv.Perm ι) (hu : Function.Involutive u)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (n start stop : ℕ), start ≤ stop → stop ≤ n →
      ∀ K : Fin n → Matrix ι ι ℝ,
        (∀ i x y, 0 ≤ K i x y) →
        (∀ i, SymmetricUnder u (K i)) →
        (∀ i, start ≤ i.val → i.val < stop →
          ∀ x y, 0 < T x y → lo ≤ K i x y) →
        (∀ i, start ≤ i.val → i.val < stop →
          ∀ x y, K i x y ≤ hi) →
        ∀ f g : ι → ℝ, (∀ i, 0 ≤ f i) → (∀ i, 0 ≤ g i) →
          |(f ⬝ᵥ ((List.ofFn K).prod *ᵥ g)) -
            (f ⬝ᵥ ((List.ofFn K).prod *ᵥ (fun i => g (u i))))| ≤
          ρ ^ ((stop - start) / N) *
            ((f ⬝ᵥ ((List.ofFn K).prod *ᵥ g)) +
              (f ⬝ᵥ ((List.ofFn K).prod *ᵥ (fun i => g (u i))))) := by
  obtain ⟨N, hN, ρ, hρ0, hρ1, hwindow⟩ :=
    uniform_finite_imbalance_of_support hT hconnected v h₂ h₃ u hu hlo hlohi
  refine ⟨N, hN, ρ, hρ0, hρ1, ?_⟩
  intro n start stop hstart hstop K hKnonneg hKsym hlower hupper f g hf hg
  let preFactors := (List.ofFn K).take start
  let window := ((List.ofFn K).drop start).take (stop - start)
  let suffix := (List.ofFn K).drop stop
  have hnonneg : ∀ B ∈ List.ofFn K, ∀ x y, 0 ≤ B x y := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact hKnonneg i
  have hsym : ∀ B ∈ List.ofFn K, SymmetricUnder u B := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact hKsym i
  have hprefix : ∀ x y, 0 ≤ preFactors.prod x y :=
    matrix_list_prod_entries_nonneg preFactors
      (fun B hB => hnonneg B (List.mem_of_mem_take hB))
  have hsuffix : ∀ x y, 0 ≤ suffix.prod x y :=
    matrix_list_prod_entries_nonneg suffix
      (fun B hB => hnonneg B (List.mem_of_mem_drop hB))
  have hsuffixsym : SymmetricUnder u suffix.prod :=
    symmetricUnder_list_prod u suffix
      (fun B hB => hsym B (List.mem_of_mem_drop hB))
  let f' := f ᵥ* preFactors.prod
  let g' := suffix.prod *ᵥ g
  have hf' : ∀ i, 0 ≤ f' i := by
    intro i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (hprefix j i))
  have hg' : ∀ i, 0 ≤ g' i := mulVec_nonneg hsuffix hg
  have hwindow_nonneg : ∀ B ∈ window, ∀ x y, 0 ≤ B x y :=
    fun B hB => hnonneg B (List.mem_of_mem_drop (List.mem_of_mem_take hB))
  have hwindow_lower : ∀ B ∈ window, ∀ x y, 0 < T x y → lo ≤ B x y := by
    intro B hB x y hxy
    obtain ⟨i, hi0, hi1, rfl⟩ := mem_window_ofFn K hstart hstop hB
    exact hlower i hi0 hi1 x y hxy
  have hwindow_upper : ∀ B ∈ window, ∀ x y, B x y ≤ hi := by
    intro B hB x y
    obtain ⟨i, hi0, hi1, rfl⟩ := mem_window_ofFn K hstart hstop hB
    exact hupper i hi0 hi1 x y
  have hwindow_sym : ∀ B ∈ window, SymmetricUnder u B :=
    fun B hB => hsym B (List.mem_of_mem_drop (List.mem_of_mem_take hB))
  have hlen : window.length = stop - start := by
    apply List.length_take_of_le
    simp only [List.length_drop, List.length_ofFn]
    omega
  have hprod : (List.ofFn K).prod = preFactors.prod * (window.prod * suffix.prod) := by
    have h := congrArg List.prod (window_split (List.ofFn K) start stop hstart)
    simpa only [List.prod_append] using h.symm
  have habsorb (z : ι → ℝ) :
      f ⬝ᵥ ((List.ofFn K).prod *ᵥ z) =
        f' ⬝ᵥ (window.prod *ᵥ (suffix.prod *ᵥ z)) := by
    rw [hprod, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_mulVec]
  have hleft : f ⬝ᵥ ((List.ofFn K).prod *ᵥ g) =
      f' ⬝ᵥ (window.prod *ᵥ g') := habsorb g
  have hright : f ⬝ᵥ ((List.ofFn K).prod *ᵥ (fun i => g (u i))) =
      f' ⬝ᵥ (window.prod *ᵥ (fun i => g' (u i))) := by
    rw [habsorb, symmetric_mulVec_comp u hu hsuffixsym]
  rw [hleft, hright]
  have h := hwindow window hwindow_nonneg hwindow_lower hwindow_upper hwindow_sym
    f' g' hf' hg'
  simpa only [hlen] using h

end CylinderMatrixContraction

#print axioms CylinderMatrixContraction.uniform_window_imbalance_of_support
