import FiniteTransfer
import MatrixContraction.OrderedApplication

/-!
# Ratio limit for finite accepted labelled paths

The hypotheses concern actual labels and paths. The transfer identities,
eventual positive powers, positive block bounds, and contraction are reused from
the checked counting and matrix modules. Short lengths may have zero counts.
-/

open scoped BigOperators Topology Matrix
open Filter CylinderMatrixContraction

namespace CylinderTransfer

universe u v w z z'

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (E : S → S → Type v) [∀ i j, Fintype (E i j)]

/-- Positive transfer entries are precisely inhabited labelled-path types. -/
theorem realTransitionMatrix_pow_pos_iff (n : ℕ) (i j : S) :
    0 < (realTransitionMatrix E ^ n) i j ↔ Nonempty (LabelledPath E n i j) := by
  rw [← card_labelledPath_real, Nat.cast_pos, Fintype.card_pos_iff]

/-- A positive power and actual boundary choices produce an accepted object. -/
theorem card_accepted_pos_of_positive_power
    (I : S → Type w) (F : S → Type z)
    [∀ i, Fintype (I i)] [∀ j, Fintype (F j)] (n : ℕ)
    (hpower : ∀ i j, 0 < (realTransitionMatrix E ^ n) i j)
    (hI : Nonempty (Σ i, I i)) (hF : Nonempty (Σ j, F j)) :
    0 < Fintype.card (Accepted E I F n) := by
  obtain ⟨⟨i, initial⟩⟩ := hI
  obtain ⟨⟨j, terminal⟩⟩ := hF
  obtain ⟨path⟩ := (realTransitionMatrix_pow_pos_iff E n i j).mp (hpower i j)
  exact Fintype.card_pos_iff.mpr ⟨⟨i, initial, j, path, terminal⟩⟩

/-- Connectivity and the two returns imply eventual positivity of accepted counts. -/
theorem eventually_card_accepted_pos
    (I : S → Type w) (F : S → Type z)
    [∀ i, Fintype (I i)] [∀ j, Fintype (F j)]
    (hconnected : ∀ i j, ∃ n, Nonempty (LabelledPath E n i j))
    (base : S) (h₂ : Nonempty (LabelledPath E 2 base base))
    (h₃ : Nonempty (LabelledPath E 3 base base))
    (hI : Nonempty (Σ i, I i)) (hF : Nonempty (Σ j, F j)) :
    ∀ᶠ n in atTop, 0 < Fintype.card (Accepted E I F n) := by
  have hT : ∀ i j, 0 ≤ realTransitionMatrix E i j := fun _ _ => Nat.cast_nonneg _
  have hconn : ∀ i j, ∃ n, 0 < (realTransitionMatrix E ^ n) i j := by
    intro i j
    obtain ⟨n, hn⟩ := hconnected i j
    exact ⟨n, (realTransitionMatrix_pow_pos_iff E n i j).mpr hn⟩
  obtain ⟨N, _, hN⟩ := eventual_positive_powers hT hconn base
    ((realTransitionMatrix_pow_pos_iff E 2 base base).mpr h₂)
    ((realTransitionMatrix_pow_pos_iff E 3 base base).mpr h₃)
  exact eventually_atTop.mpr ⟨N, fun n hn =>
    card_accepted_pos_of_positive_power E I F n (hN n hn) hI hF⟩

/-- Symmetric local labels and paired terminal labels have asymptotically equal
accepted counts. Denominators are derived to be positive eventually, with no
assumption on short lengths. Both returns occur at the displayed `base` state. -/
theorem accepted_ratio_limit
    (I : S → Type w) (F₀ : S → Type z) (F₁ : S → Type z')
    [∀ i, Fintype (I i)] [∀ i, Fintype (F₀ i)] [∀ i, Fintype (F₁ i)]
    (u : Equiv.Perm S) (hu : Function.Involutive u)
    (edgeEquiv : ∀ i j, E (u i) (u j) ≃ E i j)
    (terminalEquiv : ∀ i, F₁ i ≃ F₀ (u i))
    (hconnected : ∀ i j, ∃ n, Nonempty (LabelledPath E n i j))
    (base : S) (h₂ : Nonempty (LabelledPath E 2 base base))
    (h₃ : Nonempty (LabelledPath E 3 base base))
    (hI : Nonempty (Σ i, I i)) (hF₀ : Nonempty (Σ i, F₀ i)) :
    (∀ᶠ n in atTop, 0 < (Fintype.card (Accepted E I F₁ n) : ℝ)) ∧
      Tendsto (fun n =>
        (Fintype.card (Accepted E I F₀ n) : ℝ) /
          (Fintype.card (Accepted E I F₁ n) : ℝ)) atTop (𝓝 1) := by
  let T : Matrix S S ℝ := realTransitionMatrix E
  let f : S → ℝ := fun i => Fintype.card (I i)
  let g : S → ℝ := fun i => Fintype.card (F₀ i)
  have hT : ∀ i j, 0 ≤ T i j := fun _ _ => Nat.cast_nonneg _
  have hconn : ∀ i j, ∃ n, 0 < (T ^ n) i j := by
    intro i j
    obtain ⟨n, hn⟩ := hconnected i j
    exact ⟨n, (realTransitionMatrix_pow_pos_iff E n i j).mpr hn⟩
  have htwo : 0 < (T ^ 2) base base :=
    (realTransitionMatrix_pow_pos_iff E 2 base base).mpr h₂
  have hthree : 0 < (T ^ 3) base base :=
    (realTransitionMatrix_pow_pos_iff E 3 base base).mpr h₃
  have hsym : SymmetricUnder u T := by
    intro i j
    exact congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr (edgeEquiv i j))
  have hg₁ : (fun i => (Fintype.card (F₁ i) : ℝ)) = fun i => g (u i) := by
    funext i
    exact congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr (terminalEquiv i))
  have hcount₀ (n : ℕ) : (Fintype.card (Accepted E I F₀ n) : ℝ) =
      f ⬝ᵥ ((T ^ n) *ᵥ g) := card_accepted_real E I F₀ n
  have hcount₁ (n : ℕ) : (Fintype.card (Accepted E I F₁ n) : ℝ) =
      f ⬝ᵥ ((T ^ n) *ᵥ fun i => g (u i)) := by
    simpa only [hg₁] using card_accepted_real E I F₁ n
  have hF₁ : Nonempty (Σ i, F₁ i) := by
    obtain ⟨⟨j, terminal⟩⟩ := hF₀
    have terminal' : F₀ (u (u j)) := by simpa only [hu j] using terminal
    exact ⟨⟨u j, (terminalEquiv (u j)).symm terminal'⟩⟩
  obtain ⟨N, _, hN⟩ := eventual_positive_powers hT hconn base htwo hthree
  have hpos₀ (n : ℕ) (hn : N ≤ n) :
      0 < (Fintype.card (Accepted E I F₀ n) : ℝ) :=
    Nat.cast_pos.mpr (card_accepted_pos_of_positive_power E I F₀ n (hN n hn) hI hF₀)
  have hpos₁ (n : ℕ) (hn : N ≤ n) :
      0 < (Fintype.card (Accepted E I F₁ n) : ℝ) :=
    Nat.cast_pos.mpr (card_accepted_pos_of_positive_power E I F₁ n (hN n hn) hI hF₁)
  refine ⟨eventually_atTop.mpr ⟨N, hpos₁⟩, ?_⟩
  let b : ℝ := 1 + ∑ p : S × S, T p.1 p.2
  have hsum : 0 ≤ ∑ p : S × S, T p.1 p.2 :=
    Finset.sum_nonneg (fun p _ => hT p.1 p.2)
  have hb : (1 : ℝ) ≤ b := by dsimp [b]; linarith
  have hupper : ∀ i j, T i j ≤ b := by
    intro i j
    have hle : T i j ≤ ∑ p : S × S, T p.1 p.2 :=
      Finset.single_le_sum (fun p _ => hT p.1 p.2) (Finset.mem_univ (i, j))
    dsimp [b]
    linarith
  have hsupport : ∀ i j, 0 < T i j → 1 ≤ T i j := by
    intro i j hij
    exact Nat.one_le_cast.mpr (Nat.succ_le_iff.mpr (Nat.cast_pos.mp hij))
  have hlimit := ordered_factor_family_ratio_tendsto_one hT hconn base htwo hthree
    u hu (fun n => List.replicate (n + N) T) (fun _ => f) (fun _ => g)
    (a := 1) (b := b) zero_lt_one hb
    (by intro n B hB; simpa only [List.eq_of_mem_replicate hB] using hT)
    (by intro n B hB; simpa only [List.eq_of_mem_replicate hB] using hsupport)
    (by intro n B hB; simpa only [List.eq_of_mem_replicate hB] using hupper)
    (by intro n B hB; simpa only [List.eq_of_mem_replicate hB] using hsym)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (by
      intro n
      simp only [List.prod_replicate]
      rw [← hcount₀, ← hcount₁]
      exact add_pos (hpos₀ (n + N) (Nat.le_add_left _ _))
        (hpos₁ (n + N) (Nat.le_add_left _ _)))
    (by simpa only [List.length_replicate] using tendsto_add_atTop_nat N)
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [List.prod_replicate, ← hcount₀, ← hcount₁] using hlimit

end CylinderTransfer
