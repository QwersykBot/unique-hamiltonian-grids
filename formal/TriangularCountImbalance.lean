import CoreLabelFlip
import CoreConnectivity
import CountedTransferEquivalence
import AcceptedRatio

/-!
# A finite geometric bound for the actual parity-count imbalance

The existing uniform matrix contraction theorem is specialized to the
integer multiplicity matrix of actual core labels. The exact counted-object
identity then gives a bound at every physical cylinder width at least three.
No spectral expansion or weighted-cycle enumeration is asserted.
-/

namespace TriangularCylinder.Transfer

open CountedHamiltonian CylinderTransfer CylinderMatrixContraction
open scoped BigOperators Matrix

/-- For each circumference at least three, the relative imbalance of the
two actual undirected Hamiltonian parity counts has a uniform geometric
bound in the number of complete transfer blocks. -/
theorem exists_parityCount_geometric_imbalance {m : ℕ} (hm : 3 ≤ m) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ L : ℕ, 3 ≤ L →
        |(parityCount m L hm 0 : ℝ) - (parityCount m L hm 1 : ℝ)| ≤
          rho ^ ((L - 2) / N) *
            ((parityCount m L hm 0 : ℝ) + (parityCount m L hm 1 : ℝ)) := by
  classical
  let T : Matrix (CoreState hm) (CoreState hm) ℝ := realTransitionMatrix (LocalLabel hm)
  let f : CoreState hm → ℝ := fun s => Fintype.card (InitialLabel hm s)
  let g : CoreState hm → ℝ := fun s => Fintype.card (TerminalLabel hm 0 s)
  have hT : ∀ s t, 0 ≤ T s t := fun _ _ => Nat.cast_nonneg _
  have hconnected : ∀ s t, ∃ n, 0 < (T ^ n) s t := by
    intro s t
    obtain ⟨n, hn⟩ := core_path_nonempty hm s t
    exact ⟨n, (realTransitionMatrix_pow_pos_iff (LocalLabel hm) n s t).mpr hn⟩
  have htwo : 0 < (T ^ 2) (commonCoreState m hm) (commonCoreState m hm) :=
    (realTransitionMatrix_pow_pos_iff (LocalLabel hm) 2 _ _).mpr (common_return_two m hm)
  have hthree : 0 < (T ^ 3) (commonCoreState m hm) (commonCoreState m hm) :=
    (realTransitionMatrix_pow_pos_iff (LocalLabel hm) 3 _ _).mpr (common_return_three m hm)
  have hsym : SymmetricUnder (coreFlipEquiv hm) T := by
    intro s t
    exact congrArg (fun n : ℕ => (n : ℝ)) (localLabel_card_flip hm s t)
  have hg₁ : (fun s : CoreState hm => (Fintype.card (TerminalLabel hm 1 s) : ℝ)) =
      fun s => g (coreFlipEquiv hm s) := by
    funext s
    have htwoParity : (1 : ZMod 2) + 1 = 0 := by decide
    exact congrArg (fun n : ℕ => (n : ℝ))
      (by simpa only [htwoParity] using (terminalLabel_card_flip hm (1 : ZMod 2) s).symm)
  have hcount₀ (n : ℕ) (hn : 1 ≤ n) : (parityCount m (n + 2) hm 0 : ℝ) =
      f ⬝ᵥ ((T ^ n) *ᵥ g) := parityCount_eq_transfer_real hm hn 0
  have hcount₁ (n : ℕ) (hn : 1 ≤ n) : (parityCount m (n + 2) hm 1 : ℝ) =
      f ⬝ᵥ ((T ^ n) *ᵥ fun s => g (coreFlipEquiv hm s)) := by
    simpa only [hg₁] using parityCount_eq_transfer_real hm hn 1
  let b : ℝ := 1 + ∑ p : CoreState hm × CoreState hm, T p.1 p.2
  have hsum : 0 ≤ ∑ p : CoreState hm × CoreState hm, T p.1 p.2 :=
    Finset.sum_nonneg (fun p _ => hT p.1 p.2)
  have hb : (1 : ℝ) ≤ b := by
    dsimp [b]
    linarith
  have hupper : ∀ s t, T s t ≤ b := by
    intro s t
    have hle : T s t ≤ ∑ p : CoreState hm × CoreState hm, T p.1 p.2 :=
      Finset.single_le_sum (fun p _ => hT p.1 p.2) (Finset.mem_univ (s, t))
    dsimp [b]
    linarith
  have hsupport : ∀ s t, 0 < T s t → 1 ≤ T s t := by
    intro s t hst
    exact Nat.one_le_cast.mpr (Nat.succ_le_iff.mpr (Nat.cast_pos.mp hst))
  obtain ⟨N, hN, rho, hrho₀, hrho₁, hbound⟩ :=
    uniform_finite_imbalance_of_support hT hconnected (commonCoreState m hm)
      htwo hthree (coreFlipEquiv hm) (coreFlip_involutive hm)
      (a := 1) (b := b) zero_lt_one hb
  refine ⟨N, hN, rho, hrho₀, hrho₁, ?_⟩
  intro L hL
  let n := L - 2
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hwidth : n + 2 = L := by dsimp [n]; omega
  have hfinite := hbound (List.replicate n T)
    (by intro B hB; simpa only [List.eq_of_mem_replicate hB] using hT)
    (by intro B hB; simpa only [List.eq_of_mem_replicate hB] using hsupport)
    (by intro B hB; simpa only [List.eq_of_mem_replicate hB] using hupper)
    (by intro B hB; simpa only [List.eq_of_mem_replicate hB] using hsym)
    f g (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
  simpa only [List.prod_replicate, List.length_replicate,
    ← hcount₀ n hn, ← hcount₁ n hn, hwidth] using hfinite

#print axioms exists_parityCount_geometric_imbalance

end TriangularCylinder.Transfer
