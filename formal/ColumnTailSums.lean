import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Reindexing a strict column tail after a shift

These lemmas concern only finite sums in an additive commutative monoid.
The summands need agree only strictly after the cut. No bound on the cut
index, positive width, graph, mask, or parity definition is assumed.
-/

namespace ColumnTailSums

open scoped BigOperators

/-- Shift a column by `a` into an explicitly equal total width. -/
def shiftCol (a : ℕ) {b L : ℕ} (hL : L = a + b) (c : Fin b) : Fin L :=
  ⟨a + c.val, hL.symm ▸ Nat.add_lt_add_left c.isLt a⟩

@[simp] theorem shiftCol_val (a : ℕ) {b L : ℕ} (hL : L = a + b) (c : Fin b) :
    (shiftCol a hL c).val = a + c.val := rfl

@[simp] theorem shiftCol_eq_natAdd (a : ℕ) {b : ℕ} (c : Fin b) :
    shiftCol a rfl c = Fin.natAdd a c := rfl

theorem shiftCol_injective (a : ℕ) {b L : ℕ} (hL : L = a + b) :
    Function.Injective (shiftCol a hL) := by
  intro c d h
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)

private theorem sum_univ_split {W : Type*} [AddCommMonoid W]
    {a b : ℕ} (f : Fin (a + b) → W) :
    (∑ c : Fin (a + b), f c) =
      (∑ c : Fin a, f (Fin.castAdd b c)) + ∑ c : Fin b, f (Fin.natAdd a c) := by
  rw [Fintype.sum_equiv finSumFinEquiv.symm f fun c => f (finSumFinEquiv.toFun c)]
  · apply Fintype.sum_sum_type
  · intro c
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

/-- Summands after the shifted cut reindex to the corresponding old tail. -/
theorem sum_tail_shift {W : Type*} [AddCommMonoid W]
    (a b j : ℕ) (f : Fin (a + b) → W) (g : Fin b → W)
    (hf : ∀ c : Fin b, j < c.val → f (Fin.natAdd a c) = g c) :
    (∑ c : Fin (a + b), if a + j < c.val then f c else 0) =
      ∑ c : Fin b, if j < c.val then g c else 0 := by
  simp only [sum_univ_split, Fin.coe_castAdd, Fin.coe_natAdd,
    Nat.add_lt_add_iff_left]
  have hleft : (∑ c : Fin a, if a + j < c.val then f (Fin.castAdd b c) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    exact if_neg (not_lt_of_ge (c.isLt.le.trans (Nat.le_add_right a j)))
  rw [hleft, zero_add]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hj
  · exact hf c hj
  · rfl

/-- The same reindexing with a separately presented total width. -/
theorem sum_tail_shift_of_eq {W : Type*} [AddCommMonoid W]
    (a b j : ℕ) {L : ℕ} (hL : L = a + b) (f : Fin L → W) (g : Fin b → W)
    (hf : ∀ c : Fin b, j < c.val → f (shiftCol a hL c) = g c) :
    (∑ c : Fin L, if a + j < c.val then f c else 0) =
      ∑ c : Fin b, if j < c.val then g c else 0 := by
  subst L
  exact sum_tail_shift a b j f g hf

#print axioms shiftCol_val
#print axioms shiftCol_eq_natAdd
#print axioms shiftCol_injective
#print axioms sum_tail_shift
#print axioms sum_tail_shift_of_eq

end ColumnTailSums
