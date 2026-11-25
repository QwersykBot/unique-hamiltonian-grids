import FiniteTransferPaths
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Weighted finite labelled paths and ordered transfer products

Weights are assigned to the actual initial, local, and terminal labels of
the existing finite accepted objects. Local weights may vary with the step
position. Their finite sums are proved to equal the corresponding ordered
matrix product; neither the objects nor their weights are defined by that
matrix expression. No positivity or geometric realization is assumed.
-/

open scoped BigOperators Matrix

namespace CylinderTransfer

universe u v w z r q

variable {S : Type u} (E : S → S → Type v)
variable {R : Type r} [CommSemiring R]

/-- Multiply the actual local-label weights in increasing step order. -/
def labelledPathWeight : {n : ℕ} → (Fin n → ∀ i j, E i j → R) →
    {i j : S} → LabelledPath E n i j → R
  | 0, _, _, _, _ => 1
  | n + 1, weight, i, _, ⟨k, edge, path⟩ =>
      weight 0 i k edge * labelledPathWeight (fun t : Fin n => weight t.succ) path

/-- Initial and terminal labels retain their own independent weights. -/
def acceptedWeight (I : S → Type w) (F : S → Type z) {n : ℕ}
    (initialWeight : ∀ i, I i → R)
    (localWeight : Fin n → ∀ i j, E i j → R)
    (terminalWeight : ∀ j, F j → R) (a : Accepted E I F n) : R :=
  initialWeight a.1 a.2.1 * labelledPathWeight E localWeight a.2.2.2.1 *
    terminalWeight a.2.2.1 a.2.2.2.2

/-- Position-dependent weights can be read through the existing uniform
label observer without introducing a second path representation. -/
theorem labelledPathWeight_eq_prod_observe {W : Type q}
    (value : ∀ i j, E i j → W) {n : ℕ} (weight : Fin n → W → R)
    {i j : S} (path : LabelledPath E n i j) :
    labelledPathWeight E (fun k i j edge => weight k (value i j edge)) path =
      ∏ k : Fin n, weight k (LabelledPath.observe value path k) := by
  induction n generalizing i with
  | zero => simp [labelledPathWeight]
  | succ n ih =>
    obtain ⟨k, edge, path⟩ := path
    rw [labelledPathWeight, Fin.prod_univ_succ]
    change weight 0 (value i k edge) *
        labelledPathWeight E (fun t i j e => weight t.succ (value i j e)) path =
      weight 0 (value i k edge) *
        ∏ t : Fin n, weight t.succ (LabelledPath.observe value path t)
    rw [ih]

variable [Fintype S] [DecidableEq S] [∀ i j, Fintype (E i j)]

/-- Each entry sums the distinct local labels at one specified position. -/
def weightedTransitionMatrix (weight : ∀ i j, E i j → R) : Matrix S S R :=
  Matrix.of fun i j => ∑ edge : E i j, weight i j edge

/-- Zero-length weights sum to the identity entry: the actual path type
contains exactly the equality of its two endpoints. -/
theorem sum_labelledPathWeight_zero (weight : Fin 0 → ∀ i j, E i j → R) (i j : S) :
    (∑ path : LabelledPath E 0 i j, labelledPathWeight E weight path) =
      if i = j then 1 else 0 := by
  simp [labelledPathWeight, card_labelledPath_zero]

/-- Decomposing an actual successor path gives the first factor on the left. -/
theorem sum_labelledPathWeight_succ (n : ℕ)
    (weight : Fin (n + 1) → ∀ i j, E i j → R) (i j : S) :
    (∑ path : LabelledPath E (n + 1) i j, labelledPathWeight E weight path) =
      ∑ k : S, (∑ edge : E i k, weight 0 i k edge) *
        ∑ path : LabelledPath E n k j,
          labelledPathWeight E (fun t : Fin n => weight t.succ) path := by
  change (∑ p : Σ k : S, E i k × LabelledPath E n k j,
    weight 0 i p.1 p.2.1 *
      labelledPathWeight E (fun t : Fin n => weight t.succ) p.2.2) = _
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Summing actual path weights gives the ordered product of the separately
summed transition matrices. No pairwise matrix commutation is required. -/
theorem sum_labelledPathWeight {n : ℕ}
    (weight : Fin n → ∀ i j, E i j → R) (i j : S) :
    (∑ path : LabelledPath E n i j, labelledPathWeight E weight path) =
      (List.ofFn (fun k => weightedTransitionMatrix E (weight k))).prod i j := by
  induction n generalizing i j with
  | zero =>
    simpa only [List.ofFn_zero, List.prod_nil, Matrix.one_apply] using
      sum_labelledPathWeight_zero E weight i j
  | succ n ih =>
    rw [sum_labelledPathWeight_succ, List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih]
    rfl

variable (I : S → Type w) (F : S → Type z)
variable [∀ i, Fintype (I i)] [∀ j, Fintype (F j)]

def weightedInitialVector (weight : ∀ i, I i → R) : S → R :=
  fun i => ∑ initial : I i, weight i initial

def weightedTerminalVector (weight : ∀ j, F j → R) : S → R :=
  fun j => ∑ terminal : F j, weight j terminal

/-- The finite sum over accepted objects is the scalar ordered transfer
product, with independent initial and terminal weight vectors. -/
theorem sum_acceptedWeight {n : ℕ}
    (initialWeight : ∀ i, I i → R)
    (localWeight : Fin n → ∀ i j, E i j → R)
    (terminalWeight : ∀ j, F j → R) :
    (∑ a : Accepted E I F n, acceptedWeight E I F initialWeight localWeight terminalWeight a) =
      weightedInitialVector I initialWeight ⬝ᵥ
        ((List.ofFn (fun k => weightedTransitionMatrix E (localWeight k))).prod *ᵥ
          weightedTerminalVector F terminalWeight) := by
  simp only [Accepted, acceptedWeight, Fintype.sum_sigma, Fintype.sum_prod_type,
    weightedInitialVector, weightedTerminalVector, dotProduct, Matrix.mulVec]
  simp_rw [← sum_labelledPathWeight E localWeight]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]

/-- At length zero, the two boundary labels are at the same state and
there is no local factor. -/
theorem sum_acceptedWeight_zero
    (initialWeight : ∀ i, I i → R)
    (localWeight : Fin 0 → ∀ i j, E i j → R)
    (terminalWeight : ∀ j, F j → R) :
    (∑ a : Accepted E I F 0, acceptedWeight E I F initialWeight localWeight terminalWeight a) =
      ∑ i : S, (∑ initial : I i, initialWeight i initial) *
        ∑ terminal : F i, terminalWeight i terminal := by
  simpa only [List.ofFn_zero, List.prod_nil, Matrix.one_mulVec, dotProduct,
    weightedInitialVector, weightedTerminalVector] using
    sum_acceptedWeight E I F initialWeight localWeight terminalWeight

end CylinderTransfer
