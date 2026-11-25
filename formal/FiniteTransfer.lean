import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Finite labelled transfer paths

Paths are actual dependent choices of states and local labels. Their cardinalities
are proved to be matrix powers; they are not defined by that formula.
-/

open scoped BigOperators Matrix

namespace CylinderTransfer

universe u v w z

variable {S : Type u}

/-- An exact-length path, with a distinct local label at each step. -/
def LabelledPath (E : S → S → Type v) : ℕ → S → S → Type (max u v)
  | 0, i, j => ULift (PLift (i = j))
  | n + 1, i, j => Σ k : S, E i k × LabelledPath E n k j

variable [Fintype S] [DecidableEq S]
variable (E : S → S → Type v) [∀ i j, Fintype (E i j)]

instance labelledPathFintype (n : ℕ) (i j : S) : Fintype (LabelledPath E n i j) := by
  induction n generalizing i j with
  | zero => unfold LabelledPath; infer_instance
  | succ n ih =>
    letI (k : S) : Fintype (LabelledPath E n k j) := ih k j
    unfold LabelledPath
    infer_instance

/-- The entry counts distinct allowed labels, including parallel labels or loops. -/
def transitionMatrix : Matrix S S ℕ := Matrix.of fun i j => Fintype.card (E i j)

omit [Fintype S] [DecidableEq S] in
@[simp] theorem transitionMatrix_apply (i j : S) :
    transitionMatrix E i j = Fintype.card (E i j) := rfl

/-- A zero-length path exists exactly when its endpoints coincide. -/
theorem card_labelledPath_zero (i j : S) :
    Fintype.card (LabelledPath E 0 i j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    letI : Subsingleton (LabelledPath E 0 i i) := by
      unfold LabelledPath
      infer_instance
    letI : Unique (LabelledPath E 0 i i) :=
      { default := ⟨⟨rfl⟩⟩
        uniq := fun _ => Subsingleton.elim _ _ }
    simp
  · letI : IsEmpty (LabelledPath E 0 i j) := ⟨fun p => h p.down.down⟩
    simp [h]

/-- The first local label precedes the shorter path in the ordered recurrence. -/
theorem card_labelledPath_succ (n : ℕ) (i j : S) :
    Fintype.card (LabelledPath E (n + 1) i j) =
      ∑ k : S, Fintype.card (E i k) * Fintype.card (LabelledPath E n k j) := by
  simp only [LabelledPath, Fintype.card_sigma, Fintype.card_prod]

/-- Counting the recursively defined labelled paths gives the matrix power. -/
theorem card_labelledPath (n : ℕ) (i j : S) :
    Fintype.card (LabelledPath E n i j) = (transitionMatrix E ^ n) i j := by
  induction n generalizing i j with
  | zero => simp [card_labelledPath_zero, Matrix.one_apply]
  | succ n ih =>
    simp only [card_labelledPath_succ, ih, pow_succ', Matrix.mul_apply,
      transitionMatrix_apply]

/-- The same multiplicity matrix with real coefficients. -/
def realTransitionMatrix : Matrix S S ℝ :=
  (transitionMatrix E).map (Nat.castRingHom ℝ)

theorem realTransitionMatrix_pow (n : ℕ) :
    realTransitionMatrix E ^ n =
      (transitionMatrix E ^ n).map (Nat.castRingHom ℝ) := by
  induction n with
  | zero =>
    ext i j
    simp [Matrix.one_apply, Matrix.map_apply]
  | succ n ih =>
    rw [pow_succ', ih, pow_succ', Matrix.map_mul]
    rfl

/-- Casting the natural-number count yields the real transfer entry. -/
theorem card_labelledPath_real (n : ℕ) (i j : S) :
    (Fintype.card (LabelledPath E n i j) : ℝ) =
      (realTransitionMatrix E ^ n) i j := by
  rw [card_labelledPath, realTransitionMatrix_pow]
  rfl

/-- An accepted object includes its initial, every local, and its terminal label. -/
def Accepted (I : S → Type w) (F : S → Type z) (n : ℕ) :=
  Σ i : S, I i × Σ j : S, LabelledPath E n i j × F j

variable (I : S → Type w) (F : S → Type z)
variable [∀ i, Fintype (I i)] [∀ j, Fintype (F j)]

instance acceptedFintype (n : ℕ) : Fintype (Accepted E I F n) := by
  unfold Accepted
  infer_instance

def initialVector : S → ℕ := fun i => Fintype.card (I i)

def terminalVector : S → ℕ := fun j => Fintype.card (F j)

/-- The scalar transfer formula, with the initial vector on the left. -/
theorem card_accepted (n : ℕ) :
    Fintype.card (Accepted E I F n) =
      initialVector I ⬝ᵥ ((transitionMatrix E ^ n) *ᵥ terminalVector F) := by
  simp only [Accepted, Fintype.card_sigma, Fintype.card_prod, card_labelledPath,
    initialVector, terminalVector, dotProduct, Matrix.mulVec]

/-- At length zero, the initial and terminal choices must be at the same state. -/
theorem card_accepted_zero :
    Fintype.card (Accepted E I F 0) =
      ∑ i : S, Fintype.card (I i) * Fintype.card (F i) := by
  simpa [initialVector, terminalVector, dotProduct] using card_accepted E I F 0

/-- The real scalar formula is an exact cast of the finite counting theorem. -/
theorem card_accepted_real (n : ℕ) :
    (Fintype.card (Accepted E I F n) : ℝ) =
      (fun i => (Fintype.card (I i) : ℝ)) ⬝ᵥ
        ((realTransitionMatrix E ^ n) *ᵥ fun j => (Fintype.card (F j) : ℝ)) := by
  rw [card_accepted]
  simp [initialVector, terminalVector, dotProduct, Matrix.mulVec,
    realTransitionMatrix_pow, Matrix.map_apply]

end CylinderTransfer
