import FiniteTransfer

/-!
# Concatenating and observing exact labelled paths

These operations use the existing dependent path type. Sequence construction
retains the supplied state order and every supplied local label. A uniform
observation of each label recovers precisely the original indexed values.
No finiteness, connectivity, or counting assumption is needed here.
-/

namespace CylinderTransfer.LabelledPath

universe u v w

variable {S : Type u} {E : S → S → Type v}

/-- Concatenate two paths, preserving their order and every local choice. -/
def append {n k : ℕ} {i j l : S}
    (p : LabelledPath E n i j) (q : LabelledPath E k j l) :
    LabelledPath E (n + k) i l := by
  induction n generalizing i with
  | zero =>
      have hij := p.down.down
      cases hij
      simpa only [Nat.zero_add] using q
  | succ n ih =>
      obtain ⟨a, e, p⟩ := p
      rw [Nat.succ_add]
      exact ⟨a, e, ih p⟩

/-- Build the exact path described by consecutive states and their labels. -/
def ofSequence (E : S → S → Type v) :
    (n : ℕ) → (state : Fin (n + 1) → S) →
    ((i : Fin n) → E (state i.castSucc) (state i.succ)) →
    LabelledPath E n (state 0) (state (Fin.last n))
  | 0, _, _ => ⟨⟨rfl⟩⟩
  | n + 1, state, edge =>
      ⟨state (Fin.succ 0), edge 0,
        ofSequence E n (fun i => state i.succ) (fun i => edge i.succ)⟩

/-- Observe each local label in a common type without discarding path order. -/
def observe {W : Type w} (value : ∀ i j, E i j → W) :
    {n : ℕ} → {i j : S} → LabelledPath E n i j → Fin n → W
  | 0, _, _, _, q => Fin.elim0 q
  | _ + 1, i, _, ⟨a, e, p⟩, q =>
      Fin.cases (value i a e) (observe value p) q

/-- Every observed local value is exactly the value of the supplied label. -/
theorem observe_ofSequence {W : Type w} (value : ∀ i j, E i j → W)
    (n : ℕ) (state : Fin (n + 1) → S)
    (edge : (i : Fin n) → E (state i.castSucc) (state i.succ)) :
    observe value (ofSequence E n state edge) =
      fun i => value (state i.castSucc) (state i.succ) (edge i) := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact congrFun (ih (fun i => state i.succ) (fun i => edge i.succ)) i

/-- Existence of consecutive labels gives an exact-length path. -/
theorem nonempty_ofSequence (n : ℕ) (state : Fin (n + 1) → S)
    (edge : (i : Fin n) → E (state i.castSucc) (state i.succ)) :
    Nonempty (LabelledPath E n (state 0) (state (Fin.last n))) :=
  ⟨ofSequence E n state edge⟩

/-- Concatenation composes existence at the sum of the two lengths. -/
theorem nonempty_append {n k : ℕ} {i j l : S}
    (hp : Nonempty (LabelledPath E n i j))
    (hq : Nonempty (LabelledPath E k j l)) :
    Nonempty (LabelledPath E (n + k) i l) := by
  obtain ⟨p⟩ := hp
  obtain ⟨q⟩ := hq
  exact ⟨append p q⟩

end CylinderTransfer.LabelledPath
