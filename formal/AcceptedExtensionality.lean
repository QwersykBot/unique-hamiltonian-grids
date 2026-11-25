import CycleAccepted

/-!
# Exact observations distinguish accepted objects

A labelled path is determined by its successive target states and injective
label values. For the actual cylinder labels, the subtype value is the
physical vertical mask. Thus all cut states and all vertical masks determine
an accepted object, without a chosen Hamiltonian presentation. Each observed
step also retains the original label's realization predicate.
-/

namespace CylinderTransfer.LabelledPath

universe u v w

variable {S : Type u} {E : S → S → Type v}

/-- The last observed state is the actual terminal state, also at length zero. -/
theorem last_observed_state {n : ℕ} {i j : S} (p : LabelledPath E n i j) :
    Fin.cases i (observe (fun _ t _ => t) p) (Fin.last n) = j := by
  induction n generalizing i with
  | zero => exact p.down.down
  | succ n ih =>
      obtain ⟨a, e, p⟩ := p
      change Fin.cases a (observe (fun _ t _ => t) p) (Fin.last n) = j
      exact ih p

/-- Injective label observations and successive targets recover the whole path. -/
theorem eq_of_observations {W : Type w} (value : ∀ i j, E i j → W)
    (hvalue : ∀ i j, Function.Injective (value i j))
    {n : ℕ} {i j : S} (p q : LabelledPath E n i j)
    (htarget : observe (fun _ t _ => t) p = observe (fun _ t _ => t) q)
    (hlabel : observe value p = observe value q) : p = q := by
  induction n generalizing i with
  | zero =>
      exact @Subsingleton.elim (ULift (PLift (i = j))) inferInstance p q
  | succ n ih =>
      obtain ⟨a, e, p⟩ := p
      obtain ⟨b, f, q⟩ := q
      have hab : a = b := congrFun htarget 0
      subst b
      have hef : e = f := hvalue i a (congrFun hlabel 0)
      subst f
      have hp : p = q := ih p q
        (funext fun x => congrFun htarget x.succ)
        (funext fun x => congrFun hlabel x.succ)
      subst q
      rfl

/-- Every observed step retains any predicate satisfied by its actual label. -/
theorem observed_step {W : Type w} (value : ∀ i j, E i j → W)
    (P : S → S → W → Prop) (hP : ∀ i j e, P i j (value i j e))
    {n : ℕ} {i j : S} (p : LabelledPath E n i j) (c : Fin n) :
    P (Fin.cases i (observe (fun _ t _ => t) p) c.castSucc)
      (Fin.cases i (observe (fun _ t _ => t) p) c.succ)
      (observe value p c) := by
  induction n generalizing i with
  | zero => exact Fin.elim0 c
  | succ n ih =>
      obtain ⟨a, e, p⟩ := p
      refine Fin.cases ?_ (fun c => ?_) c
      · exact hP i a e
      · exact ih p c

end CylinderTransfer.LabelledPath

namespace TriangularCylinder.Transfer

/-- The last cut observed in an accepted object is its stated terminal state. -/
theorem acceptedCutStates_last {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    acceptedCutStates w (Fin.last n) = w.2.2.1 :=
  CylinderTransfer.LabelledPath.last_observed_state w.2.2.2.1

/-- The first observed column and cut retain the actual initial-label witness. -/
theorem accepted_initial_realized {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    InitialRealized hm (acceptedCutStates w 0) (acceptedVerticalMasks w 0) :=
  w.2.1.property

/-- Each observed transition retains its actual local realization witness. -/
theorem accepted_local_realized {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) (c : Fin n) :
    LocalRealized hm (acceptedCutStates w c.castSucc) (acceptedCutStates w c.succ)
      (acceptedVerticalMasks w c.succ.castSucc) := by
  have h := CylinderTransfer.LabelledPath.observed_step
    (fun _ _ e => e.val) (LocalRealized hm) (fun _ _ e => e.property) w.2.2.2.1 c
  change LocalRealized hm (acceptedCutStates w c.castSucc) (acceptedCutStates w c.succ)
    (acceptedVerticalMasks w c.castSucc.succ)
  simpa only [acceptedCutStates, acceptedVerticalMasks, Fin.cases_succ,
    Fin.lastCases_castSucc, acceptedLocalMasks] using h

/-- The final observed column and cut retain the actual terminal-label witness. -/
theorem accepted_terminal_realized {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : AcceptedObject hm p n) :
    TerminalRealized hm p (acceptedCutStates w (Fin.last n))
      (acceptedVerticalMasks w (Fin.last (n + 1))) := by
  rw [acceptedCutStates_last]
  change TerminalRealized hm p w.2.2.1 (acceptedVerticalMasks w (Fin.last n).succ)
  simpa only [acceptedVerticalMasks, Fin.cases_succ, Fin.lastCases_last,
    acceptedTerminalMask] using w.2.2.2.2.property

/-- Exact states and physical vertical masks distinguish all accepted data. -/
theorem accepted_ext {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w z : AcceptedObject hm p n)
    (hstate : acceptedCutStates w = acceptedCutStates z)
    (hvertical : acceptedVerticalMasks w = acceptedVerticalMasks z) : w = z := by
  obtain ⟨i, vi, j, path, vj⟩ := w
  obtain ⟨i', vi', j', path', vj'⟩ := z
  have hi : i = i' := congrFun hstate 0
  subst i'
  have hj : j = j' := by
    have h := congrFun hstate (Fin.last n)
    simpa only [acceptedCutStates_last] using h
  subst j'
  have hvi : vi = vi' := Subtype.ext (congrFun hvertical 0)
  subst vi'
  have hvj : vj = vj' := by
    apply Subtype.ext
    have h := congrFun hvertical (Fin.last n).succ
    simpa only [acceptedVerticalMasks, Fin.cases_succ,
      Fin.lastCases_last, acceptedTerminalMask] using h
  subst vj'
  have hpath : path = path' := by
    apply CylinderTransfer.LabelledPath.eq_of_observations
      (fun _ _ e => e.val) (fun _ _ => Subtype.val_injective)
    · exact funext fun c => congrFun hstate c.succ
    · funext c
      have h := congrFun hvertical c.castSucc.succ
      simpa only [acceptedVerticalMasks, Fin.cases_succ,
        Fin.lastCases_castSucc, acceptedLocalMasks] using h
  subst path'
  rfl

end TriangularCylinder.Transfer
