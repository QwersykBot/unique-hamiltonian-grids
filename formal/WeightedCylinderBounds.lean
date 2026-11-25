import WeightedCylinderEncoding
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Uniform bounds for actual physical cylinder weights

Only weights of ambient edges are bounded. The frozen physical factors and
weighted matrix/vector definitions are used unchanged, at their specified
column positions. No invariance under a row or column translation is assumed.
-/

namespace TriangularCylinder.WeightedCylinderBounds

open SimpleGraph Transfer TriangularEdgeEncoding CylinderTransfer
open scoped BigOperators Matrix

private theorem maskedFactor_bounds {epsilon M x : ℝ}
    (hx : epsilon ≤ x ∧ x ≤ M) (mask : Bool) :
    min 1 epsilon ≤ (if mask then x else 1) ∧
      (if mask then x else 1) ≤ max 1 M := by
  cases mask
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩

private theorem maskedProduct_bounds {q : ℕ} {epsilon M : ℝ}
    (hepsilon : 0 < epsilon) (mask : Fin q → Bool) (weight : Fin q → ℝ)
    (hw : ∀ r, epsilon ≤ weight r ∧ weight r ≤ M) :
    (min 1 epsilon) ^ q ≤ (∏ r : Fin q, if mask r then weight r else 1) ∧
      (∏ r : Fin q, if mask r then weight r else 1) ≤ (max 1 M) ^ q := by
  have hlo : 0 < min (1 : ℝ) epsilon := lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩
  have hfactor := fun r => maskedFactor_bounds (hw r) (mask r)
  constructor
  · calc
      _ = ∏ _r : Fin q, min (1 : ℝ) epsilon := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlo.le) (fun r _ => (hfactor r).1)
  · calc
      _ ≤ ∏ _r : Fin q, max (1 : ℝ) M :=
        Finset.prod_le_prod (fun r _ => hlo.le.trans (hfactor r).1)
          (fun r _ => (hfactor r).2)
      _ = _ := by simp

private theorem mul_pow_bounds {lo hi x y : ℝ} {p q : ℕ}
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hx : lo ^ p ≤ x ∧ x ≤ hi ^ p) (hy : lo ^ q ≤ y ∧ y ≤ hi ^ q) :
    lo ^ (p + q) ≤ x * y ∧ x * y ≤ hi ^ (p + q) := by
  constructor
  · rw [pow_add]
    exact mul_le_mul hx.1 hy.1 (pow_nonneg hlo q) ((pow_nonneg hlo p).trans hx.1)
  · rw [pow_add]
    exact mul_le_mul hx.2 hy.2 ((pow_nonneg hlo q).trans hy.1) (pow_nonneg hhi p)

/-- Each selected vertical factor is bounded using only ambient-edge hypotheses. -/
theorem verticalFactor_bounds {m L : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m L) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m L hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (c : Fin L) (mask : RowMask m) :
    (min 1 epsilon) ^ m ≤ verticalFactor hm w c mask ∧
      verticalFactor hm w c mask ≤ (max 1 M) ^ m :=
  maskedProduct_bounds hepsilon mask _
    (fun r => hw _ (toEdge_mem_edgeSet hm (.inl (r, c))))

/-- A cut has two masked physical factors per row, at that same cut. -/
theorem cutFactor_bounds {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (c : Fin (n + 1)) (horizontal diagonal : RowMask m) :
    (min 1 epsilon) ^ (2 * m) ≤ cutFactor hm w c horizontal diagonal ∧
      cutFactor hm w c horizontal diagonal ≤ (max 1 M) ^ (2 * m) := by
  have hH := maskedProduct_bounds hepsilon horizontal
    (fun r => w (toEdge hm (.inr (.inl (r, cutEdgeIndex c)))))
    (fun r => hw _ (toEdge_mem_edgeSet hm (.inr (.inl (r, cutEdgeIndex c)))))
  have hD := maskedProduct_bounds hepsilon diagonal
    (fun r => w (toEdge hm (.inr (.inr (r, cutEdgeIndex c)))))
    (fun r => hw _ (toEdge_mem_edgeSet hm (.inr (.inr (r, cutEdgeIndex c)))))
  have hlo : 0 ≤ min (1 : ℝ) epsilon :=
    (lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩).le
  have hhi : 0 ≤ max (1 : ℝ) M := zero_le_one.trans (le_max_left _ _)
  simpa only [cutFactor, Finset.prod_mul_distrib, two_mul] using
    mul_pow_bounds hlo hhi hH hD

/-- The source H/D cut and new V mask use three factors per row. -/
theorem localPhysicalWeight_bounds {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (i : Fin n) (s t : CoreState hm) (label : LocalLabel hm s t) :
    (min 1 epsilon) ^ (3 * m) ≤ localPhysicalWeight hm w i s t label ∧
      localPhysicalWeight hm w i s t label ≤ (max 1 M) ^ (3 * m) := by
  have hcut := cutFactor_bounds hm w hepsilon hw i.castSucc s.val.horizontal s.val.diagonal
  have hvertical := verticalFactor_bounds hm w hepsilon hw i.succ.castSucc label.val
  have hlo : 0 ≤ min (1 : ℝ) epsilon :=
    (lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩).le
  have hhi : 0 ≤ max (1 : ℝ) M := zero_le_one.trans (le_max_left _ _)
  have hthree : 2 * m + m = 3 * m := by omega
  simpa only [localPhysicalWeight, hthree] using mul_pow_bounds hlo hhi hcut hvertical

/-- The terminal cut and final V mask have the same three-factor bound. -/
theorem terminalPhysicalWeight_bounds {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    {p : ZMod 2} (s : CoreState hm) (label : TerminalLabel hm p s) :
    (min 1 epsilon) ^ (3 * m) ≤ terminalPhysicalWeight hm w s label ∧
      terminalPhysicalWeight hm w s label ≤ (max 1 M) ^ (3 * m) := by
  have hcut := cutFactor_bounds hm w hepsilon hw (Fin.last n) s.val.horizontal s.val.diagonal
  have hvertical := verticalFactor_bounds hm w hepsilon hw (Fin.last (n + 1)) label.val
  have hlo : 0 ≤ min (1 : ℝ) epsilon :=
    (lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩).le
  have hhi : 0 ≤ max (1 : ℝ) M := zero_le_one.trans (le_max_left _ _)
  have hthree : 2 * m + m = 3 * m := by omega
  simpa only [terminalPhysicalWeight, hthree] using mul_pow_bounds hlo hhi hcut hvertical

theorem initialPhysicalWeight_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (s : CoreState hm) (label : InitialLabel hm s) :
    0 ≤ initialPhysicalWeight hm w s label :=
  (pow_pos (lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩) m).le.trans
    (verticalFactor_bounds hm w hepsilon hw 0 label.val).1

theorem localPhysicalWeight_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (i : Fin n) (s t : CoreState hm) (label : LocalLabel hm s t) :
    0 ≤ localPhysicalWeight hm w i s t label :=
  (pow_pos (lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩) (3 * m)).le.trans
    (localPhysicalWeight_bounds hm w hepsilon hw i s t label).1

theorem terminalPhysicalWeight_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    {p : ZMod 2} (s : CoreState hm) (label : TerminalLabel hm p s) :
    0 ≤ terminalPhysicalWeight hm w s label :=
  (pow_pos (lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩) (3 * m)).le.trans
    (terminalPhysicalWeight_bounds hm w hepsilon hw s label).1

/-- Only a vertical row mask is counted; actual witnesses contribute no multiplicity. -/
theorem localLabel_card_le {m : ℕ} (hm : 3 ≤ m) (s t : CoreState hm) :
    Fintype.card (LocalLabel hm s t) ≤ 2 ^ m := by
  classical
  calc
    _ ≤ Fintype.card (RowMask m) :=
      Fintype.card_le_of_injective (fun label : LocalLabel hm s t => label.val)
        (fun _ _ h => Subtype.ext h)
    _ = _ := by simp only [RowMask, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The uniform lower/upper constants satisfy the contraction interface. -/
theorem constants_pos_le (m : ℕ) {epsilon M : ℝ} (hepsilon : 0 < epsilon) :
    0 < (min 1 epsilon) ^ (3 * m) ∧
      (min 1 epsilon) ^ (3 * m) ≤ (2 : ℝ) ^ m * (max 1 M) ^ (3 * m) := by
  have hlo : 0 < min (1 : ℝ) epsilon := lt_min_iff.mpr ⟨zero_lt_one, hepsilon⟩
  have ha : (min 1 epsilon) ^ (3 * m) ≤ 1 := pow_le_one₀ hlo.le (min_le_left _ _)
  have htwo : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hhi : (1 : ℝ) ≤ (max 1 M) ^ (3 * m) := one_le_pow₀ (le_max_left _ _)
  refine ⟨pow_pos hlo _, ha.trans ?_⟩
  simpa only [one_mul] using mul_le_mul htwo hhi zero_le_one (zero_le_one.trans htwo)

theorem weightedTransitionMatrix_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (i : Fin n) (s t : CoreState hm) :
    0 ≤ weightedTransitionMatrix (LocalLabel hm) (localPhysicalWeight hm w i) s t := by
  change 0 ≤ ∑ label : LocalLabel hm s t, localPhysicalWeight hm w i s t label
  exact Finset.sum_nonneg (fun label _ => localPhysicalWeight_nonneg hm w hepsilon hw i s t label)

/-- Positive unweighted label support gives a uniformly positive weighted entry. -/
theorem weightedTransitionMatrix_lower {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (i : Fin n) (s t : CoreState hm)
    (hsupport : 0 < realTransitionMatrix (LocalLabel hm) s t) :
    (min 1 epsilon) ^ (3 * m) ≤
      weightedTransitionMatrix (LocalLabel hm) (localPhysicalWeight hm w i) s t := by
  change 0 < (Fintype.card (LocalLabel hm s t) : ℝ) at hsupport
  obtain ⟨label⟩ := Fintype.card_pos_iff.mp (Nat.cast_pos.mp hsupport)
  change _ ≤ ∑ a : LocalLabel hm s t, localPhysicalWeight hm w i s t a
  exact (localPhysicalWeight_bounds hm w hepsilon hw i s t label).1.trans
    (Finset.single_le_sum (fun a _ => localPhysicalWeight_nonneg hm w hepsilon hw i s t a)
      (Finset.mem_univ label))

theorem weightedTransitionMatrix_upper {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (i : Fin n) (s t : CoreState hm) :
    weightedTransitionMatrix (LocalLabel hm) (localPhysicalWeight hm w i) s t ≤
      (2 : ℝ) ^ m * (max 1 M) ^ (3 * m) := by
  have hcard : (Fintype.card (LocalLabel hm s t) : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast localLabel_card_le hm s t
  have hhi : 0 ≤ max (1 : ℝ) M := zero_le_one.trans (le_max_left _ _)
  change (∑ label : LocalLabel hm s t, localPhysicalWeight hm w i s t label) ≤ _
  calc
    _ ≤ ∑ _label : LocalLabel hm s t, (max 1 M) ^ (3 * m) :=
      Finset.sum_le_sum (fun label _ => (localPhysicalWeight_bounds hm w hepsilon hw i s t label).2)
    _ = (Fintype.card (LocalLabel hm s t) : ℝ) * (max 1 M) ^ (3 * m) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hhi _)

theorem weightedInitialVector_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (s : CoreState hm) :
    0 ≤ weightedInitialVector (InitialLabel hm) (initialPhysicalWeight hm w) s := by
  change 0 ≤ ∑ label : InitialLabel hm s, initialPhysicalWeight hm w s label
  exact Finset.sum_nonneg (fun label _ => initialPhysicalWeight_nonneg hm w hepsilon hw s label)

theorem weightedTerminalVector_nonneg {m n : ℕ} {epsilon M : ℝ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → ℝ) (hepsilon : 0 < epsilon)
    (hw : ∀ e ∈ (graph m (n + 2) hm).edgeSet, epsilon ≤ w e ∧ w e ≤ M)
    (p : ZMod 2) (s : CoreState hm) :
    0 ≤ weightedTerminalVector (TerminalLabel hm p) (terminalPhysicalWeight hm w) s := by
  change 0 ≤ ∑ label : TerminalLabel hm p s, terminalPhysicalWeight hm w s label
  exact Finset.sum_nonneg (fun label _ => terminalPhysicalWeight_nonneg hm w hepsilon hw s label)

#print axioms verticalFactor_bounds
#print axioms cutFactor_bounds
#print axioms localPhysicalWeight_bounds
#print axioms terminalPhysicalWeight_bounds
#print axioms initialPhysicalWeight_nonneg
#print axioms localPhysicalWeight_nonneg
#print axioms terminalPhysicalWeight_nonneg
#print axioms localLabel_card_le
#print axioms constants_pos_le
#print axioms weightedTransitionMatrix_nonneg
#print axioms weightedTransitionMatrix_lower
#print axioms weightedTransitionMatrix_upper
#print axioms weightedInitialVector_nonneg
#print axioms weightedTerminalVector_nonneg

end TriangularCylinder.WeightedCylinderBounds
