import ExteriorGeometry

/-!
# Exact physical exterior-event transport

The complete selected-and-absent exterior event is equivalent to the
once-only initial, local and terminal mask filters. The filtered accepted
weight is then the actual physical edge product times that event indicator.
The existing counted bijection transports the physical sum to the ordered
product of the separately filtered label sums.
-/

open scoped BigOperators Matrix

namespace TriangularCylinder.Transfer

open CountedHamiltonian TriangularEdgeEncoding

/-- Physical exterior agreement is exactly Boolean agreement on the
prescribed physical IDs, including IDs marked absent. -/
theorem exteriorAgrees_realizedEdges_iff {m n : ℕ} (hm : 3 ≤ m)
    (σ g : ColumnGeometry m (n + 2)) (a b : ℕ) :
    ExteriorAgrees hm σ a b (realizedEdges hm g) ↔
      GeometryExteriorAgrees σ a b g := by
  unfold ExteriorAgrees GeometryExteriorAgrees
  constructor
  · intro h id hi
    apply Bool.eq_iff_iff.mpr
    exact (mem_realizedEdges_iff hm g id).symm.trans (h id hi)
  · intro h id hi
    rw [mem_realizedEdges_iff, h id hi]

/-- Every physical exterior ID belongs to exactly the indicated initial,
local or terminal mask block. Free prescription entries are never tested. -/
theorem geometryExteriorAgrees_iff_ownedMasks {m n : ℕ}
    (σ g : ColumnGeometry m (n + 2)) (a b : ℕ) (hbn : b ≤ n) :
    GeometryExteriorAgrees σ a b g ↔
      g.1 0 = σ.1 0 ∧
      (∀ i : Fin n, ¬ freeLocalSlot a b i.val →
        localMaskAgreement σ i (g.2.1 (cutEdgeIndex i.castSucc))
          (g.2.2 (cutEdgeIndex i.castSucc)) (g.1 i.succ.castSucc)) ∧
      terminalMaskAgreement σ (g.2.1 (cutEdgeIndex (Fin.last n)))
        (g.2.2 (cutEdgeIndex (Fin.last n))) (g.1 (Fin.last (n + 1))) := by
  have hlast : ¬ freeLocalSlot a b n := by
    unfold freeLocalSlot
    omega
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext r
      exact h (.inl (r, 0)) (by simp [freePhysicalId])
    · intro i hi
      refine ⟨?_, ?_, ?_⟩
      · funext r
        exact h (.inr (.inl (r, cutEdgeIndex i.castSucc))) hi
      · funext r
        exact h (.inr (.inr (r, cutEdgeIndex i.castSucc))) hi
      · funext r
        exact h (.inl (r, i.succ.castSucc)) (by simpa [freePhysicalId] using hi)
    · refine ⟨?_, ?_, ?_⟩
      · funext r
        exact h (.inr (.inl (r, cutEdgeIndex (Fin.last n)))) hlast
      · funext r
        exact h (.inr (.inr (r, cutEdgeIndex (Fin.last n)))) hlast
      · funext r
        exact h (.inl (r, Fin.last (n + 1))) (by simpa [freePhysicalId] using hlast)
  · rintro ⟨hfirst, hlocal, hterminal⟩ id
    rcases id with ⟨r, c⟩ | (⟨r, c⟩ | ⟨r, c⟩)
    · refine Fin.cases ?_ (fun c => ?_) c
      · intro _
        exact congrFun hfirst r
      · refine Fin.lastCases ?_ (fun i => ?_) c
        · intro _
          exact congrFun hterminal.2.2 r
        · intro hi
          have hout : ¬ freeLocalSlot a b i.val := by
            simpa [freePhysicalId] using hi
          exact congrFun (hlocal i hout).2.2 r
    · refine Fin.lastCases ?_ (fun i => ?_) c
      · intro _
        exact congrFun hterminal.1 r
      · intro hi
        exact congrFun (hlocal i hi).1 r
    · refine Fin.lastCases ?_ (fun i => ?_) c
      · intro _
        exact congrFun hterminal.2.1 r
      · intro hi
        exact congrFun (hlocal i hi).2.1 r

/-- The exterior event on one accepted object's actual edges is equivalent
to the masks carried by that same object's three types of labels. -/
theorem exteriorAgrees_acceptedEdges_iff {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (σ : ColumnGeometry m (n + 2)) (a b : ℕ) (hbn : b ≤ n)
    (x : AcceptedObject hm p n) :
    ExteriorAgrees hm σ a b (acceptedEdges x) ↔
      x.2.1.val = σ.1 0 ∧
      (∀ i : Fin n, ¬ freeLocalSlot a b i.val →
        localMaskAgreement σ i (acceptedCutStates x i.castSucc).val.horizontal
          (acceptedCutStates x i.castSucc).val.diagonal (acceptedLocalMasks x i)) ∧
      terminalMaskAgreement σ x.2.2.1.val.horizontal
        x.2.2.1.val.diagonal x.2.2.2.2.val := by
  rw [acceptedEdges, exteriorAgrees_realizedEdges_iff,
    geometryExteriorAgrees_iff_ownedMasks σ _ a b hbn]
  have hindex (c : Fin (n + 1)) : cutEdgeIndex c = c := by
    apply Fin.ext
    rfl
  simp only [acceptedGeometry, ← Fin.succ_castSucc, ← Fin.succ_last,
    acceptedVerticalMasks, Fin.cases_zero, Fin.cases_succ,
    Fin.lastCases_castSucc, Fin.lastCases_last, acceptedCutStates_last,
    acceptedInitialMask, acceptedTerminalMask, hindex]

variable {R : Type*} [CommSemiring R]

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

noncomputable local instance {m : ℕ} (hm : 3 ≤ m) : DecidableEq (CoreState hm) :=
  Classical.decEq _

private theorem product_indicators {ι : Type*} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] [Decidable (∀ i, P i)] :
    (∏ i, if P i then (1 : R) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases hall : ∀ i, P i
  · simp [hall]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    rw [if_neg hall]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem observed_source_value {S W : Type*} {E : S → S → Type*}
    (value : ∀ s t, E s t → W) {n : ℕ} {s t : S}
    (path : CylinderTransfer.LabelledPath E n s t) (i : Fin n) :
    CylinderTransfer.LabelledPath.observe (fun s t z => (s, value s t z)) path i =
      (Fin.cases s (CylinderTransfer.LabelledPath.observe (fun _ t _ => t) path)
        i.castSucc, CylinderTransfer.LabelledPath.observe value path i) := by
  induction n generalizing s with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨u, z, path⟩ := path
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact ih path i

private theorem labelledPathWeight_mul {S : Type*} (E : S → S → Type*) {n : ℕ}
    (f g : Fin n → ∀ s t, E s t → R) {s t : S}
    (path : CylinderTransfer.LabelledPath E n s t) :
    CylinderTransfer.labelledPathWeight E (fun i s t z => f i s t z * g i s t z) path =
      CylinderTransfer.labelledPathWeight E f path *
        CylinderTransfer.labelledPathWeight E g path := by
  induction n generalizing s with
  | zero => simp [CylinderTransfer.labelledPathWeight]
  | succ n ih =>
      obtain ⟨u, z, path⟩ := path
      simp only [CylinderTransfer.labelledPathWeight]
      rw [ih]
      ac_rfl

private theorem acceptedWeight_mul {S : Type*} (E : S → S → Type*)
    (I F : S → Type*) {n : ℕ}
    (initial initial' : ∀ s, I s → R)
    (step step' : Fin n → ∀ s t, E s t → R)
    (terminal terminal' : ∀ s, F s → R) (x : CylinderTransfer.Accepted E I F n) :
    CylinderTransfer.acceptedWeight E I F
        (fun s z => initial s z * initial' s z)
        (fun i s t z => step i s t z * step' i s t z)
        (fun s z => terminal s z * terminal' s z) x =
      CylinderTransfer.acceptedWeight E I F initial step terminal x *
        CylinderTransfer.acceptedWeight E I F initial' step' terminal' x := by
  unfold CylinderTransfer.acceptedWeight
  rw [labelledPathWeight_mul]
  dsimp only
  ac_rfl

/-- Multiplying the masks carried by the same accepted object gives the
zero-one indicator of its actual physical exterior event. -/
theorem acceptedExteriorFilters_eq_indicator {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (σ : ColumnGeometry m (n + 2)) (a b : ℕ) (hbn : b ≤ n)
    (x : AcceptedObject hm p n) :
    CylinderTransfer.acceptedWeight (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p)
      (initialExteriorFilter hm σ) (localExteriorFilter hm σ a b)
      (terminalExteriorFilter hm σ) x =
        (exteriorIndicator hm σ a b (acceptedEdges x) : R) := by
  have hpath : CylinderTransfer.labelledPathWeight (LocalLabel hm)
      (localExteriorFilter hm σ a b) x.2.2.2.1 =
        ∏ i : Fin n, if (¬ freeLocalSlot a b i.val →
          localMaskAgreement σ i (acceptedCutStates x i.castSucc).val.horizontal
            (acceptedCutStates x i.castSucc).val.diagonal (acceptedLocalMasks x i))
          then (1 : R) else 0 := by
    calc
      _ = ∏ i : Fin n,
          let q := CylinderTransfer.LabelledPath.observe
            (fun s _ z => (s, z.val)) x.2.2.2.1 i
          if freeLocalSlot a b i.val then (1 : R) else
            if localMaskAgreement σ i q.1.val.horizontal q.1.val.diagonal q.2
            then 1 else 0 :=
        CylinderTransfer.labelledPathWeight_eq_prod_observe (LocalLabel hm)
          (fun s _ z => (s, z.val))
          (fun i q => if freeLocalSlot a b i.val then (1 : R) else
            if localMaskAgreement σ i q.1.val.horizontal q.1.val.diagonal q.2
            then 1 else 0) x.2.2.2.1
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [observed_source_value]
        dsimp only
        change (if freeLocalSlot a b i.val then (1 : R) else
          if localMaskAgreement σ i (acceptedCutStates x i.castSucc).val.horizontal
            (acceptedCutStates x i.castSucc).val.diagonal (acceptedLocalMasks x i)
          then 1 else 0) = _
        by_cases hi : freeLocalSlot a b i.val <;> simp [hi]
  unfold CylinderTransfer.acceptedWeight
  rw [hpath]
  unfold initialExteriorFilter terminalExteriorFilter exteriorIndicator
  rw [exteriorAgrees_acceptedEdges_iff σ a b hbn x]
  by_cases hfirst : x.2.1.val = σ.1 0
  · by_cases hterminal : terminalMaskAgreement σ x.2.2.1.val.horizontal
        x.2.2.1.val.diagonal x.2.2.2.2.val
    · simp only [hfirst, hterminal, if_true, one_mul, mul_one, true_and, and_true]
      exact product_indicators (R := R) (fun i : Fin n =>
        ¬ freeLocalSlot a b i.val →
          localMaskAgreement σ i (acceptedCutStates x i.castSucc).val.horizontal
            (acceptedCutStates x i.castSucc).val.diagonal (acceptedLocalMasks x i))
    · simp [hterminal]
  · simp [hfirst]

/-- The filtered accepted weight is the genuine unordered physical edge
product multiplied by the complete exterior-event indicator. -/
theorem exteriorAcceptedWeight_eq_physical {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (hbn : b ≤ n) (x : AcceptedObject hm p n) :
    exteriorAcceptedWeight w σ a b x =
      (∏ e ∈ acceptedEdges x, w e) * exteriorIndicator hm σ a b (acceptedEdges x) := by
  unfold exteriorAcceptedWeight exteriorInitialWeight exteriorLocalWeight exteriorTerminalWeight
  rw [acceptedWeight_mul, acceptedWeight_eq_factors,
    acceptedExteriorFilters_eq_indicator σ a b hbn x,
    ← acceptedEdges_product_eq_factors]

/-- The frozen counted bijection transports each actual physical product
and its exterior indicator, including impossible exterior prescriptions. -/
theorem exteriorParityCount_eq_sum_acceptedWeight {m n : ℕ}
    (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (hbn : b ≤ n) :
    exteriorParityCount hm p w σ a b =
      ∑ x : AcceptedObject hm p n, exteriorAcceptedWeight w σ a b x := by
  classical
  unfold exteriorParityCount
  refine Fintype.sum_equiv (countedTransferEquiv hm hn p) _ _ (fun s => ?_)
  change selectionProduct (graph m (n + 2) hm) w s.val *
      exteriorIndicator hm σ a b s.val.val =
    exteriorAcceptedWeight w σ a b (selectionAccepted hm hn p s)
  rw [exteriorAcceptedWeight_eq_physical w σ a b hbn,
    acceptedEdges_selectionAccepted hm hn p s]
  rfl

/-- Exact ordered-product formula for the original physical exterior count.
Only `b ≤ n` is needed for the endcap ownership; no weight bounds are assumed. -/
theorem exteriorParityCount_eq_orderedProduct {m n : ℕ}
    (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) (σ : ColumnGeometry m (n + 2))
    (a b : ℕ) (hbn : b ≤ n) :
    exteriorParityCount hm p w σ a b =
      exteriorInitialVector hm w σ ⬝ᵥ
        ((List.ofFn (fun i : Fin n => exteriorLocalMatrix hm w σ a b i)).prod *ᵥ
          exteriorTerminalVector hm p w σ) := by
  rw [exteriorParityCount_eq_sum_acceptedWeight hm hn p w σ a b hbn]
  exact CylinderTransfer.sum_acceptedWeight (LocalLabel hm) (InitialLabel hm)
    (TerminalLabel hm p) (exteriorInitialWeight hm w σ)
    (exteriorLocalWeight hm w σ a b) (exteriorTerminalWeight hm w σ)

#print axioms exteriorAgrees_realizedEdges_iff
#print axioms geometryExteriorAgrees_iff_ownedMasks
#print axioms exteriorAgrees_acceptedEdges_iff
#print axioms acceptedExteriorFilters_eq_indicator
#print axioms exteriorAcceptedWeight_eq_physical
#print axioms exteriorParityCount_eq_sum_acceptedWeight
#print axioms exteriorParityCount_eq_orderedProduct

end TriangularCylinder.Transfer
