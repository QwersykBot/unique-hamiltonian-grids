import CountedTransferEquivalence
import ColumnWeights
import WeightedFiniteTransfer
import Mathlib.Algebra.BigOperators.Fin

/-!
# Physical edge products and exact accepted-object weights

Weights are assigned to the actual unordered physical edges of the fixed
cylinder. Each counted object is the existing undirected Hamiltonian edge
selection; roots, directions, and realization witnesses contribute no factors.

At width `n + 2`, the initial factor owns `V₀`, local step `i` owns the
source state's `Hᵢ,Dᵢ` and the new mask `Vᵢ₊₁`, and the terminal factor owns
`Hₙ,Dₙ,Vₙ₊₁`. Products need only a commutative monoid. Transporting finite
weighted sums uses a commutative semiring and the frozen counted bijection.
No positivity, transfer contraction, or asymptotic claim is made here.
-/

open scoped BigOperators

namespace CountedHamiltonian

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The physical edge product of the existing unordered counted selection. -/
def selectionProduct {R : Type*} [CommMonoid R]
    (w : Sym2 V → R) (s : Selection G) : R :=
  ∏ e ∈ s.val, w e

/-- A Hamiltonian presentation uses every selected edge exactly once. -/
theorem selectionProduct_ofCycle {R : Type*} [CommMonoid R]
    (w : Sym2 V → R) {v : V} (C : G.Walk v v) (hC : C.IsHamiltonianCycle) :
    selectionProduct G w (ofCycle G C hC) = (C.edges.map w).prod := by
  exact List.prod_toFinset w hC.isCycle.isTrail.edges_nodup

end CountedHamiltonian

namespace TriangularEdgeEncoding

open TriangularCylinder

variable {m L : ℕ} {R : Type*} [CommMonoid R]

/-- The frozen physical-edge uniqueness theorem also gives exact products. -/
theorem prod_realizedEdges_eq_selectedIds (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (w : Sym2 (Vertex m L) → R) :
    (∏ e ∈ realizedEdges hm g, w e) =
      ∏ id ∈ idsOfGeometry g, w (toEdge hm id) := by
  exact congrArg Additive.toMul
    (sum_realizedEdges_eq_selectedIds hm g (fun e => Additive.ofMul (w e)))

/-- A multiplicative instance of the frozen once-only V/H/D charging formula. -/
theorem prod_realizedEdges_eq_column_cut (hm : 3 ≤ m)
    (g : ColumnGeometry m L) (w : Sym2 (Vertex m L) → R) :
    (∏ e ∈ realizedEdges hm g, w e) =
      (∏ c : Fin L, ∏ r : Fin m,
        if g.1 c r then w (toEdge hm (.inl (r, c))) else 1) *
      (∏ c : Fin (L - 1), ∏ r : Fin m,
        ((if g.2.1 c r then w (toEdge hm (.inr (.inl (r, c)))) else 1) *
         (if g.2.2 c r then w (toEdge hm (.inr (.inr (r, c)))) else 1))) := by
  exact congrArg Additive.toMul
    (sum_realizedEdges_eq_column_cut hm g (fun e => Additive.ofMul (w e)))

end TriangularEdgeEncoding

namespace TriangularCylinder.Transfer

open CountedHamiltonian TriangularEdgeEncoding

variable {R : Type*}

noncomputable local instance {m : ℕ} (hm : 3 ≤ m) : DecidableEq (CoreState hm) :=
  Classical.decEq _

private theorem observed_source_value {S W : Type*} {E : S → S → Type*}
    (value : ∀ s t, E s t → W) {n : ℕ} {s t : S}
    (path : CylinderTransfer.LabelledPath E n s t) (i : Fin n) :
    CylinderTransfer.LabelledPath.observe (fun s t a => (s, value s t a)) path i =
      (Fin.cases s (CylinderTransfer.LabelledPath.observe (fun _ t _ => t) path)
        i.castSucc, CylinderTransfer.LabelledPath.observe value path i) := by
  induction n generalizing s with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨u, a, path⟩ := path
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact ih path i

section Products

variable [CommMonoid R]

/-- Product of the selected vertical physical edges in column `c`. -/
def verticalFactor {m L : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m L) → R) (c : Fin L) (a : RowMask m) : R :=
  ∏ r : Fin m, if a r then w (toEdge hm (.inl (r, c))) else 1

/-- Product of the selected horizontal and diagonal physical edges at one cut. -/
def cutFactor {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (c : Fin (n + 1))
    (h d : RowMask m) : R :=
  ∏ r : Fin m,
    (if h r then w (toEdge hm (.inr (.inl (r, cutEdgeIndex c)))) else 1) *
    (if d r then w (toEdge hm (.inr (.inr (r, cutEdgeIndex c)))) else 1)

/-- The initial label owns only the first column's vertical edges. -/
def initialPhysicalWeight {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R)
    (s : CoreState hm) (a : InitialLabel hm s) : R :=
  verticalFactor hm w 0 a.val

/-- Local step `i` owns its source H/D edges and its new-column V mask. -/
def localPhysicalWeight {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (i : Fin n)
    (s t : CoreState hm) (a : LocalLabel hm s t) : R :=
  cutFactor hm w i.castSucc s.val.horizontal s.val.diagonal *
    verticalFactor hm w i.succ.castSucc a.val

/-- The terminal label owns the last cut's H/D and the final column's V. -/
def terminalPhysicalWeight {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) {p : ZMod 2}
    (s : CoreState hm) (a : TerminalLabel hm p s) : R :=
  cutFactor hm w (Fin.last n) s.val.horizontal s.val.diagonal *
    verticalFactor hm w (Fin.last (n + 1)) a.val

/-- The same local factor read directly from the exact accepted observations. -/
def acceptedLocalFactor {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (x : AcceptedObject hm p n) (i : Fin n) : R :=
  cutFactor hm w i.castSucc (acceptedCutStates x i.castSucc).val.horizontal
      (acceptedCutStates x i.castSucc).val.diagonal *
    verticalFactor hm w i.succ.castSucc (acceptedLocalMasks x i)

/-- Initial, ordered local, and terminal physical factors of an accepted object. -/
def acceptedFactorWeight {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (x : AcceptedObject hm p n) : R :=
  initialPhysicalWeight hm w x.1 x.2.1 *
    (∏ i : Fin n, acceptedLocalFactor w x i) *
    terminalPhysicalWeight hm w x.2.2.1 x.2.2.2.2

/-- The local physical factor reads the actual source state and label value
of that step in the original dependent path. -/
theorem acceptedLocalFactor_eq_observed {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (x : AcceptedObject hm p n) (i : Fin n) :
    acceptedLocalFactor w x i =
      let q := CylinderTransfer.LabelledPath.observe
        (fun s _ a => (s, a.val)) x.2.2.2.1 i
      cutFactor hm w i.castSucc q.1.val.horizontal q.1.val.diagonal *
        verticalFactor hm w i.succ.castSucc q.2 := by
  rw [observed_source_value]
  rfl

private theorem prod_columns_cuts {n : ℕ}
    (v : Fin (n + 2) → R) (c : Fin (n + 1) → R) :
    (∏ i, v i) * (∏ i, c i) =
      v 0 * (∏ i : Fin n, c i.castSucc * v i.succ.castSucc) *
        (c (Fin.last n) * v (Fin.last (n + 1))) := by
  rw [Fin.prod_univ_succ v,
    Fin.prod_univ_castSucc (fun i : Fin (n + 1) => v i.succ),
    Fin.prod_univ_castSucc c, Finset.prod_mul_distrib]
  change (v 0 * ((∏ i : Fin n, v i.succ.castSucc) * v (Fin.last (n + 1)))) *
      ((∏ i : Fin n, c i.castSucc) * c (Fin.last n)) = _
  ac_rfl

/-- The product on reconstructed physical edges factors with no duplicate or
omitted edge. This holds for arbitrary accepted data, including length zero. -/
theorem acceptedEdges_product_eq_factors {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (x : AcceptedObject hm p n) :
    (∏ e ∈ acceptedEdges x, w e) = acceptedFactorWeight w x := by
  rw [acceptedEdges, prod_realizedEdges_eq_column_cut]
  change (∏ c : Fin (n + 2), verticalFactor hm w c (acceptedVerticalMasks x c)) *
      (∏ c : Fin (n + 1), cutFactor hm w c (acceptedCutStates x c).val.horizontal
        (acceptedCutStates x c).val.diagonal) = _
  rw [prod_columns_cuts]
  simp only [← Fin.succ_castSucc, ← Fin.succ_last,
    acceptedVerticalMasks, Fin.cases_zero, Fin.cases_succ,
    Fin.lastCases_castSucc, Fin.lastCases_last, acceptedCutStates_last,
    acceptedFactorWeight, initialPhysicalWeight, terminalPhysicalWeight,
    acceptedLocalFactor, acceptedInitialMask, acceptedTerminalMask]

/-- The frozen counted reconstruction preserves the actual physical product. -/
theorem acceptedSelection_product_eq_factors {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (x : AcceptedObject hm p n) :
    selectionProduct (graph m (n + 2) hm) w (acceptedSelection x).val =
      acceptedFactorWeight w x :=
  acceptedEdges_product_eq_factors w x

/-- The canonical encoding of any counted selection preserves its edge product. -/
theorem selectionProduct_eq_encoded_factors {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (w : Sym2 (Vertex m (n + 2)) → R)
    (s : ParitySelection hm p (n + 2)) :
    selectionProduct (graph m (n + 2) hm) w s.val =
      acceptedFactorWeight w (selectionAccepted hm hn p s) := by
  rw [← acceptedEdges_product_eq_factors, acceptedEdges_selectionAccepted]
  rfl

end Products

section Sums

variable [CommSemiring R]

/-- The actual dependent accepted-object weight is precisely the observed
physical-factor product. The step observer includes its source state. -/
theorem acceptedWeight_eq_factors {m n : ℕ} {hm : 3 ≤ m} {p : ZMod 2}
    (w : Sym2 (Vertex m (n + 2)) → R) (x : AcceptedObject hm p n) :
    CylinderTransfer.acceptedWeight (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p)
      (initialPhysicalWeight hm w) (localPhysicalWeight hm w)
      (terminalPhysicalWeight hm w) x = acceptedFactorWeight w x := by
  have hpath : CylinderTransfer.labelledPathWeight (LocalLabel hm)
      (localPhysicalWeight hm w) x.2.2.2.1 =
        ∏ i : Fin n, acceptedLocalFactor w x i := by
    calc
      _ = ∏ i : Fin n,
          let q := CylinderTransfer.LabelledPath.observe
            (fun s _ a => (s, a.val)) x.2.2.2.1 i
          cutFactor hm w i.castSucc q.1.val.horizontal q.1.val.diagonal *
            verticalFactor hm w i.succ.castSucc q.2 :=
        CylinderTransfer.labelledPathWeight_eq_prod_observe (LocalLabel hm)
          (fun s _ a => (s, a.val))
          (fun i q => cutFactor hm w i.castSucc q.1.val.horizontal q.1.val.diagonal *
            verticalFactor hm w i.succ.castSucc q.2) x.2.2.2.1
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        exact (acceptedLocalFactor_eq_observed w x i).symm
  unfold CylinderTransfer.acceptedWeight acceptedFactorWeight
  rw [hpath]

/-- Sum of genuine physical edge products over the existing unordered
Hamiltonian selections in the specified existing meridian-parity subtype. -/
noncomputable def weightedParityCount {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m L) → R) : R :=
  ∑ s : ParitySelection hm p L, selectionProduct (graph m L hm) w s.val

/-- Exact finite weighted-sum transport along the proved counted bijection.
This uses the physical product identity, not a cardinality inference. -/
theorem weightedParityCount_eq_sum_factors {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (p : ZMod 2) (w : Sym2 (Vertex m (n + 2)) → R) :
    weightedParityCount hm p w =
      ∑ x : AcceptedObject hm p n, acceptedFactorWeight w x := by
  classical
  unfold weightedParityCount
  exact Fintype.sum_equiv (countedTransferEquiv hm hn p) _ _
    (fun s => selectionProduct_eq_encoded_factors hm hn p w s)

/-- The physical weighted count equals the sum of weights on the original
accepted objects, with their actual initial/local/terminal labels. -/
theorem weightedParityCount_eq_sum_acceptedWeight {m n : ℕ}
    (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) :
    weightedParityCount hm p w =
      ∑ x : AcceptedObject hm p n,
        CylinderTransfer.acceptedWeight (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p)
          (initialPhysicalWeight hm w) (localPhysicalWeight hm w)
          (terminalPhysicalWeight hm w) x := by
  rw [weightedParityCount_eq_sum_factors hm hn p w]
  apply Finset.sum_congr rfl
  intro x _
  exact (acceptedWeight_eq_factors w x).symm

/-- Unit physical weights specialize to the existing undirected parity count. -/
theorem weightedParityCount_one {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2) :
    weightedParityCount (R := R) (L := L) hm p (fun _ => 1) =
      (parityCount m L hm p : R) := by
  classical
  simp only [weightedParityCount, selectionProduct, Finset.prod_const_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [parityCount_eq_card_paritySelection]

end Sums

end TriangularCylinder.Transfer
