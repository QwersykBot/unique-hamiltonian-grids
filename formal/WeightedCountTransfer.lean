import WeightedCylinderEncoding

/-!
# Ordered transfer formula for actual physical edge-product counts

Each vector or matrix entry sums the existing actual label types with
their physical edge factors. The frozen weighted counted-object bijection
and generic weighted path identity give the ordered matrix product.
The width is `n + 2` with `n ≥ 1`, exactly the range of the counted bijection.
No positivity, symmetry, or asymptotic assertion is made here.
-/

open scoped BigOperators Matrix

namespace TriangularCylinder.Transfer

variable {R : Type*} [CommSemiring R]

noncomputable local instance {m : ℕ} (hm : 3 ≤ m) : DecidableEq (CoreState hm) :=
  Classical.decEq _

/-- The initial vector sums the first-column vertical products over the
actual initial labels at each state. -/
noncomputable def initialPhysicalVector {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) : CoreState hm → R :=
  fun s => ∑ a : InitialLabel hm s, initialPhysicalWeight hm w s a

/-- Position `i` owns source-cut H/D and the following column's V.
Each matrix entry sums these factors over its actual local labels. -/
noncomputable def localPhysicalMatrix {m n : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Vertex m (n + 2)) → R) (i : Fin n) :
    Matrix (CoreState hm) (CoreState hm) R :=
  Matrix.of fun s t => ∑ a : LocalLabel hm s t, localPhysicalWeight hm w i s t a

/-- The terminal vector sums the last-cut H/D and final-column V factors
over the actual terminal labels of the specified parity. -/
noncomputable def terminalPhysicalVector {m n : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) : CoreState hm → R :=
  fun s => ∑ a : TerminalLabel hm p s, terminalPhysicalWeight hm w s a

/-- The actual weighted count is the initial vector, followed by the
position-ordered local matrices, followed by the terminal vector. -/
theorem weightedParityCount_eq_ordered_transfer {m n : ℕ}
    (hm : 3 ≤ m) (hn : 1 ≤ n) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) :
    weightedParityCount hm p w =
      initialPhysicalVector hm w ⬝ᵥ
        ((List.ofFn (localPhysicalMatrix hm w)).prod *ᵥ terminalPhysicalVector hm p w) := by
  rw [weightedParityCount_eq_sum_acceptedWeight hm hn p w]
  exact CylinderTransfer.sum_acceptedWeight
    (LocalLabel hm) (InitialLabel hm) (TerminalLabel hm p)
    (initialPhysicalWeight hm w) (localPhysicalWeight hm w) (terminalPhysicalWeight hm w)

end TriangularCylinder.Transfer
