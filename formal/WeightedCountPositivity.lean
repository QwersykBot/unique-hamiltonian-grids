import WeightedCylinderEncoding
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Positivity of the actual physical weighted counts

Every selected Hamiltonian edge belongs to the ambient graph. Strict
positivity of weights on those graph edges therefore makes each selected
edge product positive. Summing over the existing parity subtype is positive
exactly when that subtype has an element, equivalently when its existing
unweighted count is positive. All cylinder widths are allowed; weights on
nonedges are unrestricted and no uniform numerical lower bound is used.
-/

open scoped BigOperators

namespace CountedHamiltonian

/-- Positivity is needed only on actual ambient edges, since every selected
edge of a Hamiltonian realization belongs to that ambient graph. -/
theorem selectionProduct_pos {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 < w e) (s : Selection G) :
    0 < selectionProduct G w s := by
  exact Finset.prod_pos (fun e he => hw e (selection_edge_mem G s he))

end CountedHamiltonian

namespace TriangularCylinder.Transfer

open CountedHamiltonian

/-- At every width, strictly positive physical weights preserve exactly
the positivity of the existing unordered Hamiltonian parity count. -/
theorem weightedParityCount_pos_iff {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m L) → ℝ)
    (hw : ∀ e ∈ (graph m L hm).edgeSet, 0 < w e) :
    0 < weightedParityCount hm p w ↔ 0 < parityCount m L hm p := by
  classical
  rw [parityCount_eq_card_paritySelection, Fintype.card_pos_iff]
  constructor
  · intro h
    by_contra hempty
    letI : IsEmpty (ParitySelection hm p L) := not_nonempty_iff.mp hempty
    simp only [weightedParityCount, Finset.univ_eq_empty, Finset.sum_empty,
      lt_self_iff_false] at h
  · rintro ⟨s⟩
    exact Finset.sum_pos
      (fun t _ => selectionProduct_pos (graph m L hm) w hw t.val)
      ⟨s, Finset.mem_univ s⟩

end TriangularCylinder.Transfer
