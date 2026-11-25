import CylinderSplice
import Mathlib.Data.ZMod.Basic

/-!
# Mod-two edge coboundaries along graph walks

If two edge weights differ by the sum of vertex potentials at the endpoints
of every actual graph edge, their walk weights differ by the two endpoint
potentials. Interior potentials cancel in pairs. Thus the weights agree on
every closed walk, without a simplicity or Hamiltonicity hypothesis.

This is finite combinatorial bookkeeping and makes no topological claim.
-/

namespace EdgeCoboundary

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The endpoint formula for edge weights differing by a vertex coboundary.
The hypothesis is required only on actual edges of `G`. -/
theorem edgeWeight_change (w w' : Sym2 V → ZMod 2) (d : V → ZMod 2)
    (h : ∀ {x y : V}, G.Adj x y → w' s(x, y) = w s(x, y) + d x + d y)
    {x y : V} (p : G.Walk x y) :
    CylinderSplice.edgeWeight w' p = CylinderSplice.edgeWeight w p + d x + d y := by
  induction p with
  | nil => simp [CylinderSplice.edgeWeight, ZModModule.add_self]
  | @cons x y z hxy p ih =>
    change w' s(x, y) + CylinderSplice.edgeWeight w' p =
      (w s(x, y) + CylinderSplice.edgeWeight w p) + d x + d z
    rw [h hxy, ih]
    calc
      (w s(x, y) + d x + d y) + (CylinderSplice.edgeWeight w p + d y + d z) =
          ((w s(x, y) + CylinderSplice.edgeWeight w p) + d x + d z) + (d y + d y) := by
        ac_rfl
      _ = (w s(x, y) + CylinderSplice.edgeWeight w p) + d x + d z := by
        rw [ZModModule.add_self, add_zero]

/-- A vertex coboundary has zero contribution around every closed graph walk. -/
theorem edgeWeight_eq_of_closed (w w' : Sym2 V → ZMod 2) (d : V → ZMod 2)
    (h : ∀ {x y : V}, G.Adj x y → w' s(x, y) = w s(x, y) + d x + d y)
    {x : V} (p : G.Walk x x) :
    CylinderSplice.edgeWeight w' p = CylinderSplice.edgeWeight w p := by
  simpa only [add_assoc, ZModModule.add_self, add_zero] using edgeWeight_change w w' d h p

#print axioms edgeWeight_change
#print axioms edgeWeight_eq_of_closed

end EdgeCoboundary
