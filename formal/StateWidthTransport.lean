import ActualTransfer
import SplicePrefixCoordinates

/-!
# Actual occurrence under width reassociation

The splice coordinate equivalence is the same coordinate-preserving width
transport used by the actual-state API. A public substitution lemma makes
occurrence available after this transport without using a private declaration.
No parity or counting statement is added.
-/

namespace TriangularCylinder.StateWidthTransport

open SimpleGraph BoundaryState SplicePrefixCoordinates

/-- The splice width reassociation is the actual-state width equivalence. -/
theorem fullWidthEquiv_eq_widthEquiv (m a j k : ℕ) :
    fullWidthEquiv m a j k = Transfer.widthEquiv (m := m)
      (by omega : (a + j) + 1 + k = a + (j + 1 + k)) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · rfl
  · apply Fin.ext
    rfl

/-- A state of an actual Hamiltonian cycle still occurs after an equal-width
transport into the column split expected by `stateAt`. -/
theorem occurs_stateAt_comap_widthEquiv {m j k L : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) (h : j + 1 + k = L)
    {v : Vertex m L} (C : (graph m L hm).Walk v v) (hC : C.IsHamiltonianCycle) :
    Occurs hm (stateAt hm hk ((fromEdgeSet C.edgeSet).comap (Transfer.widthEquiv h))) := by
  subst L
  simpa only [Transfer.widthEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id] using
    occurs_stateAt hm hk C hC

/-- The state at the shifted joined cut occurs whenever the joined cycle is
an actual Hamiltonian cycle. Empty old or inserted prefix interiors are allowed. -/
theorem occurs_joined_state {m a j k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k)
    {v : Vertex m (a + (j + 1 + k))}
    (J : (graph m (a + (j + 1 + k)) hm).Walk v v) (hJ : J.IsHamiltonianCycle) :
    Occurs hm (stateAt (j := a + j) hm hk
      ((fromEdgeSet J.edgeSet).comap (fullWidthEquiv m a j k))) := by
  rw [fullWidthEquiv_eq_widthEquiv m a j k]
  exact occurs_stateAt_comap_widthEquiv (j := a + j) hm hk (by omega) J hJ

#print axioms fullWidthEquiv_eq_widthEquiv
#print axioms occurs_stateAt_comap_widthEquiv
#print axioms occurs_joined_state

end TriangularCylinder.StateWidthTransport
