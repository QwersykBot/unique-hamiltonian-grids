import RowRotation
import Mathlib.Data.Set.Card

/-!
# Selected vertical edges at the ends of a triangular cylinder

The ambient graph is the frozen consistently oriented triangular cylinder.
The selected graph is spanning, connected, and has exactly two neighbors at
every vertex. No Hamiltonian-cycle presentation or classification theorem is
assumed. The first or last two columns saturate if their end column has no
selected vertical edge. All forcing statements already hold for two columns.
The two ends are handled directly; no column-reversal symmetry is assumed.
-/

namespace TriangularCylinder.BoundaryVertical

open SimpleGraph

variable {m L : ℕ}

def secondCol (L : ℕ) (hL : 2 ≤ L) : Fin L := ⟨1, by omega⟩

def penultimateCol (L : ℕ) (hL : 2 ≤ L) : Fin L := ⟨L - 2, by omega⟩

/-- No selected vertical in the given column, in either undirected orientation. -/
def NoVerticalAt (H : SimpleGraph (Vertex m L)) (c : Fin L) : Prop :=
  ∀ r s : Fin m, NextRow r s → ¬ H.Adj (r, c) (s, c)

section Rows

variable [NeZero m]

theorem nextRow_succ (hm : 3 ≤ m) (r : Fin m) : NextRow r (r + 1) :=
  (nextRow_iff_add_one hm r (r + 1)).mpr rfl

theorem nextRow_pred (hm : 3 ≤ m) (r : Fin m) : NextRow (r - 1) r := by
  apply (nextRow_iff_add_one hm (r - 1) r).mpr
  simp

/-- Without a first-column vertical, there are only two possible selected neighbors. -/
theorem first_neighbors_subset_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hno : NoVerticalAt H (firstCol L hL)) (r : Fin m) :
    H.neighborSet (r, firstCol L hL) ⊆
      {(r, secondCol L hL), (r + 1, secondCol L hL)} := by
  intro w hw
  rcases w with ⟨s, c⟩
  change H.Adj (r, firstCol L hL) (s, c) at hw
  have hamb := hsub hw
  change Forward (r, firstCol L hL) (s, c) ∨
    Forward (s, c) (r, firstCol L hL) at hamb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hamb with hf | hf
  · rcases hf with ⟨hc, hr⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
    · change firstCol L hL = c at hc
      subst c
      exact (hno r s hr hw).elim
    · change r = s at hr
      subst s
      left
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change (firstCol L hL).val + 1 = c.val at hc
        simp only [firstCol] at hc
        change c.val = 1
        omega
    · change NextRow r s at hr
      have hs := (nextRow_iff_add_one hm r s).mp hr
      subst s
      right
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change (firstCol L hL).val + 1 = c.val at hc
        simp only [firstCol] at hc
        change c.val = 1
        omega
  · rcases hf with ⟨hc, hr⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · change c = firstCol L hL at hc
      subst c
      exact (hno s r hr hw.symm).elim
    · change c.val + 1 = (firstCol L hL).val at hc
      simp only [firstCol] at hc
      omega
    · change c.val + 1 = (firstCol L hL).val at hc
      simp only [firstCol] at hc
      omega

/-- Degree two forces both allowable first-column crossing edges to be selected. -/
theorem first_neighbors_eq_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (firstCol L hL)) (r : Fin m) :
    H.neighborSet (r, firstCol L hL) =
      {(r, secondCol L hL), (r + 1, secondCol L hL)} := by
  have hpair : (r, secondCol L hL) ≠ (r + 1, secondCol L hL) := by
    intro h
    exact nextRow_ne hm (nextRow_succ hm r) (congrArg Prod.fst h)
  apply Set.eq_of_subset_of_ncard_le
    (first_neighbors_subset_of_no_vertical hm hL H hsub hno r)
  rw [Set.ncard_pair hpair, hdeg]

/-- The two forced crossings already exhaust every second-column neighbor set. -/
theorem second_neighbors_eq_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (firstCol L hL)) (r : Fin m) :
    H.neighborSet (r, secondCol L hL) =
      {(r, firstCol L hL), (r - 1, firstCol L hL)} := by
  have hhor : H.Adj (r, firstCol L hL) (r, secondCol L hL) := by
    change (r, secondCol L hL) ∈ H.neighborSet (r, firstCol L hL)
    rw [first_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r]
    simp
  have hdiag : H.Adj (r - 1, firstCol L hL) (r, secondCol L hL) := by
    change (r, secondCol L hL) ∈ H.neighborSet (r - 1, firstCol L hL)
    rw [first_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno (r - 1)]
    simp
  have hpair : (r, firstCol L hL) ≠ (r - 1, firstCol L hL) := by
    intro h
    exact (nextRow_ne hm (nextRow_pred hm r)) (congrArg Prod.fst h).symm
  have hsubset : {(r, firstCol L hL), (r - 1, firstCol L hL)} ⊆
      H.neighborSet (r, secondCol L hL) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hhor.symm
    · exact hdiag.symm
  symm
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [Set.ncard_pair hpair, hdeg]

/-- The first interface selects every horizontal and every forward diagonal. -/
theorem first_crossings_selected_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (firstCol L hL)) (r : Fin m) :
    H.Adj (r, firstCol L hL) (r, secondCol L hL) ∧
      H.Adj (r, firstCol L hL) (r + 1, secondCol L hL) := by
  constructor
  · change (r, secondCol L hL) ∈ H.neighborSet (r, firstCol L hL)
    rw [first_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r]
    simp
  · change (r + 1, secondCol L hL) ∈ H.neighborSet (r, firstCol L hL)
    rw [first_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r]
    simp

/-- No selected edge can leave the first two columns once the first end has no vertical. -/
theorem first_two_closed_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (firstCol L hL))
    {u v : Vertex m L} (hu : u.2.val < 2) (huv : H.Adj u v) : v.2.val < 2 := by
  rcases u with ⟨r, c⟩
  change c.val < 2 at hu
  have hc : c = firstCol L hL ∨ c = secondCol L hL := by
    have hv : c.val = 0 ∨ c.val = 1 := by omega
    rcases hv with hv | hv
    · left
      exact Fin.ext hv
    · right
      exact Fin.ext hv
  rcases hc with rfl | rfl
  · change v ∈ H.neighborSet (r, firstCol L hL) at huv
    rw [first_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r] at huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    rcases huv with rfl | rfl <;> simp [secondCol]
  · change v ∈ H.neighborSet (r, secondCol L hL) at huv
    rw [second_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r] at huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    rcases huv with rfl | rfl <;> simp [firstCol]

/-- The right end has only its horizontal and backward-row diagonal possibilities. -/
theorem last_neighbors_subset_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hno : NoVerticalAt H (lastCol L hL)) (r : Fin m) :
    H.neighborSet (r, lastCol L hL) ⊆
      {(r, penultimateCol L hL), (r - 1, penultimateCol L hL)} := by
  intro w hw
  rcases w with ⟨s, c⟩
  change H.Adj (r, lastCol L hL) (s, c) at hw
  have hamb := hsub hw
  change Forward (r, lastCol L hL) (s, c) ∨
    Forward (s, c) (r, lastCol L hL) at hamb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hamb with hf | hf
  · rcases hf with ⟨hc, hr⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · change lastCol L hL = c at hc
      subst c
      exact (hno r s hr hw).elim
    · change (lastCol L hL).val + 1 = c.val at hc
      simp only [lastCol] at hc
      have hlt := c.isLt
      omega
    · change (lastCol L hL).val + 1 = c.val at hc
      simp only [lastCol] at hc
      have hlt := c.isLt
      omega
  · rcases hf with ⟨hc, hr⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
    · change c = lastCol L hL at hc
      subst c
      exact (hno s r hr hw.symm).elim
    · change s = r at hr
      subst s
      left
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change c.val + 1 = (lastCol L hL).val at hc
        simp only [lastCol] at hc
        change c.val = L - 2
        omega
    · change NextRow s r at hr
      have hrow := (nextRow_iff_add_one hm s r).mp hr
      have hs : s = r - 1 := by
        rw [hrow]
        simp
      subst s
      right
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change c.val + 1 = (lastCol L hL).val at hc
        simp only [lastCol] at hc
        change c.val = L - 2
        omega

/-- Both allowed right-end crossings are forced by the selected degree. -/
theorem last_neighbors_eq_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (lastCol L hL)) (r : Fin m) :
    H.neighborSet (r, lastCol L hL) =
      {(r, penultimateCol L hL), (r - 1, penultimateCol L hL)} := by
  have hpair : (r, penultimateCol L hL) ≠ (r - 1, penultimateCol L hL) := by
    intro h
    exact (nextRow_ne hm (nextRow_pred hm r)) (congrArg Prod.fst h).symm
  apply Set.eq_of_subset_of_ncard_le
    (last_neighbors_subset_of_no_vertical hm hL H hsub hno r)
  rw [Set.ncard_pair hpair, hdeg]

/-- Forced right-end crossings exhaust every penultimate-column neighbor set. -/
theorem penultimate_neighbors_eq_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (lastCol L hL)) (r : Fin m) :
    H.neighborSet (r, penultimateCol L hL) =
      {(r, lastCol L hL), (r + 1, lastCol L hL)} := by
  have hhor : H.Adj (r, lastCol L hL) (r, penultimateCol L hL) := by
    change (r, penultimateCol L hL) ∈ H.neighborSet (r, lastCol L hL)
    rw [last_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r]
    simp
  have hdiag : H.Adj (r + 1, lastCol L hL) (r, penultimateCol L hL) := by
    change (r, penultimateCol L hL) ∈ H.neighborSet (r + 1, lastCol L hL)
    rw [last_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno (r + 1)]
    simp
  have hpair : (r, lastCol L hL) ≠ (r + 1, lastCol L hL) := by
    intro h
    exact nextRow_ne hm (nextRow_succ hm r) (congrArg Prod.fst h)
  have hsubset : {(r, lastCol L hL), (r + 1, lastCol L hL)} ⊆
      H.neighborSet (r, penultimateCol L hL) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hhor.symm
    · exact hdiag.symm
  symm
  apply Set.eq_of_subset_of_ncard_le hsubset
  rw [Set.ncard_pair hpair, hdeg]

/-- The last interface selects every horizontal and every forward diagonal. -/
theorem last_crossings_selected_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (lastCol L hL)) (r : Fin m) :
    H.Adj (r, penultimateCol L hL) (r, lastCol L hL) ∧
      H.Adj (r, penultimateCol L hL) (r + 1, lastCol L hL) := by
  constructor
  · change (r, lastCol L hL) ∈ H.neighborSet (r, penultimateCol L hL)
    rw [penultimate_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r]
    simp
  · change (r + 1, lastCol L hL) ∈ H.neighborSet (r, penultimateCol L hL)
    rw [penultimate_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r]
    simp

/-- The last two columns form an adjacency-closed set when the last end has no vertical. -/
theorem last_two_closed_of_no_vertical (hm : 3 ≤ m) (hL : 2 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 2)
    (hno : NoVerticalAt H (lastCol L hL))
    {u v : Vertex m L} (hu : L - 2 ≤ u.2.val) (huv : H.Adj u v) : L - 2 ≤ v.2.val := by
  rcases u with ⟨r, c⟩
  change L - 2 ≤ c.val at hu
  have hc : c = penultimateCol L hL ∨ c = lastCol L hL := by
    have hlt := c.isLt
    have hv : c.val = L - 2 ∨ c.val = L - 1 := by omega
    rcases hv with hv | hv
    · left
      exact Fin.ext hv
    · right
      exact Fin.ext hv
  rcases hc with rfl | rfl
  · change v ∈ H.neighborSet (r, penultimateCol L hL) at huv
    rw [penultimate_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r] at huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    rcases huv with rfl | rfl <;> change L - 2 ≤ L - 1 <;> omega
  · change v ∈ H.neighborSet (r, lastCol L hL) at huv
    rw [last_neighbors_eq_of_no_vertical hm hL H hsub hdeg hno r] at huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    rcases huv with rfl | rfl <;> simp [penultimateCol]

end Rows

private theorem reachable_preserves_closed {V : Type*} {H : SimpleGraph V} {S : Set V}
    (hclosed : ∀ {u v}, u ∈ S → H.Adj u v → v ∈ S)
    {u v : V} (h : H.Reachable u v) (hu : u ∈ S) : v ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hstep ih => exact hclosed ih hstep

/-- Three or more columns force a selected vertical at the first end. -/
theorem exists_first_selected_vertical (hm : 3 ≤ m) (hL : 3 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hconn : H.Connected) (hdeg : ∀ v, (H.neighborSet v).ncard = 2) :
    ∃ r s : Fin m, NextRow r s ∧
      H.Adj (r, firstCol L (by omega)) (s, firstCol L (by omega)) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have h2 : 2 ≤ L := by omega
  by_contra h
  have hno : NoVerticalAt H (firstCol L h2) := by
    intro r s hrs hadj
    exact h ⟨r, s, hrs, hadj⟩
  let r : Fin m := ⟨0, by omega⟩
  let u : Vertex m L := (r, firstCol L h2)
  let v : Vertex m L := (r, ⟨2, by omega⟩)
  have hv : v.2.val < 2 := reachable_preserves_closed
    (S := {z : Vertex m L | z.2.val < 2})
    (fun hz hadj => first_two_closed_of_no_vertical hm h2 H hsub hdeg hno hz hadj)
    (hconn.preconnected u v) (by simp [u, firstCol])
  change 2 < 2 at hv
  omega

/-- Three or more columns also force a selected vertical at the last end. -/
theorem exists_last_selected_vertical (hm : 3 ≤ m) (hL : 3 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hconn : H.Connected) (hdeg : ∀ v, (H.neighborSet v).ncard = 2) :
    ∃ r s : Fin m, NextRow r s ∧
      H.Adj (r, lastCol L (by omega)) (s, lastCol L (by omega)) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have h2 : 2 ≤ L := by omega
  by_contra h
  have hno : NoVerticalAt H (lastCol L h2) := by
    intro r s hrs hadj
    exact h ⟨r, s, hrs, hadj⟩
  let r : Fin m := ⟨0, by omega⟩
  let u : Vertex m L := (r, lastCol L h2)
  let v : Vertex m L := (r, firstCol L h2)
  have hv : L - 2 ≤ v.2.val := reachable_preserves_closed
    (S := {z : Vertex m L | L - 2 ≤ z.2.val})
    (fun hz hadj => last_two_closed_of_no_vertical hm h2 H hsub hdeg hno hz hadj)
    (hconn.preconnected u v) (by change L - 2 ≤ L - 1; omega)
  change L - 2 ≤ 0 at hv
  omega

/-- Both ends have selected verticals; their selected gaps need not agree. -/
theorem exists_selected_verticals_at_both_ends (hm : 3 ≤ m) (hL : 3 ≤ L)
    (H : SimpleGraph (Vertex m L)) (hsub : H ≤ graph m L hm)
    (hconn : H.Connected) (hdeg : ∀ v, (H.neighborSet v).ncard = 2) :
    (∃ r s : Fin m, NextRow r s ∧
      H.Adj (r, firstCol L (by omega)) (s, firstCol L (by omega))) ∧
    (∃ r s : Fin m, NextRow r s ∧
      H.Adj (r, lastCol L (by omega)) (s, lastCol L (by omega))) :=
  ⟨exists_first_selected_vertical hm hL H hsub hconn hdeg,
    exists_last_selected_vertical hm hL H hsub hconn hdeg⟩

#print axioms first_neighbors_eq_of_no_vertical
#print axioms second_neighbors_eq_of_no_vertical
#print axioms first_crossings_selected_of_no_vertical
#print axioms last_neighbors_eq_of_no_vertical
#print axioms penultimate_neighbors_eq_of_no_vertical
#print axioms last_crossings_selected_of_no_vertical
#print axioms exists_first_selected_vertical
#print axioms exists_last_selected_vertical
#print axioms exists_selected_verticals_at_both_ends

end TriangularCylinder.BoundaryVertical
