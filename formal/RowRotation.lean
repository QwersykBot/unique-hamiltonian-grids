import AuxiliaryCycle
import EdgeCoboundary
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Row rotations and two-boundary alignment

Row shifts are actual automorphisms of the consistently triangulated graph.
Their mod-two parity invariance is proved first for one step by an edge
coboundary, then for every finite shift by iteration.
-/

namespace TriangularCylinder

open SimpleGraph

section Shifts

variable {m L : ℕ} [NeZero m]

theorem nextRow_iff_add_one (hm : 3 ≤ m) (r s : Fin m) :
    NextRow r s ↔ s = r + 1 := by
  have h1 : (1 : Fin m).val = 1 := by
    change 1 % m = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [NextRow, Fin.ext_iff, Fin.val_add, h1]

theorem nextRow_add_iff (hm : 3 ≤ m) (r s k : Fin m) :
    NextRow (r + k) (s + k) ↔ NextRow r s := by
  rw [nextRow_iff_add_one hm, nextRow_iff_add_one hm]
  rw [show r + k + 1 = (r + 1) + k by ac_rfl]
  exact add_right_cancel_iff

theorem nextRow_sub_iff (hm : 3 ≤ m) (r s k : Fin m) :
    NextRow (r - k) (s - k) ↔ NextRow r s := by
  simpa only [sub_eq_add_neg] using nextRow_add_iff hm r s (-k)

def shiftVertex (k : Fin m) (x : Vertex m L) : Vertex m L := (x.1 + k, x.2)

theorem shiftVertex_bijective (k : Fin m) :
    Function.Bijective (shiftVertex (L := L) k) := by
  constructor
  · intro x y h
    apply Prod.ext
    · exact add_right_cancel (congrArg (fun z : Vertex m L => z.1) h)
    · have hc := congrArg (fun z : Vertex m L => z.2) h
      exact hc
  · intro x
    refine ⟨(x.1 - k, x.2), ?_⟩
    simp [shiftVertex]

theorem forward_shift_iff (hm : 3 ≤ m) (k : Fin m) (x y : Vertex m L) :
    Forward (shiftVertex k x) (shiftVertex k y) ↔ Forward x y := by
  simp only [Forward, shiftVertex, nextRow_add_iff hm, add_right_cancel_iff]

def shiftHom (hm : 3 ≤ m) (k : Fin m) : graph m L hm →g graph m L hm where
  toFun := shiftVertex k
  map_rel' := by
    intro x y h
    change Forward (shiftVertex k x) (shiftVertex k y) ∨
      Forward (shiftVertex k y) (shiftVertex k x)
    simpa only [forward_shift_iff hm] using h

theorem shiftHom_zero (hm : 3 ≤ m) : shiftHom (L := L) hm 0 = Hom.id := by
  apply DFunLike.ext
  intro x
  change (x.1 + 0, x.2) = x
  simp

theorem shiftHom_add (hm : 3 ≤ m) (k l : Fin m) :
    shiftHom (L := L) hm (k + l) = (shiftHom hm l).comp (shiftHom hm k) := by
  apply DFunLike.ext
  intro x
  change (x.1 + (k + l), x.2) = ((x.1 + k) + l, x.2)
  rw [add_assoc]

def lastRowPotential (hm : 3 ≤ m) (x : Vertex m L) : ZMod 2 :=
  if x.1 = lastRow m hm then 1 else 0

theorem nextRow_weight_shift_one (hm : 3 ≤ m) (r s : Fin m)
    (h : NextRow r s) (c d : Fin L) :
    meridianWeight hm s((r + 1, c), (s + 1, d)) =
      meridianWeight hm s((r, c), (s, d)) +
        lastRowPotential hm (r, c) + lastRowPotential hm (s, d) := by
  rw [meridianWeight_nextRow hm _ _ ((nextRow_add_iff hm r s 1).mpr h),
    meridianWeight_nextRow hm _ _ h]
  have hs : s = r + 1 := (nextRow_iff_add_one hm r s).mp h
  rw [← hs]
  unfold lastRowPotential
  rw [ZModModule.add_self, zero_add]

theorem forward_weight_shift_one (hm : 3 ≤ m) (x y : Vertex m L)
    (h : Forward x y) :
    meridianWeight hm s(shiftVertex 1 x, shiftVertex 1 y) =
      meridianWeight hm s(x, y) + lastRowPotential hm x + lastRowPotential hm y := by
  rcases x with ⟨r, c⟩
  rcases y with ⟨s, d⟩
  rcases h with ⟨_, hrow⟩ | ⟨hr, _⟩ | ⟨hrow, _⟩
  · exact nextRow_weight_shift_one hm r s hrow c d
  · cases hr
    simp only [shiftVertex, meridianWeight_sameRow, zero_add]
    change 0 = (if r = lastRow m hm then 1 else 0) +
      (if r = lastRow m hm then 1 else 0)
    exact (ZModModule.add_self _).symm
  · exact nextRow_weight_shift_one hm r s hrow c d

theorem edge_weight_shift_one (hm : 3 ≤ m) {x y : Vertex m L}
    (h : (graph m L hm).Adj x y) :
    meridianWeight hm (Sym2.map (shiftHom hm 1) s(x, y)) =
      meridianWeight hm s(x, y) + lastRowPotential hm x + lastRowPotential hm y := by
  rw [Sym2.map_pair_eq]
  rcases h with h | h
  · exact forward_weight_shift_one hm x y h
  · have hrev := forward_weight_shift_one hm y x h
    simpa only [Sym2.eq_swap, add_comm, add_left_comm, add_assoc] using hrev

/-- Every closed walk preserves the fixed-meridian parity after a one-row
rotation. This is proved by endpoint-potential cancellation, not topology. -/
theorem typeParity_shift_one (hm : 3 ≤ m) {x : Vertex m L}
    (p : (graph m L hm).Walk x x) :
    typeParity hm (p.map (shiftHom hm 1)) = typeParity hm p := by
  have h := EdgeCoboundary.edgeWeight_eq_of_closed
    (meridianWeight hm) (fun e => meridianWeight hm (Sym2.map (shiftHom hm 1) e))
    (lastRowPotential hm) (edge_weight_shift_one hm) p
  simpa only [typeParity, CylinderSplice.edgeWeight, Walk.edges_map,
    List.map_map, Function.comp_def] using h

/-- Every finite row shift preserves parity on every closed walk. -/
theorem typeParity_shift (hm : 3 ≤ m) (k : Fin m) {x : Vertex m L}
    (p : (graph m L hm).Walk x x) :
    typeParity hm (p.map (shiftHom hm k)) = typeParity hm p := by
  have hnat : ∀ j : ℕ, typeParity hm (p.map (shiftHom hm (j : Fin m))) = typeParity hm p := by
    intro j
    induction j with
    | zero =>
      change typeParity hm (p.map (shiftHom hm 0)) = typeParity hm p
      rw [shiftHom_zero, Walk.map_id]
    | succ j ih =>
      rw [Nat.cast_succ, shiftHom_add, ← Walk.map_map, typeParity_shift_one, ih]
  have hk : (k.val : Fin m) = k := by
    apply Fin.ext
    change k.val % m = k.val
    exact Nat.mod_eq_of_lt k.isLt
  have h := hnat k.val
  rw [hk] at h
  exact h

theorem shifted_vertical_mem (hm : 3 ≤ m) (k r s : Fin m) (c : Fin L)
    {x y : Vertex m L} (p : (graph m L hm).Walk x y)
    (hmem : s((r - k, c), (s - k, c)) ∈ p.edges) :
    s((r, c), (s, c)) ∈ (p.map (shiftHom hm k)).edges := by
  rw [Walk.edges_map]
  apply List.mem_map.mpr
  refine ⟨s((r - k, c), (s - k, c)), hmem, ?_⟩
  rw [Sym2.map_pair_eq]
  change s(((r - k) + k, c), ((s - k) + k, c)) = s((r, c), (s, c))
  simp only [sub_add_cancel]

end Shifts

/-- There are at least three row shifts, so two forbidden shifts cannot
exhaust them. The forbidden shifts need not be distinct. -/
theorem exists_row_avoiding_two {m : ℕ} (hm : 3 ≤ m) (a b : Fin m) :
    ∃ k : Fin m, k ≠ a ∧ k ≠ b := by
  have hpair : ({a, b} : Finset (Fin m)).card ≤ 2 := by
    simpa using Finset.card_insert_le a ({b} : Finset (Fin m))
  have hlt : ({a, b} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_not_mem_of_card_lt_card hlt
  refine ⟨k, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk

/-- Any prescribed left and right cyclic row gaps can be selected
simultaneously by a rotated three-column auxiliary. The resulting cycle is
Hamiltonian and has parity one in the original, fixed meridian convention. -/
theorem exists_aligned_three_column_auxiliary (m : ℕ) (hm : 3 ≤ m)
    (r s q t : Fin m) (hleftGap : NextRow r s) (hrightGap : NextRow q t) :
    ∃ v : Vertex m 3, ∃ C : (graph m 3 hm).Walk v v,
      C.IsHamiltonianCycle ∧ typeParity hm C = 1 ∧
      s((r, (0 : Fin 3)), (s, (0 : Fin 3))) ∈ C.edges ∧
      s((q, (2 : Fin 3)), (t, (2 : Fin 3))) ∈ C.edges := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨v, C, hC, hparity, hleft, hright⟩ := exists_three_column_auxiliary m hm
  obtain ⟨k, hkr, hkq⟩ := exists_row_avoiding_two hm r (q - lastRow m hm)
  have hfirst : firstRow m hm = (0 : Fin m) := by
    apply Fin.ext
    rfl
  have hleftPre : r - k ≠ firstRow m hm := by
    intro heq
    have hsum := congrArg (fun z : Fin m => z + k) heq
    change (r - k) + k = firstRow m hm + k at hsum
    rw [sub_add_cancel, hfirst, zero_add] at hsum
    exact hkr hsum.symm
  have hrightPre : q - k ≠ lastRow m hm := by
    intro heq
    apply hkq
    apply (eq_sub_iff_add_eq).mpr
    have hq : q = lastRow m hm + k := (sub_eq_iff_eq_add).mp heq
    simpa only [add_comm] using hq.symm
  have hleftMem := (hleft (r - k) (s - k)
    ((nextRow_sub_iff hm r s k).mpr hleftGap)).mpr hleftPre
  have hrightMem := (hright (q - k) (t - k)
    ((nextRow_sub_iff hm q t k).mpr hrightGap)).mpr hrightPre
  refine ⟨(shiftHom hm k) v, C.map (shiftHom hm k),
    hC.map (shiftHom hm k) (shiftVertex_bijective k), ?_, ?_, ?_⟩
  · rw [typeParity_shift, hparity]
  · exact shifted_vertical_mem hm k r s 0 C hleftMem
  · exact shifted_vertical_mem hm k q t 2 C hrightMem

#print axioms typeParity_shift
#print axioms exists_row_avoiding_two
#print axioms exists_aligned_three_column_auxiliary

end TriangularCylinder
