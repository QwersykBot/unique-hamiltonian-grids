import TriangularParity

/-!
# Meridian classification for a positively oriented row step

This file concerns the concrete finite row relation and the already-defined
mod-two edge indicator. It makes no topological contractibility claim.
-/

namespace TriangularCylinder

/-- A cyclic row step is either the ordinary successor or the last-to-first
step. No lower bound on the circumference is needed for this case split. -/
theorem nextRow_cases {m : ℕ} {r s : Fin m} (h : NextRow r s) :
    r.val + 1 = s.val ∨ (r.val = m - 1 ∧ s.val = 0) := by
  have hr := r.isLt
  unfold NextRow at h
  by_cases hlt : r.val + 1 < m
  · left
    rw [Nat.mod_eq_of_lt hlt] at h
    exact h.symm
  · right
    have heq : r.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at h
    exact ⟨by omega, h⟩

/-- The wrap step exists in the positively oriented cyclic relation. -/
theorem nextRow_last_first {m : ℕ} (hm : 3 ≤ m) :
    NextRow (lastRow m hm) (firstRow m hm) := by
  change 0 = (m - 1 + 1) % m
  have heq : m - 1 + 1 = m := by omega
  rw [heq, Nat.mod_self]

/-- A step out of the last row arrives in the first row. -/
theorem nextRow_target_first_of_source_last {m : ℕ} (hm : 3 ≤ m)
    {r s : Fin m} (h : NextRow r s) (hr : r = lastRow m hm) :
    s = firstRow m hm := by
  have hrval : r.val = m - 1 := congrArg Fin.val hr
  have hslt := s.isLt
  rcases nextRow_cases h with hstep | ⟨_, hs⟩
  · exfalso
    omega
  · apply Fin.ext
    exact hs

theorem nextRow_source_last_iff_target_first {m : ℕ} (hm : 3 ≤ m)
    {r s : Fin m} (h : NextRow r s) :
    r = lastRow m hm ↔ s = firstRow m hm := by
  constructor
  · exact nextRow_target_first_of_source_last hm h
  · intro hs
    have hsval : s.val = 0 := congrArg Fin.val hs
    rcases nextRow_cases h with hstep | ⟨hr, _⟩
    · exfalso
      omega
    · apply Fin.ext
      exact hr

/-- For circumference at least three, the unordered row pair of a forward
step is the meridian pair exactly when its source is the last row. -/
theorem nextRow_pair_eq_meridian_iff {m : ℕ} (hm : 3 ≤ m)
    {r s : Fin m} (h : NextRow r s) :
    s(r, s) = s(lastRow m hm, firstRow m hm) ↔ r = lastRow m hm := by
  constructor
  · intro hpair
    rcases Sym2.eq_iff.mp hpair with ⟨hr, _⟩ | ⟨hr, hs⟩
    · exact hr
    · have hrval : r.val = 0 := congrArg Fin.val hr
      have hsval : s.val = m - 1 := congrArg Fin.val hs
      rcases nextRow_cases h with hstep | ⟨hwrap, _⟩ <;> exfalso <;> omega
  · intro hr
    exact Sym2.eq_iff.mpr (Or.inl
      ⟨hr, nextRow_target_first_of_source_last hm h hr⟩)

/-- The same formula handles forward vertical and forward diagonal edges,
because the column coordinates do not affect the meridian indicator. -/
theorem meridianWeight_nextRow {m L : ℕ} (hm : 3 ≤ m)
    (r s : Fin m) (h : NextRow r s) (c d : Fin L) :
    meridianWeight hm s((r, c), (s, d)) =
      if r = lastRow m hm then 1 else 0 := by
  simp only [meridianWeight_pair, nextRow_pair_eq_meridian_iff hm h]

@[simp]
theorem meridianWeight_last_first {m L : ℕ} (hm : 3 ≤ m) (c d : Fin L) :
    meridianWeight hm s((lastRow m hm, c), (firstRow m hm, d)) = 1 := by
  rw [meridianWeight_nextRow hm _ _ (nextRow_last_first hm)]
  simp

end TriangularCylinder
