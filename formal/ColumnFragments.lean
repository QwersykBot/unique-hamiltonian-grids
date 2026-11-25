import ColumnCut

/-!
# Ambient validity of independently cut column fragments

A prefix is normalized to j+1 columns with the boundary last. A suffix is
normalized to k+1 columns with the boundary first, and owns no boundary-to-
boundary edges. Their permitted ambient edges depend only on their own
lengths. Gluing any two permitted fragments yields a selected subgraph of
the actual cylinder after the canonical column-cut transport.
No connectivity, degree, parity, or state-sufficiency conclusion is asserted.
-/

namespace TriangularCylinder.ColumnFragments

open SimpleGraph

def prefixCoord {m : ℕ} (j : ℕ) : Vertex m j ⊕ Fin m → Vertex m (j + 1)
  | Sum.inl x => (x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩)
  | Sum.inr r => (r, ⟨j, by omega⟩)

def suffixCoord {m : ℕ} (k : ℕ) : Vertex m k ⊕ Fin m → Vertex m (k + 1)
  | Sum.inl x => (x.1, ⟨x.2.val + 1, by have := x.2.isLt; omega⟩)
  | Sum.inr r => (r, ⟨0, by omega⟩)

/-- Forward adjacency is exactly preserved by a common nonnegative column
translation when the row labels are preserved. -/
theorem forward_iff_of_coordinate_shift {m L L' d : ℕ}
    {x y : Vertex m L} {x' y' : Vertex m L'}
    (hxr : x'.1 = x.1) (hyr : y'.1 = y.1)
    (hxc : x'.2.val = d + x.2.val) (hyc : y'.2.val = d + y.2.val) :
    Forward x' y' ↔ Forward x y := by
  have hcol : x'.2 = y'.2 ↔ x.2 = y.2 := by
    simp only [Fin.ext_iff, hxc, hyc, Nat.add_left_cancel_iff]
  have hnext : x'.2.val + 1 = y'.2.val ↔ x.2.val + 1 = y.2.val := by
    simp only [hxc, hyc, Nat.add_assoc, Nat.add_left_cancel_iff]
  simp only [Forward, hxr, hyr, hcol, hnext]

theorem prefixVertex_row {m j k : ℕ} (x : Vertex m j ⊕ Fin m) :
    (ColumnCut.prefixVertex j k x).1 = (prefixCoord j x).1 := by
  cases x <;> rfl

theorem prefixVertex_col {m j k : ℕ} (x : Vertex m j ⊕ Fin m) :
    (ColumnCut.prefixVertex j k x).2.val = (prefixCoord j x).2.val := by
  cases x <;> rfl

theorem suffixVertex_row {m j k : ℕ} (x : Vertex m k ⊕ Fin m) :
    (ColumnCut.suffixVertex j k x).1 = (suffixCoord k x).1 := by
  cases x <;> rfl

theorem suffixVertex_col {m j k : ℕ} (x : Vertex m k ⊕ Fin m) :
    (ColumnCut.suffixVertex j k x).2.val = j + (suffixCoord k x).2.val := by
  cases x with
  | inl x =>
    change j + 1 + x.2.val = j + (x.2.val + 1)
    omega
  | inr r =>
    change j = j + 0
    rfl

theorem forward_prefix_iff {m j k : ℕ} (x y : Vertex m j ⊕ Fin m) :
    Forward (ColumnCut.prefixVertex j k x) (ColumnCut.prefixVertex j k y) ↔
      Forward (prefixCoord j x) (prefixCoord j y) :=
  forward_iff_of_coordinate_shift (d := 0) (prefixVertex_row x) (prefixVertex_row y)
    (by simpa only [Nat.zero_add] using prefixVertex_col (k := k) x)
    (by simpa only [Nat.zero_add] using prefixVertex_col (k := k) y)

theorem forward_suffix_iff {m j k : ℕ} (x y : Vertex m k ⊕ Fin m) :
    Forward (ColumnCut.suffixVertex j k x) (ColumnCut.suffixVertex j k y) ↔
      Forward (suffixCoord k x) (suffixCoord k y) :=
  forward_iff_of_coordinate_shift (d := j) (suffixVertex_row x) (suffixVertex_row y)
    (suffixVertex_col x) (suffixVertex_col y)

theorem prefixVertex_adj_iff {m j k : ℕ} (hm : 3 ≤ m) (x y : Vertex m j ⊕ Fin m) :
    (graph m (j + 1 + k) hm).Adj (ColumnCut.prefixVertex j k x) (ColumnCut.prefixVertex j k y) ↔
      (graph m (j + 1) hm).Adj (prefixCoord j x) (prefixCoord j y) :=
  or_congr (forward_prefix_iff x y) (forward_prefix_iff y x)

theorem suffixVertex_adj_iff {m j k : ℕ} (hm : 3 ≤ m) (x y : Vertex m k ⊕ Fin m) :
    (graph m (j + 1 + k) hm).Adj (ColumnCut.suffixVertex j k x) (ColumnCut.suffixVertex j k y) ↔
      (graph m (k + 1) hm).Adj (suffixCoord k x) (suffixCoord k y) :=
  or_congr (forward_suffix_iff x y) (forward_suffix_iff y x)

/-- Permitted prefix edges in j+1 columns, independent of any old suffix length. -/
def prefixAmbient {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    SimpleGraph (Vertex m j ⊕ Fin m) :=
  (graph m (j + 1) hm).comap (prefixCoord j)

/-- Permitted suffix edges in k+1 columns, independent of any old prefix length.
The boundary is column zero and owns no edges internally. -/
def suffixAmbient {m : ℕ} (hm : 3 ≤ m) (k : ℕ) :
    SimpleGraph (Vertex m k ⊕ Fin m) where
  Adj x y := (graph m (k + 1) hm).Adj (suffixCoord k x) (suffixCoord k y) ∧
    ∃ o : Vertex m k, x = Sum.inl o ∨ y = Sum.inl o
  symm _ _ h := by
    obtain ⟨hxy, o, ho⟩ := h
    exact ⟨hxy.symm, o, ho.symm⟩
  loopless x h := (graph m (k + 1) hm).loopless _ h.1

theorem suffixAmbient_no_boundary_edges {m k : ℕ} (hm : 3 ≤ m) (r s : Fin m) :
    ¬ (suffixAmbient hm k).Adj (Sum.inr r) (Sum.inr s) := by
  rintro ⟨_, o, h | h⟩ <;> cases h

/-- Every actual selected prefix obeys the normalized prefix ambient. -/
theorem prefixPart_le_prefixAmbient {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) :
    ColumnCut.prefixPart j k H ≤ prefixAmbient hm j := by
  intro x y h
  exact (prefixVertex_adj_iff hm x y).mp (hH h)

/-- Every actual selected suffix obeys the normalized suffix ambient. -/
theorem suffixPart_le_suffixAmbient {m j k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + k))}
    (hH : H ≤ graph m (j + 1 + k) hm) :
    ColumnCut.suffixPart j k H ≤ suffixAmbient hm k := by
  intro x y h
  exact ⟨(suffixVertex_adj_iff hm x y).mp (hH h.1), h.2⟩

/-- Any two permitted fragments glue to legal physical ambient edges. -/
theorem glue_permitted_le_comap {m j k : ℕ} (hm : 3 ≤ m)
    {P : SimpleGraph (Vertex m j ⊕ Fin m)}
    {Q : SimpleGraph (Vertex m k ⊕ Fin m)}
    (hP : P ≤ prefixAmbient hm j) (hQ : Q ≤ suffixAmbient hm k) :
    CylinderFrontier.glue P Q ≤ (graph m (j + 1 + k) hm).comap (ColumnCut.vertexEquiv m j k) := by
  intro x y h
  rcases h with hp | hq
  · rcases hp with ⟨u, v, huv, rfl, rfl⟩
    exact (prefixVertex_adj_iff hm u v).mpr (hP huv)
  · rcases hq with ⟨u, v, huv, rfl, rfl⟩
    exact (suffixVertex_adj_iff hm u v).mpr (hQ huv).1

def transportedGlue {m j k : ℕ}
    (P : SimpleGraph (Vertex m j ⊕ Fin m))
    (Q : SimpleGraph (Vertex m k ⊕ Fin m)) : SimpleGraph (Vertex m (j + 1 + k)) :=
  (CylinderFrontier.glue P Q).map (ColumnCut.vertexEquiv m j k).toEmbedding

/-- The canonical transport of the glued fragments is a selected subgraph
of the actual consistently triangulated cylinder. -/
theorem transportedGlue_le {m j k : ℕ} (hm : 3 ≤ m)
    {P : SimpleGraph (Vertex m j ⊕ Fin m)}
    {Q : SimpleGraph (Vertex m k ⊕ Fin m)}
    (hP : P ≤ prefixAmbient hm j) (hQ : Q ≤ suffixAmbient hm k) :
    transportedGlue P Q ≤ graph m (j + 1 + k) hm := by
  intro x y h
  rcases h with ⟨u, v, huv, rfl, rfl⟩
  exact glue_permitted_le_comap hm hP hQ huv

/-- Prefix and suffix cuts can come from different original lengths. Their
canonical join still has only legal ambient edges. -/
theorem mixed_cut_parts_le {m j oldSuffix oldPrefix k : ℕ} (hm : 3 ≤ m)
    {H : SimpleGraph (Vertex m (j + 1 + oldSuffix))}
    {K : SimpleGraph (Vertex m (oldPrefix + 1 + k))}
    (hH : H ≤ graph m (j + 1 + oldSuffix) hm)
    (hK : K ≤ graph m (oldPrefix + 1 + k) hm) :
    transportedGlue (ColumnCut.prefixPart j oldSuffix H) (ColumnCut.suffixPart oldPrefix k K) ≤
      graph m (j + 1 + k) hm :=
  transportedGlue_le hm (prefixPart_le_prefixAmbient hm hH) (suffixPart_le_suffixAmbient hm hK)

#print axioms forward_iff_of_coordinate_shift
#print axioms forward_prefix_iff
#print axioms forward_suffix_iff
#print axioms prefixVertex_adj_iff
#print axioms suffixVertex_adj_iff
#print axioms suffixAmbient_no_boundary_edges
#print axioms prefixPart_le_prefixAmbient
#print axioms suffixPart_le_suffixAmbient
#print axioms glue_permitted_le_comap
#print axioms transportedGlue_le
#print axioms mixed_cut_parts_le

end TriangularCylinder.ColumnFragments
