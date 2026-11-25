import ExteriorGeometry

/-!
# One canonical code for each physical exterior observation

A canonical code uses the existing V/H/D geometry and sets all unobserved
free flags to false. These flags are placeholders: the existing exterior
agreement predicate still ignores them, so selected free edges are allowed.
All canonical codes are included, whether or not any Hamiltonian selection
has that exterior. Impossible observations receive zero mass.

Every finite edge set has exactly one such exterior code. Consequently the
exterior indicators partition one, and their physical parity masses sum to
the existing unconditioned physical weighted count. No interval-validity,
Hamiltonian-realizability, weight-positivity, or normalization premise is
needed for these identities.
-/

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace TriangularCylinder.Transfer

open CountedHamiltonian TriangularEdgeEncoding

/-- A unique geometry representative of an exterior prescription. False
free flags are unobserved placeholders, not absent-edge requirements. -/
def CanonicalExteriorCode (m n a b : ℕ) :=
  {σ : ColumnGeometry m (n + 2) //
    ∀ id : EdgeId m (n + 2), freePhysicalId a b id → geometryFlag σ id = false}

instance canonicalExteriorCodeFintype (m n a b : ℕ) :
    Fintype (CanonicalExteriorCode m n a b) := by
  classical
  unfold CanonicalExteriorCode
  exact Fintype.ofFinite _

/-- Record exactly the selected exterior IDs of a finite unordered edge set.
The edge set need not be ambient-valid or Hamiltonian. -/
def encodeExterior {m n : ℕ} (hm : 3 ≤ m) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) : CanonicalExteriorCode m n a b := by
  classical
  refine ⟨geometryOfIds (Finset.univ.filter fun id =>
    ¬ freePhysicalId a b id ∧ toEdge hm id ∈ E), ?_⟩
  intro id hfree
  simp only [geometryFlag_ofIds, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [hfree, not_true_eq_false, false_and, decide_false]

/-- Each encoded flag is selected membership restricted to the exterior. -/
theorem encodeExterior_flag {m n : ℕ} (hm : 3 ≤ m) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) (id : EdgeId m (n + 2)) :
    geometryFlag (encodeExterior hm a b E).val id =
      decide (¬ freePhysicalId a b id ∧ toEdge hm id ∈ E) := by
  classical
  simp only [encodeExterior, geometryFlag_ofIds, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Encoding never constrains selected free edges: it agrees exactly where
the original physical exterior predicate makes an observation. -/
theorem exteriorAgrees_encodeExterior {m n : ℕ} (hm : 3 ≤ m) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) :
    ExteriorAgrees hm (encodeExterior hm a b E).val a b E := by
  intro id houtside
  rw [encodeExterior_flag]
  simp only [houtside, not_false_eq_true, true_and, decide_eq_true_eq]

/-- Exterior agreement is equality with the unique canonical observation.
This includes arbitrary finite edge sets and impossible prescribed codes. -/
theorem exteriorAgrees_iff_encodeExterior_eq {m n : ℕ} (hm : 3 ≤ m) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) (σ : CanonicalExteriorCode m n a b) :
    ExteriorAgrees hm σ.val a b E ↔ encodeExterior hm a b E = σ := by
  classical
  constructor
  · intro h
    apply Subtype.ext
    apply idsOfGeometry_injective
    ext id
    rw [mem_idsOfGeometry, mem_idsOfGeometry, encodeExterior_flag]
    by_cases hfree : freePhysicalId a b id
    · simp only [hfree, not_true_eq_false, false_and, decide_false,
        σ.property id hfree]
    · simpa only [hfree, not_false_eq_true, true_and, decide_eq_true_eq]
        using h id hfree
  · intro h
    rw [← h]
    exact exteriorAgrees_encodeExterior hm a b E

variable {R : Type*} [CommSemiring R]

/-- Exactly one canonical exterior event contains each finite edge set. -/
theorem sum_exteriorIndicator {m n : ℕ} (hm : 3 ≤ m) (a b : ℕ)
    (E : Finset (Sym2 (Vertex m (n + 2)))) :
    (∑ σ : CanonicalExteriorCode m n a b,
      exteriorIndicator (R := R) hm σ.val a b E) = 1 := by
  classical
  simp only [exteriorIndicator, exteriorAgrees_iff_encodeExterior_eq]
  simp

/-- The canonical exterior masses partition the existing physical weighted
parity count, with no duplicated free-bit observations. -/
theorem sum_exteriorParityCount {m n : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w : Sym2 (Vertex m (n + 2)) → R) (a b : ℕ) :
    (∑ σ : CanonicalExteriorCode m n a b,
      exteriorParityCount hm p w σ.val a b) = weightedParityCount hm p w := by
  classical
  unfold exteriorParityCount weightedParityCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum, sum_exteriorIndicator, mul_one]

end TriangularCylinder.Transfer
