import WeightedCountImbalance
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Independent physical edge likelihoods

For a fixed report, `q1 e` and `q0 e` are its likelihood factors when the
actual unordered edge `e` is respectively selected or absent. The product
over the ambient graph's edge finset expresses conditional independence.
The factors need not be normalized probabilities for the algebra below.

The counted objects remain the existing undirected Hamiltonian selections.
A common base activity `w` supplies an edge-product prior; `w = 1` gives
equal weight per selection. No arbitrary prior, class-dependent likelihood,
posterior normalization, or topology interpretation is included.
-/

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace CountedHamiltonian

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]

/-- The fixed report likelihood, with one factor for each actual edge. -/
def selectionLikelihood (q1 q0 : Sym2 V → ℝ) (s : Selection G) : ℝ :=
  ∏ e ∈ G.edgeFinset, if e ∈ s.val then q1 e else q0 e

/-- The absent-edge reference product depends on the report and graph,
but not on the selected Hamiltonian cycle or its parity. -/
def absentLikelihoodProduct (q0 : Sym2 V → ℝ) : ℝ :=
  ∏ e ∈ G.edgeFinset, q0 e

/-- A finite independent likelihood factors into one common report factor
and the selected-edge product of likelihood ratios. Only actual edges
require a nonzero absent likelihood. -/
theorem selectionLikelihood_eq_product (q1 q0 : Sym2 V → ℝ)
    (hq0 : ∀ e ∈ G.edgeSet, q0 e ≠ 0) (s : Selection G) :
    selectionLikelihood G q1 q0 s =
      absentLikelihoodProduct G q0 *
        selectionProduct G (fun e => q1 e / q0 e) s := by
  classical
  have hsubset : s.val ⊆ G.edgeFinset :=
    fun e he => SimpleGraph.mem_edgeFinset.mpr (selection_edge_mem G s he)
  calc
    _ = ∏ e ∈ G.edgeFinset,
        q0 e * (if e ∈ s.val then q1 e / q0 e else 1) := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases hs : e ∈ s.val
      · simpa only [if_pos hs] using
          (mul_div_cancel₀ (q1 e) (hq0 e (SimpleGraph.mem_edgeFinset.mp he))).symm
      · simp only [if_neg hs, mul_one]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem,
        Finset.inter_eq_right.mpr hsubset]
      rfl

/-- A common edge-product base activity multiplies the same physical
likelihood ratios, without changing the report-only factor. -/
theorem weightedSelectionLikelihood_eq_product (w q1 q0 : Sym2 V → ℝ)
    (hq0 : ∀ e ∈ G.edgeSet, q0 e ≠ 0) (s : Selection G) :
    selectionProduct G w s * selectionLikelihood G q1 q0 s =
      absentLikelihoodProduct G q0 *
        selectionProduct G (fun e => w e * (q1 e / q0 e)) s := by
  rw [selectionLikelihood_eq_product G q1 q0 hq0 s]
  simp only [selectionProduct, Finset.prod_mul_distrib]
  exact mul_left_comm _ _ _

omit [DecidableEq V] in
theorem absentLikelihoodProduct_pos (q0 : Sym2 V → ℝ)
    (hq0 : ∀ e ∈ G.edgeSet, 0 < q0 e) :
    0 < absentLikelihoodProduct G q0 := by
  exact Finset.prod_pos
    (fun e he => hq0 e (SimpleGraph.mem_edgeFinset.mp he))

theorem selectionLikelihood_nonneg (q1 q0 : Sym2 V → ℝ)
    (hq1 : ∀ e ∈ G.edgeSet, 0 ≤ q1 e)
    (hq0 : ∀ e ∈ G.edgeSet, 0 ≤ q0 e) (s : Selection G) :
    0 ≤ selectionLikelihood G q1 q0 s := by
  apply Finset.prod_nonneg
  intro e he
  split_ifs
  · exact hq1 e (SimpleGraph.mem_edgeFinset.mp he)
  · exact hq0 e (SimpleGraph.mem_edgeFinset.mp he)

end CountedHamiltonian

namespace TriangularCylinder.Transfer

open CountedHamiltonian

/-- Physical fixed-report mass in one existing meridian-parity class.
The same base activity and both likelihood fields are used for all classes. -/
def noisyParityMass {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w q1 q0 : Sym2 (Vertex m L) → ℝ) : ℝ := by
  classical
  exact ∑ s : ParitySelection hm p L,
    selectionProduct (graph m L hm) w s.val *
      selectionLikelihood (graph m L hm) q1 q0 s.val

/-- Exact physical mass identity at every width. There is no transfer-length
restriction or assumption that either parity class is nonempty. -/
theorem noisyParityMass_eq_weightedParityCount {m L : ℕ} (hm : 3 ≤ m)
    (p : ZMod 2) (w q1 q0 : Sym2 (Vertex m L) → ℝ)
    (hq0 : ∀ e ∈ (graph m L hm).edgeSet, q0 e ≠ 0) :
    noisyParityMass hm p w q1 q0 =
      absentLikelihoodProduct (graph m L hm) q0 *
        weightedParityCount hm p (fun e => w e * (q1 e / q0 e)) := by
  classical
  unfold noisyParityMass
  simp_rw [weightedSelectionLikelihood_eq_product (graph m L hm) w q1 q0 hq0]
  rw [← Finset.mul_sum]
  rfl

/-- Nonnegative physical activities and likelihoods give nonnegative mass,
including empty parity classes and likelihood factors equal to zero. -/
theorem noisyParityMass_nonneg {m L : ℕ} (hm : 3 ≤ m) (p : ZMod 2)
    (w q1 q0 : Sym2 (Vertex m L) → ℝ)
    (hw : ∀ e ∈ (graph m L hm).edgeSet, 0 ≤ w e)
    (hq1 : ∀ e ∈ (graph m L hm).edgeSet, 0 ≤ q1 e)
    (hq0 : ∀ e ∈ (graph m L hm).edgeSet, 0 ≤ q0 e) :
    0 ≤ noisyParityMass hm p w q1 q0 := by
  classical
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg
    (Finset.prod_nonneg (fun e he => hw e (selection_edge_mem (graph m L hm) s.val he)))
    (selectionLikelihood_nonneg (graph m L hm) q1 q0 hq1 hq0 s.val)

/-- Uniform finite parity imbalance for a fixed report's physical mass.
The constants precede the width and all three shared edge fields. Bounds
are imposed only on actual edges; absent likelihoods need only positivity,
not a uniform lower bound. The likelihood-ratio and base-activity bounds
are fixed independently of the width and report. -/
theorem exists_noisyParityMass_geometric_imbalance {m : ℕ} (hm : 3 ≤ m)
    {activityLower activityUpper ratioLower ratioUpper : ℝ}
    (hactivity : 0 < activityLower) (hratio : 0 < ratioLower) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ rho : ℝ, 0 ≤ rho ∧ rho < 1 ∧
      ∀ L : ℕ, 3 ≤ L → ∀ w q1 q0 : Sym2 (Vertex m L) → ℝ,
        (∀ e ∈ (graph m L hm).edgeSet,
          activityLower ≤ w e ∧ w e ≤ activityUpper) →
        (∀ e ∈ (graph m L hm).edgeSet, 0 < q0 e) →
        (∀ e ∈ (graph m L hm).edgeSet,
          ratioLower ≤ q1 e / q0 e ∧ q1 e / q0 e ≤ ratioUpper) →
        |noisyParityMass hm 0 w q1 q0 - noisyParityMass hm 1 w q1 q0| ≤
          rho ^ ((L - 2) / N) *
            (noisyParityMass hm 0 w q1 q0 + noisyParityMass hm 1 w q1 q0) := by
  classical
  obtain ⟨N, hN, rho, hrho0, hrho1, hbound⟩ :=
    exists_weightedParityCount_geometric_imbalance hm
      (M := activityUpper * ratioUpper) (mul_pos hactivity hratio)
  refine ⟨N, hN, rho, hrho0, hrho1, ?_⟩
  intro L hL w q1 q0 hw hq0 hratios
  have heffective : ∀ e ∈ (graph m L hm).edgeSet,
      activityLower * ratioLower ≤ w e * (q1 e / q0 e) ∧
        w e * (q1 e / q0 e) ≤ activityUpper * ratioUpper := by
    intro e he
    obtain ⟨hwl, hwu⟩ := hw e he
    obtain ⟨hrl, hru⟩ := hratios e he
    exact ⟨mul_le_mul hwl hrl hratio.le (hactivity.le.trans hwl),
      mul_le_mul hwu hru (hratio.le.trans hrl) ((hactivity.le.trans hwl).trans hwu)⟩
  have hfinite := hbound L hL (fun e => w e * (q1 e / q0 e)) heffective
  have hcommon := absentLikelihoodProduct_pos (graph m L hm) q0 hq0
  have hnonzero : ∀ e ∈ (graph m L hm).edgeSet, q0 e ≠ 0 :=
    fun e he => (hq0 e he).ne'
  rw [noisyParityMass_eq_weightedParityCount hm 0 w q1 q0 hnonzero,
    noisyParityMass_eq_weightedParityCount hm 1 w q1 q0 hnonzero,
    ← mul_sub, abs_mul, abs_of_pos hcommon]
  calc
    _ ≤ absentLikelihoodProduct (graph m L hm) q0 *
        (rho ^ ((L - 2) / N) *
          (weightedParityCount hm 0 (fun e => w e * (q1 e / q0 e)) +
            weightedParityCount hm 1 (fun e => w e * (q1 e / q0 e)))) :=
      mul_le_mul_of_nonneg_left hfinite hcommon.le
    _ = _ := by ring

end TriangularCylinder.Transfer
