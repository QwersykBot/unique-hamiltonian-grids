import GenericEdgeWeights
import TriangularParity
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-!
Finite counted objects for the exact undirected selected-edge convention.
A selection is a finite set of undirected edges with an actual Mathlib
Hamiltonian-cycle witness.  Witnesses are propositions, not additional
counted data.  Parity is a finite sum on the selected edges.
No transfer formula, asymptotic statement, or topology identification is
claimed in this development.
-/

namespace CountedHamiltonian

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The witness uses Mathlib's standard, nondegenerate Hamiltonian-cycle
predicate.  A root and direction are existential witnesses only. -/
def HasHamiltonianRealization (E : Finset (Sym2 V)) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v,
    p.IsHamiltonianCycle ∧ selectedEdges p = E

/-- The intended objects to count: one element per undirected selected
Hamiltonian edge set on the fixed vertex labels. -/
def Selection := {E : Finset (Sym2 V) // HasHamiltonianRealization G E}

noncomputable instance [Fintype V] : Fintype (Selection G) := by
  classical
  unfold Selection
  exact Fintype.ofFinite _

def ofCycle {v : V} (p : G.Walk v v) (hp : p.IsHamiltonianCycle) : Selection G :=
  ⟨selectedEdges p, v, p, hp, rfl⟩

theorem selection_eq_iff (x y : Selection G) : x = y ↔ x.val = y.val :=
  Subtype.ext_iff

theorem ofCycle_eq_iff {v w : V} (p : G.Walk v v) (q : G.Walk w w)
    (hp : p.IsHamiltonianCycle) (hq : q.IsHamiltonianCycle) :
    ofCycle G p hp = ofCycle G q hq ↔ selectedEdges p = selectedEdges q :=
  Subtype.ext_iff

/-- Every counted edge set has a genuine Hamiltonian presentation. -/
theorem selection_has_presentation (s : Selection G) :
    ∃ v : V, ∃ p : G.Walk v v, ∃ hp : p.IsHamiltonianCycle, ofCycle G p hp = s := by
  rcases s.property with ⟨v, p, hp, he⟩
  exact ⟨v, p, hp, Subtype.ext he⟩

/-- Presentations retain a start and traversal, unlike selections. -/
def Presentation := Σ v : V, {p : G.Walk v v // p.IsHamiltonianCycle}

def presentationSelection (p : Presentation G) : Selection G :=
  ofCycle G p.2.val p.2.property

theorem presentationSelection_surjective :
    Function.Surjective (presentationSelection G) := by
  intro s
  rcases selection_has_presentation G s with ⟨v, p, hp, h⟩
  exact ⟨⟨v, p, hp⟩, h⟩

theorem selection_edge_mem (s : Selection G) {e : Sym2 V} (he : e ∈ s.val) :
    e ∈ G.edgeSet := by
  rcases s.property with ⟨v, p, hp, hs⟩
  rw [← hs] at he
  exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)

theorem selection_card [Fintype V] (s : Selection G) :
    s.val.card = Fintype.card V := by
  rcases s.property with ⟨v, p, hp, hs⟩
  rw [← hs]
  change p.edges.toFinset.card = Fintype.card V
  exact (List.toFinset_card_of_nodup hp.isCycle.isTrail.edges_nodup).trans
    ((Walk.length_edges p).trans hp.length_eq)

theorem selection_three_le_card [Fintype V] (s : Selection G) :
    3 ≤ Fintype.card V := by
  rcases s.property with ⟨v, p, hp, hs⟩
  rw [← hp.length_eq]
  exact hp.isCycle.three_le_length

def selectionWeight {W : Type*} [AddCommMonoid W] (w : Sym2 V → W)
    (s : Selection G) : W := ∑ e ∈ s.val, w e

/-- The weight depends only on the selected edge set and agrees with the
standard walk sum for every Hamiltonian presentation. -/
theorem selectionWeight_ofCycle {W : Type*} [AddCommMonoid W]
    (w : Sym2 V → W) {v : V} (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    selectionWeight G w (ofCycle G p hp) = CylinderSplice.edgeWeight w p := by
  exact (edgeWeight_eq_sum_selectedEdges w p hp.isCycle.isTrail).symm

end CountedHamiltonian

namespace TriangularCylinder

open CountedHamiltonian
open scoped BigOperators

/-- Parity on the finite selected-edge object, without choosing a walk. -/
def selectionParity {m L : ℕ} (hm : 3 ≤ m)
    (s : Selection (graph m L hm)) : ZMod 2 :=
  selectionWeight (graph m L hm) (meridianWeight hm) s

theorem selectionParity_ofCycle {m L : ℕ} (hm : 3 ≤ m) {v : Vertex m L}
    (p : (graph m L hm).Walk v v) (hp : p.IsHamiltonianCycle) :
    selectionParity hm (ofCycle (graph m L hm) p hp) = typeParity hm p := by
  exact selectionWeight_ofCycle (graph m L hm) (meridianWeight hm) p hp

/-- A finite count of selected Hamiltonian edge sets in one mod-two class.
The values zero and one are parity classes, not a formal topology claim. -/
noncomputable def parityCount (m L : ℕ) (hm : 3 ≤ m) (t : ZMod 2) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Selection (graph m L hm))).filter
    (fun s => selectionParity hm s = t)).card

theorem parity_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t <;> simp

/-- The two parity counts partition the finite undirected count exactly. -/
theorem parityCount_partition (m L : ℕ) (hm : 3 ≤ m) :
    parityCount m L hm 0 + parityCount m L hm 1 =
      Fintype.card (Selection (graph m L hm)) := by
  classical
  let S : Finset (Selection (graph m L hm)) := Finset.univ
  have hdis : Disjoint (S.filter (fun s => selectionParity hm s = 0))
      (S.filter (fun s => selectionParity hm s = 1)) := by
    apply Finset.disjoint_left.mpr
    intro s hs0 hs1
    have h0 := (Finset.mem_filter.mp hs0).2
    have h1 := (Finset.mem_filter.mp hs1).2
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    exact hne (h0.symm.trans h1)
  have hcover : S.filter (fun s => selectionParity hm s = 0) ∪
      S.filter (fun s => selectionParity hm s = 1) = S := by
    ext s
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hs, _⟩ | ⟨hs, _⟩) <;> exact hs
    · intro hs
      rcases parity_eq_zero_or_one (selectionParity hm s) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
  change (S.filter (fun s => selectionParity hm s = 0)).card +
    (S.filter (fun s => selectionParity hm s = 1)).card = _
  rw [← Finset.card_union_of_disjoint hdis, hcover]
  exact Finset.card_univ

#print axioms CountedHamiltonian.selection_has_presentation
#print axioms CountedHamiltonian.presentationSelection_surjective
#print axioms CountedHamiltonian.ofCycle_eq_iff
#print axioms CountedHamiltonian.selection_edge_mem
#print axioms CountedHamiltonian.selection_card
#print axioms CountedHamiltonian.selection_three_le_card
#print axioms CountedHamiltonian.selectionWeight_ofCycle
#print axioms selectionParity_ofCycle
#print axioms parityCount_partition

end TriangularCylinder
