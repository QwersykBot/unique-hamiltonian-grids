import CylinderSplice
import Mathlib.Data.List.FinRange

/-!
# Walks and cycles from finite vertex enumerations

An enumeration and adjacency of consecutive entries determine a graph walk.
The exact support and edge lists are retained. A bijective enumeration gives
a Hamiltonian path; an available closing edge gives a Hamiltonian cycle when
there are at least three enumerated vertices.

This is a generic constructor, not a cylinder theorem.
-/

namespace EnumeratedWalk

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Traverse a finite vertex enumeration in its given order. -/
def ofFnWalk : {n : ℕ} → (f : Fin (n + 1) → V) →
    (∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) →
    G.Walk (f 0) (f (Fin.last n))
  | 0, _, _ => .nil
  | n + 1, f, h => .cons (h 0)
      (ofFnWalk (fun i : Fin (n + 1) => f i.succ) (fun i => h i.succ))

@[simp]
theorem ofFnWalk_support {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) :
    (ofFnWalk f h).support = List.ofFn f := by
  induction n with
  | zero => simp [ofFnWalk]
  | succ n ih => simp [ofFnWalk, ih]

@[simp]
theorem ofFnWalk_edges {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) :
    (ofFnWalk f h).edges =
      List.ofFn (fun i : Fin n => s(f i.castSucc, f i.succ)) := by
  induction n with
  | zero => simp [ofFnWalk]
  | succ n ih => simp [ofFnWalk, ih, Fin.succ_castSucc]

@[simp]
theorem mem_ofFnWalk_support {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) (x : V) :
    x ∈ (ofFnWalk f h).support ↔ ∃ i, f i = x := by
  rw [ofFnWalk_support, List.mem_ofFn]

@[simp]
theorem mem_ofFnWalk_edges {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) (e : Sym2 V) :
    e ∈ (ofFnWalk f h).edges ↔ ∃ i : Fin n, s(f i.castSucc, f i.succ) = e := by
  rw [ofFnWalk_edges, List.mem_ofFn]

theorem ofFnWalk_isPath {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (hf : Function.Injective f) : (ofFnWalk f h).IsPath := by
  apply Walk.IsPath.mk'
  rw [ofFnWalk_support]
  exact List.nodup_ofFn.mpr hf

theorem ofFnWalk_isHamiltonian [DecidableEq V] {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (hf : Function.Bijective f) : (ofFnWalk f h).IsHamiltonian := by
  apply (ofFnWalk_isPath f h hf.injective).isHamiltonian_of_mem
  intro x
  exact (mem_ofFnWalk_support f h x).mpr (hf.surjective x)

/-- Put the closing edge first, followed by the enumerated path. -/
def ofFnCycle {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (close : G.Adj (f (Fin.last n)) (f 0)) :
    G.Walk (f (Fin.last n)) (f (Fin.last n)) :=
  .cons close (ofFnWalk f h)

@[simp]
theorem ofFnCycle_support {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (close : G.Adj (f (Fin.last n)) (f 0)) :
    (ofFnCycle f h close).support = f (Fin.last n) :: List.ofFn f := by
  simp [ofFnCycle]

@[simp]
theorem ofFnCycle_edges {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (close : G.Adj (f (Fin.last n)) (f 0)) :
    (ofFnCycle f h close).edges = s(f (Fin.last n), f 0) ::
      List.ofFn (fun i : Fin n => s(f i.castSucc, f i.succ)) := by
  simp [ofFnCycle]

@[simp]
theorem mem_ofFnCycle_edges {n : ℕ} (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (close : G.Adj (f (Fin.last n)) (f 0)) (e : Sym2 V) :
    e ∈ (ofFnCycle f h close).edges ↔
      e = s(f (Fin.last n), f 0) ∨
        ∃ i : Fin n, s(f i.castSucc, f i.succ) = e := by
  simp only [ofFnCycle_edges, List.mem_cons, List.mem_ofFn]

/-- A closing edge not already used by the enumerated Hamiltonian path
creates a Hamiltonian cycle in Mathlib's standard sense. -/
theorem ofFnCycle_isHamiltonianCycle_of_not_mem [DecidableEq V] {n : ℕ}
    (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (close : G.Adj (f (Fin.last n)) (f 0)) (hf : Function.Bijective f)
    (hclose : s(f (Fin.last n), f 0) ∉ (ofFnWalk f h).edges) :
    (ofFnCycle f h close).IsHamiltonianCycle := by
  refine ⟨?_, ?_⟩
  · exact (Walk.cons_isCycle_iff _ close).mpr ⟨ofFnWalk_isPath f h hf.injective, hclose⟩
  · simpa [ofFnCycle, Walk.IsHamiltonian] using ofFnWalk_isHamiltonian f h hf

/-- With at least three distinct vertices, the closing edge is different
from every consecutive edge of the linear enumeration. -/
theorem closing_edge_not_mem {n : ℕ} (hn : 2 ≤ n) (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (hf : Function.Injective f) :
    s(f (Fin.last n), f 0) ∉ (ofFnWalk f h).edges := by
  rw [mem_ofFnWalk_edges]
  rintro ⟨i, hi⟩
  rcases Sym2.eq_iff.mp hi with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · have hval := congrArg Fin.val (hf h₀)
    have hiLt := i.isLt
    simp only [Fin.coe_castSucc, Fin.val_last] at hval
    omega
  · have hval₀ := congrArg Fin.val (hf h₀)
    have hval₁ := congrArg Fin.val (hf h₁)
    simp only [Fin.coe_castSucc, Fin.val_zero] at hval₀
    simp only [Fin.val_succ, Fin.val_last] at hval₁
    omega

/-- A bijective enumeration of at least three vertices, with consecutive
adjacency and the closing adjacency, gives a Hamiltonian cycle. -/
theorem ofFnCycle_isHamiltonianCycle [DecidableEq V] {n : ℕ} (hn : 2 ≤ n)
    (f : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ))
    (close : G.Adj (f (Fin.last n)) (f 0)) (hf : Function.Bijective f) :
    (ofFnCycle f h close).IsHamiltonianCycle :=
  ofFnCycle_isHamiltonianCycle_of_not_mem f h close hf
    (closing_edge_not_mem hn f h hf.injective)

/-- The next index in a cyclic enumeration, including its last-to-first step. -/
def cyclicNext {N : ℕ} (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (by have := i.isLt; omega)⟩

@[simp]
theorem cyclicNext_castSucc {n : ℕ} (i : Fin n) :
    cyclicNext i.castSucc = i.succ := by
  apply Fin.ext
  change (i.val + 1) % (n + 1) = i.val + 1
  apply Nat.mod_eq_of_lt
  have := i.isLt
  omega

@[simp]
theorem cyclicNext_last (n : ℕ) : cyclicNext (Fin.last n) = 0 := by
  apply Fin.ext
  simp [cyclicNext]

/-- Construct a closed traversal directly from a cyclically adjacent enumeration.
It starts at the last entry, takes the last-to-first edge, then traverses the
entries in their linear order. -/
def ofCyclicEnumeration : {N : ℕ} → (hN : 3 ≤ N) → (f : Fin N → V) →
    (∀ i : Fin N, G.Adj (f i) (f (cyclicNext i))) →
    G.Walk (f ⟨N - 1, by omega⟩) (f ⟨N - 1, by omega⟩)
  | 0, hN, _, _ => by omega
  | n + 1, _, f, h => ofFnCycle f
      (fun i => by simpa only [cyclicNext_castSucc] using h i.castSucc)
      (by simpa only [cyclicNext_last] using h (Fin.last n))

@[simp]
theorem ofCyclicEnumeration_support {N : ℕ} (hN : 3 ≤ N) (f : Fin N → V)
    (h : ∀ i : Fin N, G.Adj (f i) (f (cyclicNext i))) :
    (ofCyclicEnumeration hN f h).support = f ⟨N - 1, by omega⟩ :: List.ofFn f := by
  cases N with
  | zero => omega
  | succ n => simp [ofCyclicEnumeration, Fin.last]

/-- Every edge, including the closing edge, is exactly one cyclic consecutive
pair in the supplied enumeration. -/
@[simp]
theorem mem_ofCyclicEnumeration_edges {N : ℕ} (hN : 3 ≤ N) (f : Fin N → V)
    (h : ∀ i : Fin N, G.Adj (f i) (f (cyclicNext i))) (e : Sym2 V) :
    e ∈ (ofCyclicEnumeration hN f h).edges ↔
      ∃ i : Fin N, s(f i, f (cyclicNext i)) = e := by
  cases N with
  | zero => omega
  | succ n =>
    rw [ofCyclicEnumeration, mem_ofFnCycle_edges]
    constructor
    · rintro (hclose | ⟨i, hi⟩)
      · exact ⟨Fin.last n, by simpa only [cyclicNext_last] using hclose.symm⟩
      · exact ⟨i.castSucc, by simpa only [cyclicNext_castSucc] using hi⟩
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        left
        simpa only [cyclicNext_last] using hi.symm
      · intro hi
        right
        exact ⟨j, by simpa only [cyclicNext_castSucc] using hi⟩

/-- A bijective cyclic enumeration of at least three vertices constructs a
standard Hamiltonian cycle; Hamiltonicity is a conclusion, never an input. -/
theorem ofCyclicEnumeration_isHamiltonianCycle [DecidableEq V] {N : ℕ}
    (hN : 3 ≤ N) (f : Fin N → V)
    (h : ∀ i : Fin N, G.Adj (f i) (f (cyclicNext i))) (hf : Function.Bijective f) :
    (ofCyclicEnumeration hN f h).IsHamiltonianCycle := by
  cases N with
  | zero => omega
  | succ n =>
    exact ofFnCycle_isHamiltonianCycle (by omega) f
      (fun i => by simpa only [cyclicNext_castSucc] using h i.castSucc)
      (by simpa only [cyclicNext_last] using h (Fin.last n)) hf

#print axioms ofFnWalk_support
#print axioms ofFnWalk_edges
#print axioms ofFnWalk_isHamiltonian
#print axioms ofFnCycle_isHamiltonianCycle
#print axioms mem_ofCyclicEnumeration_edges
#print axioms ofCyclicEnumeration_isHamiltonianCycle

end EnumeratedWalk
