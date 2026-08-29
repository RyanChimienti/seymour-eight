import Mathlib.Combinatorics.Digraph.Basic

set_option linter.style.header false

/-! This file supplies definitions on top of MathLib's Digraph. -/

namespace Digraph

variable {V : Type*} (G : Digraph V)

/-- The set of vertices reached by one outgoing arc from `v`. -/
def outNeighborSet (v : V) : Set V :=
  {w | G.Adj v w}

@[simp]
theorem mem_outNeighborSet {v w : V} :
    w ∈ G.outNeighborSet v ↔ G.Adj v w :=
  Iff.rfl

/-- The union of the outneighborhoods of all vertices in `S`. -/
def outNeighborSetOf (S : Set V) : Set V :=
  {w | ∃ v ∈ S, G.Adj v w}

@[simp]
theorem mem_outNeighborSetOf {S : Set V} {w : V} :
    w ∈ G.outNeighborSetOf S ↔ ∃ v ∈ S, G.Adj v w :=
  Iff.rfl

/--
The strict second outneighborhood of `v`: vertices reached by a directed
two-step walk, excluding `v` itself and its direct outneighbors.
-/
def secondOutNeighborSet (v : V) : Set V :=
  G.outNeighborSetOf (G.outNeighborSet v) \ (G.outNeighborSet v ∪ {v})

@[simp]
theorem mem_secondOutNeighborSet {v w : V} :
    w ∈ G.secondOutNeighborSet v ↔
      (∃ u, G.Adj v u ∧ G.Adj u w) ∧ ¬G.Adj v w ∧ w ≠ v := by
  simp only [secondOutNeighborSet, Set.mem_sdiff, mem_outNeighborSetOf,
    mem_outNeighborSet, Set.mem_union, Set.mem_singleton_iff]
  aesop

/-- A loopless digraph has no vertex pointing to itself. -/
def IsLoopless : Prop :=
  ∀ v, ¬G.Adj v v

/-- An oriented graph is a digraph with no loops and no pair of oppositely directed arcs. -/
def IsOriented : Prop :=
  G.IsLoopless ∧ ∀ ⦃u v⦄, G.Adj u v → ¬G.Adj v u

section Finite

variable [Fintype V] [DecidableRel G.Adj]

/-- The finite first outneighborhood of `v`. -/
def outNeighborFinset (v : V) : Finset V :=
  Finset.univ.filter (G.Adj v)

@[simp]
theorem mem_outNeighborFinset {v w : V} :
    w ∈ G.outNeighborFinset v ↔ G.Adj v w := by
  simp [outNeighborFinset]

variable [DecidableEq V]

/-- The finite union of the outneighborhoods of all vertices in `S`. -/
def outNeighborFinsetOf (S : Finset V) : Finset V :=
  Finset.univ.filter fun w ↦ ∃ v ∈ S, G.Adj v w

omit [DecidableEq V] in
@[simp]
theorem mem_outNeighborFinsetOf {S : Finset V} {w : V} :
    w ∈ G.outNeighborFinsetOf S ↔ ∃ v ∈ S, G.Adj v w := by
  simp [outNeighborFinsetOf]

omit [DecidableEq V] in
@[simp]
theorem coe_outNeighborFinsetOf (S : Finset V) :
    (G.outNeighborFinsetOf S : Set V) = G.outNeighborSetOf S := by
  ext
  simp

/-- The finite strict second outneighborhood of `v`. -/
def secondOutNeighborFinset (v : V) : Finset V :=
  Finset.univ.filter fun w ↦
    (∃ u ∈ (Finset.univ : Finset V), G.Adj v u ∧ G.Adj u w) ∧
      ¬G.Adj v w ∧ w ≠ v

@[simp]
theorem mem_secondOutNeighborFinset {v w : V} :
    w ∈ G.secondOutNeighborFinset v ↔ w ∈ G.secondOutNeighborSet v := by
  simp [secondOutNeighborFinset]

omit [DecidableEq V] in
@[simp]
theorem coe_outNeighborFinset (v : V) :
    (G.outNeighborFinset v : Set V) = G.outNeighborSet v := by
  ext
  simp

@[simp]
theorem coe_secondOutNeighborFinset (v : V) :
    (G.secondOutNeighborFinset v : Set V) = G.secondOutNeighborSet v := by
  ext
  simp

/-- The outdegree of `v`. -/
def outdegree (v : V) : ℕ :=
  (G.outNeighborFinset v).card

/-- The cardinality of the strict second outneighborhood of `v`. -/
def secondOutdegree (v : V) : ℕ :=
  (G.secondOutNeighborFinset v).card

/-- A vertex is Seymour when its second outneighborhood is at least as large as its first. -/
def IsSeymourVertex (v : V) : Prop :=
  G.outdegree v ≤ G.secondOutdegree v

/-- The digraph has a Seymour vertex. -/
def HasSeymourVertex : Prop :=
  ∃ v, G.IsSeymourVertex v

/-- The digraph has a vertex whose outdegree is at most `h`. -/
def HasVertexWithOutdegreeAtMost (h : ℕ) : Prop :=
  ∃ v, G.outdegree v ≤ h

end Finite

/--
The Seymour conjecture for graphs having a vertex with outdegree at most `h`,
for fixed vertex type `V`.
-/
def LimitedSeymourConjectureOn (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) : Prop :=
  ∀ (G : Digraph V) [DecidableRel G.Adj],
    G.IsOriented → G.HasVertexWithOutdegreeAtMost h → G.HasSeymourVertex

/-- The Seymour conjecture for graphs having a vertex with outdegree at most `h`. -/
def LimitedSeymourConjecture.{u} (h : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V], LimitedSeymourConjectureOn V h

end Digraph
