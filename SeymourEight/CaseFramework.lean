import SeymourEight.LocalConfiguration

set_option linter.style.header false

/-!
# Shared framework for the five local cases

This module contains only the pivot convention and the propositions naming the
five `(|B|, k)` leaves.  Individual case developments import this shared
interface, and the global theorem imports their proved implementations.
-/

namespace SeymourEight

/--
The pivot convention used in the local case tree: `a1` minimizes its number
of outneighbors in `A`, and among tied vertices minimizes its number of
outneighbors in `B`.
-/
def IsMinimalPivot {V : Type*} (G : Digraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (C : G.LocalConfiguration) : Prop :=
  ∀ a ∈ C.A,
    C.k ≤ (C.A.filter (G.Adj a)).card ∧
      ((C.A.filter (G.Adj a)).card = C.k →
        C.r ≤ (C.B.filter (G.Adj a)).card)

/-- A single leaf of the local case tree, parameterized by `(|B|, k)`. -/
def LocalCase.{u} (b k : Nat) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V],
    Digraph.LimitedSeymourConjectureOn V 7 →
    ∀ (G : Digraph V) [DecidableRel G.Adj] (C : G.LocalConfiguration),
      G.IsOriented →
      (∀ v, 8 ≤ G.outdegree v) →
      G.outdegree C.s = 8 →
      IsMinimalPivot G C →
      C.B.card = b →
      C.k = k →
      G.HasSeymourVertex

/-- The `(|B|, k) = (6, 2)` leaf. -/
def BSixKTwoCase.{u} : Prop := LocalCase.{u} 6 2

/-- The `(|B|, k) = (6, 3)` leaf. -/
def BSixKThreeCase.{u} : Prop := LocalCase.{u} 6 3

/-- The `(|B|, k) = (7, 1)` leaf. -/
def BSevenKOneCase.{u} : Prop := LocalCase.{u} 7 1

/-- The `(|B|, k) = (7, 2)` leaf. -/
def BSevenKTwoCase.{u} : Prop := LocalCase.{u} 7 2

/-- The `(|B|, k) = (7, 3)` leaf. -/
def BSevenKThreeCase.{u} : Prop := LocalCase.{u} 7 3

end SeymourEight
