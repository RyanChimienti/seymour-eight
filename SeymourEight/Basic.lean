import SeymourEight.LocalConfiguration
import Std.Tactic.BVDecide

set_option linter.style.header false

/-!
# Executable sanity checks

This file verifies the directed-triangle definitions and includes a minimal
finite contradiction checked by Lean's certificate-producing `bv_decide`
tactic.
-/

namespace SeymourEight

/-- The directed three-cycle `0 → 1 → 2 → 0`, using Mathlib's `Digraph`. -/
def directedTriangle : Digraph (Fin 3) :=
  Digraph.mk' fun u v ↦
    (u == 0 && v == 1) ||
    (u == 1 && v == 2) ||
    (u == 2 && v == 0)

instance : DecidableRel directedTriangle.Adj := by
  unfold directedTriangle
  infer_instance

example : directedTriangle.Adj 0 1 := by decide
example : directedTriangle.Adj 1 2 := by decide
example : directedTriangle.Adj 2 0 := by decide
example : ¬directedTriangle.Adj 1 0 := by decide

/-- The directed triangle has no loops. -/
theorem directedTriangle_loopless :
    ∀ v, ¬directedTriangle.Adj v v := by
  decide +kernel

/-- The directed triangle never contains both orientations of an edge. -/
theorem directedTriangle_no_antiparallel_edges :
    ∀ u v, directedTriangle.Adj u v → ¬directedTriangle.Adj v u := by
  decide +kernel

/-- The directed triangle is an oriented graph in the formal sense. -/
theorem directedTriangle_isOriented : directedTriangle.IsOriented := by
  unfold Digraph.IsOriented Digraph.IsLoopless
  decide +kernel

/-- Every vertex of the directed triangle has one first and one strict second outneighbor. -/
theorem directedTriangle_degrees :
    ∀ v, directedTriangle.outdegree v = 1 ∧
      directedTriangle.secondOutdegree v = 1 := by
  decide +kernel

/-- In particular, every vertex of the directed triangle is a Seymour vertex. -/
theorem directedTriangle_isSeymour :
    ∀ v, directedTriangle.IsSeymourVertex v := by
  unfold Digraph.IsSeymourVertex
  decide +kernel

/-- Choose `0` as the root and its unique outneighbor `1` as the pivot. -/
def directedTriangleConfiguration : directedTriangle.LocalConfiguration where
  s := 0
  a1 := 1
  a1_mem_root_outNeighbors := by decide

/--
An executable sanity check for every local set: for the directed triangle,
`A = {1}`, `B = P = {2}`, and all the remaining local sets are empty.
-/
theorem directedTriangle_local_sets :
    directedTriangleConfiguration.A = {1} ∧
      directedTriangleConfiguration.B = {2} ∧
      directedTriangleConfiguration.A1 = ∅ ∧
      directedTriangleConfiguration.P = {2} ∧
      directedTriangleConfiguration.Q = ∅ ∧
      directedTriangleConfiguration.X = ∅ ∧
      directedTriangleConfiguration.R = ∅ ∧
      directedTriangleConfiguration.Z = ∅ := by
  decide +kernel

/--
A minimal SAT/LRAT certificate check: the displayed Boolean constraints have
no satisfying assignment.
-/
theorem tiny_unsat_core (a b : Bool) :
    ¬(a = true ∧ b = true ∧ (a && b) = false) := by
  bv_decide

end SeymourEight
