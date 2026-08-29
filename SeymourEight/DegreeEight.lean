import SeymourEight.Reduction

set_option linter.style.header false

/-!
# Consequences at a degree-eight root

This file specializes the one-vertex reduction at `h = 7`.  It proves that,
in a counterexample, a vertex of outdegree eight has six or seven strict
second outneighbors.
-/

namespace Digraph

variable {V : Type*} (G : Digraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A non-Seymour vertex has strictly fewer second outneighbors than first outneighbors. -/
theorem secondOutdegree_lt_outdegree_of_not_seymour {v : V}
    (hv : ¬G.IsSeymourVertex v) :
    G.secondOutdegree v < G.outdegree v := by
  unfold IsSeymourVertex at hv
  omega

/-- A degree-eight vertex in a counterexample has at most seven second outneighbors. -/
theorem secondOutdegree_le_seven {v : V} (hDegree : G.outdegree v = 8)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    G.secondOutdegree v ≤ 7 := by
  have hv : ¬G.IsSeymourVertex v := by
    intro h
    exact hNoSeymour ⟨v, h⟩
  have hlt := secondOutdegree_lt_outdegree_of_not_seymour G hv
  omega

/--
The Hall-type lower bound at a degree-eight root: assuming the degree-seven
Seymour bound, a degree-eight vertex in a counterexample has at least six
strict second outneighbors.
-/
theorem six_le_secondOutdegree {s : V} (hBound : LimitedSeymourConjectureOn V 7)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree s = 8) :
    6 ≤ G.secondOutdegree s := by
  let A := G.outNeighborFinset s
  have hAcard : A.card = 8 := hDegree
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, haA⟩ := hAne
  let S := A.erase a
  have hScard : S.card = 7 := by
    simp only [S, Finset.card_erase_of_mem haA, hAcard]
  have hSsubset : (S : Set V) ⊆ G.outNeighborSet s := by
    intro u huS
    have huA : u ∈ A := Finset.mem_of_mem_erase huS
    simpa only [A, mem_outNeighborFinset, mem_outNeighborSet] using huA
  have hExpand := oneVertexReduction G hBound hG hNoSeymour hSsubset (by omega)
  have hTargetSubset :
      G.outNeighborFinsetOf S \ (S ∪ {s}) ⊆
        {a} ∪ G.secondOutNeighborFinset s := by
    intro w hw
    have hwOut : w ∈ G.outNeighborFinsetOf S := (Finset.mem_sdiff.mp hw).1
    have hwOutside : w ∉ S ∪ {s} := (Finset.mem_sdiff.mp hw).2
    have hwNotS : w ∉ S := by
      intro hwS
      exact hwOutside (Finset.mem_union_left _ hwS)
    have hws : w ≠ s := by
      intro h
      subst w
      exact hwOutside (by simp)
    have hwOut' : ∃ u ∈ S, G.Adj u w := by
      simpa [outNeighborFinsetOf] using hwOut
    obtain ⟨u, huS, huw⟩ := hwOut'
    by_cases hwa : w = a
    · exact Finset.mem_union_left _ (by simp [hwa])
    · apply Finset.mem_union_right
      rw [mem_secondOutNeighborFinset, mem_secondOutNeighborSet]
      refine ⟨⟨u, ?_, huw⟩, ?_, hws⟩
      · have huA : u ∈ A := Finset.mem_of_mem_erase huS
        simpa only [A, mem_outNeighborFinset] using huA
      · intro hsw
        have hwA : w ∈ A := by
          simpa only [A, mem_outNeighborFinset] using hsw
        have hwS : w ∈ S := by
          simp [S, hwA, hwa]
        exact hwNotS hwS
  have hTargetCard :
      (G.outNeighborFinsetOf S \ (S ∪ {s})).card ≤
        1 + G.secondOutdegree s := by
    calc
      (G.outNeighborFinsetOf S \ (S ∪ {s})).card ≤
          ({a} ∪ G.secondOutNeighborFinset s).card :=
        Finset.card_le_card hTargetSubset
      _ ≤ ({a} : Finset V).card + (G.secondOutNeighborFinset s).card :=
        Finset.card_union_le _ _
      _ = 1 + G.secondOutdegree s := by simp [secondOutdegree]
  omega

/-- A degree-eight root in a counterexample has six or seven strict second outneighbors. -/
theorem secondOutdegree_eq_six_or_seven {s : V} (hBound : LimitedSeymourConjectureOn V 7)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree s = 8) :
    G.secondOutdegree s = 6 ∨ G.secondOutdegree s = 7 := by
  have hlo := six_le_secondOutdegree G hBound hG hNoSeymour hDegree
  have hhi := secondOutdegree_le_seven G hDegree hNoSeymour
  omega

end Finite

end Digraph
