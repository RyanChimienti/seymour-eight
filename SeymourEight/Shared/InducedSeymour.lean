import SeymourEight.Reduction
import SeymourEight.Shared.ArcCounting
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

namespace SeymourEight.Shared

open Digraph

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Strict second neighbors of `v` inside the subgraph induced by `S`. -/
def inducedSecondFinset (S : Finset V) (v : V) : Finset V :=
  S.filter fun w ↦ w ≠ v ∧ ¬G.Adj v w ∧ ∃ m ∈ S, G.Adj v m ∧ G.Adj m w

/-- A fixed-type form of applying the degree-seven theorem to an induced
subgraph.  Outside vertices are made into a transitive tournament which
dominates `S`; they have positive outdegree and no strict second neighbors,
so the Seymour witness supplied by `hBound` must belong to `S`. -/
theorem inducedSeymour_of_low_degree
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (S : Finset V) (hS : S.Nonempty)
    (hLow : ∃ v ∈ S, directCount G S v ≤ 7) :
    ∃ v ∈ S, directCount G S v ≤ (inducedSecondFinset G S v).card := by
  classical
  let rank : V → Nat := fun v ↦ (Fintype.equivFin V v).val
  let D : Digraph V := ⟨fun x y ↦
    if x ∈ S then y ∈ S ∧ G.Adj x y
    else if y ∈ S then True else rank x < rank y⟩
  let : DecidableRel D.Adj := Classical.decRel _
  have hDOriented : D.IsOriented := by
    constructor
    · intro x
      by_cases hx : x ∈ S
      · simpa [D, hx] using hG.1 x
      · simp [D, hx]
    · intro x y hxy hyx
      by_cases hx : x ∈ S
      · have hy : y ∈ S := (by simpa [D, hx] using hxy : y ∈ S ∧ G.Adj x y).1
        exact hG.2 (by simpa [D, hx, hy] using hxy)
          (by simpa [D, hx, hy] using hyx)
      · by_cases hy : y ∈ S
        · simp [D, hx, hy] at hyx
        · have hlt : rank x < rank y := by simpa [D, hx, hy] using hxy
          have hgt : rank y < rank x := by simpa [D, hx, hy] using hyx
          omega
  obtain ⟨low, hlowS, hlow⟩ := hLow
  have hLowDegree : D.outdegree low ≤ 7 := by
    have hEq : D.outNeighborFinset low = S.filter (G.Adj low) := by
      ext w
      simp [Digraph.mem_outNeighborFinset, D, hlowS]
    change (D.outNeighborFinset low).card ≤ 7
    rw [hEq]
    exact hlow
  obtain ⟨v, hvSeymour⟩ := hBound D hDOriented ⟨low, hLowDegree⟩
  have hvS : v ∈ S := by
    by_contra hv
    have hvOutPos : 1 ≤ D.outdegree v := by
      obtain ⟨s, hs⟩ := hS
      have hvs : D.Adj v s := by simp [D, hv, hs]
      have hsMem : s ∈ D.outNeighborFinset v :=
        (Digraph.mem_outNeighborFinset (G := D)).mpr hvs
      exact (Finset.one_le_card.mpr ⟨s, hsMem⟩)
    have hSecondEmpty : D.secondOutNeighborFinset v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet] at hw
      rcases hw with ⟨⟨m, hvm, hmw⟩, hNot, _⟩
      by_cases hm : m ∈ S
      · have hwS : w ∈ S := (by simpa [D, hm] using hmw : w ∈ S ∧ G.Adj m w).1
        exact hNot (by simp [D, hv, hwS])
      · by_cases hwS : w ∈ S
        · exact hNot (by simp [D, hv, hwS])
        · have hvm' : rank v < rank m := by simpa [D, hv, hm] using hvm
          have hmw' : rank m < rank w := by simpa [D, hm, hwS] using hmw
          exact hNot (by simp [D, hv, hwS]; omega)
    unfold Digraph.IsSeymourVertex Digraph.secondOutdegree at hvSeymour
    rw [hSecondEmpty] at hvSeymour
    simp only [Finset.card_empty] at hvSeymour
    omega
  refine ⟨v, hvS, ?_⟩
  have hOutEq : D.outNeighborFinset v = S.filter (G.Adj v) := by
    ext w
    simp [Digraph.mem_outNeighborFinset, D, hvS]
  have hSecondEq : D.secondOutNeighborFinset v = inducedSecondFinset G S v := by
    ext w
    simp only [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet, inducedSecondFinset, Finset.mem_filter]
    constructor
    · rintro ⟨⟨m, hvm, hmw⟩, hNot, hwv⟩
      have hmS : m ∈ S := (by simpa [D, hvS] using hvm : m ∈ S ∧ G.Adj v m).1
      have hwS : w ∈ S := (by simpa [D, hmS] using hmw : w ∈ S ∧ G.Adj m w).1
      exact ⟨hwS, hwv, by simpa [D, hvS, hwS] using hNot,
        m, hmS, by simpa [D, hvS, hmS] using hvm,
        by simpa [D, hmS, hwS] using hmw⟩
    · rintro ⟨hwS, hwv, hNot, m, hmS, hvm, hmw⟩
      exact ⟨⟨m, by simpa [D, hvS, hmS] using hvm,
        by simpa [D, hmS, hwS] using hmw⟩,
        by simpa [D, hvS, hwS] using hNot, hwv⟩
  unfold Digraph.IsSeymourVertex Digraph.outdegree Digraph.secondOutdegree at hvSeymour
  rw [hOutEq, hSecondEq] at hvSeymour
  exact hvSeymour

/-- Every nonempty induced subgraph on at most fifteen vertices has an
internal vertex of outdegree at most seven, by orientation and averaging. -/
theorem inducedSeymour_of_card_le_fifteen
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (S : Finset V) (hS : S.Nonempty) (hCard : S.card ≤ 15) :
    ∃ v ∈ S, directCount G S v ≤ (inducedSecondFinset G S v).card := by
  apply inducedSeymour_of_low_degree G hBound hG S hS
  by_contra hn
  push Not at hn
  have hLower : 8 * S.card ≤ edgeCount G S S := by
    unfold edgeCount
    calc
      8 * S.card = ∑ _v ∈ S, 8 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ S, directCount G S v := by
        apply Finset.sum_le_sum
        intro v hv
        have hvLow := hn v hv
        omega
  have hUpper := internal_edgeCount_le_choose_two G S hG
  have hPos : 1 ≤ S.card := Finset.one_le_card.mpr hS
  interval_cases h : S.card <;> simp [Nat.choose] at hLower hUpper <;> omega

end SeymourEight.Shared
