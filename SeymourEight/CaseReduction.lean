import SeymourEight.DegreeEight
import SeymourEight.CaseFramework
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option linter.style.header false

/-!
# Reduction to the five local cases

This file constructs the lexicographically minimal pivot, proves the averaging
bound `k ≤ 3`, and reduces the degree-eight conjecture to the five local
`(|B|, k)` cases exposed by `CaseFramework`.
-/

namespace SeymourEight

section CaseReduction

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every outneighbor of the pivot lies in its `A`-part or its `B`-part. -/
private theorem outNeighborFinset_pivot_eq (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    G.outNeighborFinset C.a1 = C.A1 ∪ C.P := by
  ext v
  simp only [Digraph.mem_outNeighborFinset, Finset.mem_union,
    Digraph.LocalConfiguration.A1, Digraph.LocalConfiguration.P,
    Finset.mem_filter]
  constructor
  · intro ha1v
    by_cases hvA : v ∈ C.A
    · exact Or.inl ⟨hvA, ha1v⟩
    · right
      refine ⟨?_, ha1v⟩
      change v ∈ G.secondOutNeighborFinset C.s
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      have hsa1 : G.Adj C.s C.a1 :=
        (Digraph.mem_outNeighborFinset (G := G)).mp
          C.a1_mem_root_outNeighbors
      refine ⟨⟨C.a1, hsa1, ha1v⟩, ?_, ?_⟩
      · intro hsv
        exact hvA ((Digraph.mem_outNeighborFinset (G := G)).mpr hsv)
      · intro hvs
        subst v
        exact hG.2 hsa1 ha1v
  · rintro (⟨_hvA, ha1v⟩ | ⟨_hvB, ha1v⟩) <;> exact ha1v

/-- The pivot's complete outdegree is `k + r`. -/
private theorem outdegree_pivot_eq_k_add_r (C : G.LocalConfiguration)
    (hG : G.IsOriented) :
    G.outdegree C.a1 = C.k + C.r := by
  have hDisjoint : Disjoint C.A1 C.P := by
    rw [Finset.disjoint_left]
    intro v hvA1 hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
        (Digraph.LocalConfiguration.A1_subset_A (G := G) C hvA1)
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  unfold Digraph.outdegree
  rw [outNeighborFinset_pivot_eq G C hG,
    Finset.card_union_of_disjoint hDisjoint]
  rfl

/-- A nonempty root neighborhood has a pivot satisfying the tie-breaking convention. -/
private theorem exists_minimalPivot (s : V) (hDegree : G.outdegree s = 8) :
    ∃ C : G.LocalConfiguration, C.s = s ∧ IsMinimalPivot G C := by
  let A := G.outNeighborFinset s
  have hACard : A.card = 8 := hDegree
  have hANonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a0, ha0A, ha0Min⟩ := A.exists_min_image
    (fun a ↦ (A.filter (G.Adj a)).card) hANonempty
  let M := A.filter fun a ↦
    (A.filter (G.Adj a)).card = (A.filter (G.Adj a0)).card
  have hMNonempty : M.Nonempty := by
    refine ⟨a0, ?_⟩
    simp [M, ha0A]
  obtain ⟨a1, ha1M, ha1Min⟩ := M.exists_min_image
    (fun a ↦ ((G.secondOutNeighborFinset s).filter (G.Adj a)).card)
    hMNonempty
  have ha1A : a1 ∈ A := (Finset.mem_filter.mp ha1M).1
  let C : G.LocalConfiguration :=
    { s := s
      a1 := a1
      a1_mem_root_outNeighbors := ha1A }
  refine ⟨C, rfl, ?_⟩
  intro a haA
  have haA' : a ∈ A := by simpa [C, Digraph.LocalConfiguration.A, A] using haA
  have ha1Internal :
      (A.filter (G.Adj a1)).card = (A.filter (G.Adj a0)).card :=
    (Finset.mem_filter.mp ha1M).2
  constructor
  · simpa [C, Digraph.LocalConfiguration.k, Digraph.LocalConfiguration.A1,
      Digraph.LocalConfiguration.A, A, ha1Internal] using ha0Min a haA'
  · intro haTie
    have haTie' :
        (A.filter (G.Adj a)).card = (A.filter (G.Adj a0)).card := by
      simpa [C, Digraph.LocalConfiguration.k, Digraph.LocalConfiguration.A1,
        Digraph.LocalConfiguration.A, A, ha1Internal] using haTie
    have haM : a ∈ M := Finset.mem_filter.mpr ⟨haA', haTie'⟩
    simpa [C, Digraph.LocalConfiguration.r, Digraph.LocalConfiguration.P,
      Digraph.LocalConfiguration.B, A] using ha1Min a haM

/-- The averaging step on the eight-vertex oriented graph induced by `A`. -/
private theorem minimalPivot_k_le_three (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C) :
    C.k ≤ 3 := by
  let A := C.A
  have hACard : A.card = 8 := hRootDegree
  have hIncidentLe : ∀ v ∈ A,
      (A.filter (G.Adj v)).card + (A.filter fun u ↦ G.Adj u v).card ≤ 7 := by
    intro v hvA
    have hDisjoint :
        Disjoint (A.filter (G.Adj v)) (A.filter fun u ↦ G.Adj u v) := by
      rw [Finset.disjoint_left]
      intro u huOut huIn
      exact hG.2 (Finset.mem_filter.mp huOut).2
        (Finset.mem_filter.mp huIn).2
    have hSubset :
        A.filter (G.Adj v) ∪ (A.filter fun u ↦ G.Adj u v) ⊆ A.erase v := by
      intro u hu
      apply Finset.mem_erase.mpr
      rcases Finset.mem_union.mp hu with huOut | huIn
      · refine ⟨?_, (Finset.mem_filter.mp huOut).1⟩
        intro huv
        subst u
        exact hG.1 v (Finset.mem_filter.mp huOut).2
      · refine ⟨?_, (Finset.mem_filter.mp huIn).1⟩
        intro huv
        subst u
        exact hG.1 v (Finset.mem_filter.mp huIn).2
    calc
      (A.filter (G.Adj v)).card + (A.filter fun u ↦ G.Adj u v).card =
          (A.filter (G.Adj v) ∪ (A.filter fun u ↦ G.Adj u v)).card := by
        rw [Finset.card_union_of_disjoint hDisjoint]
      _ ≤ (A.erase v).card := Finset.card_le_card hSubset
      _ = 7 := by rw [Finset.card_erase_of_mem hvA, hACard]
  have hOutIn :
      (∑ v ∈ A, (A.filter (G.Adj v)).card) =
        ∑ v ∈ A, (A.filter fun u ↦ G.Adj u v).card := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := A) (t := A) G.Adj)
  have hIncidentSum :
      (∑ v ∈ A,
        ((A.filter (G.Adj v)).card + (A.filter fun u ↦ G.Adj u v).card)) ≤ 56 := by
    calc
      (∑ v ∈ A,
        ((A.filter (G.Adj v)).card + (A.filter fun u ↦ G.Adj u v).card)) ≤
          ∑ _v ∈ A, 7 := Finset.sum_le_sum hIncidentLe
      _ = 56 := by simp [hACard]
  by_contra hk
  have hFour : 4 ≤ C.k := by omega
  have hOutLower : 32 ≤ ∑ v ∈ A, (A.filter (G.Adj v)).card := by
    calc
      32 = ∑ _v ∈ A, 4 := by simp [hACard]
      _ ≤ ∑ v ∈ A, (A.filter (G.Adj v)).card := by
        apply Finset.sum_le_sum
        intro v hvA
        exact hFour.trans (hPivot v (by simpa [A] using hvA)).1
  rw [Finset.sum_add_distrib, hOutIn] at hIncidentSum
  omega

end CaseReduction

/--
The complete global assembly.  Assuming the known degree-seven bound and the
five local leaves, every finite oriented graph of minimum outdegree at most
eight has a Seymour vertex.
-/
theorem degreeEightConjecture_of_subcases.{u}
    (hSeven : Digraph.LimitedSeymourConjecture.{u} 7)
    (hSixTwo : BSixKTwoCase.{u})
    (hSixThree : BSixKThreeCase.{u})
    (hSevenOne : BSevenKOneCase.{u})
    (hSevenTwo : BSevenKTwoCase.{u})
    (hSevenThree : BSevenKThreeCase.{u}) :
    Digraph.LimitedSeymourConjecture.{u} 8 := by
  intro V _instFintype _instDecidableEq G _instDecidableAdj hG hLowDegree
  by_cases hLowSeven : G.HasVertexWithOutdegreeAtMost 7
  · exact hSeven V G hG hLowSeven
  have hMin : ∀ v, 8 ≤ G.outdegree v := by
    intro v
    by_contra hv
    exact hLowSeven ⟨v, by omega⟩
  obtain ⟨s, hsAtMost⟩ := hLowDegree
  have hsDegree : G.outdegree s = 8 := Nat.le_antisymm hsAtMost (hMin s)
  by_contra hNoSeymour
  obtain ⟨C, hCs, hPivot⟩ := exists_minimalPivot G s hsDegree
  have hRootDegree : G.outdegree C.s = 8 := by simpa [hCs] using hsDegree
  have hB : C.B.card = 6 ∨ C.B.card = 7 := by
    have hSecond := Digraph.secondOutdegree_eq_six_or_seven G
      (hSeven V) hG hNoSeymour hRootDegree
    simpa [Digraph.LocalConfiguration.B, Digraph.secondOutdegree] using hSecond
  have hkUpper : C.k ≤ 3 :=
    minimalPivot_k_le_three G C hG hRootDegree hPivot
  have hDegreeBound : 8 ≤ C.k + C.B.card := by
    calc
      8 ≤ G.outdegree C.a1 := hMin C.a1
      _ = C.k + C.r := outdegree_pivot_eq_k_add_r G C hG
      _ ≤ C.k + C.B.card := Nat.add_le_add_left
        (Finset.card_le_card
          (Digraph.LocalConfiguration.P_subset_B (G := G) C)) C.k
  rcases hB with hBSix | hBSeven
  · have hk : C.k = 2 ∨ C.k = 3 := by omega
    rcases hk with hkTwo | hkThree
    · exact hNoSeymour
        (hSixTwo V (hSeven V) G C hG hMin hRootDegree hPivot hBSix hkTwo)
    · exact hNoSeymour
        (hSixThree V (hSeven V) G C hG hMin hRootDegree hPivot hBSix hkThree)
  · have hk : C.k = 1 ∨ C.k = 2 ∨ C.k = 3 := by omega
    rcases hk with hkOne | hkTwo | hkThree
    · exact hNoSeymour
        (hSevenOne V (hSeven V) G C hG hMin hRootDegree hPivot hBSeven hkOne)
    · exact hNoSeymour
        (hSevenTwo V (hSeven V) G C hG hMin hRootDegree hPivot hBSeven hkTwo)
    · exact hNoSeymour
        (hSevenThree V (hSeven V) G C hG hMin hRootDegree hPivot hBSeven hkThree)

end SeymourEight
