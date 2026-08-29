import SeymourEight.Cases.BSevenKOne.Counting
import SeymourEight.Reduction

set_option linter.style.header false

/-!
# The tight epsilon-one row `(x,z)=(1,5)`

This row collapses without a finite certificate.  If `u` and `x` are the
unique vertices of `A1` and `X`, minimality makes `u` point to `x` and every
vertex of `P`.  One-arc deletion at `a1 → u` then forces a `P → x` arc.
Minimality at `x` consequently forces at least two `A`-outneighbors, and those
two vertices together with the six external targets make `u` Seymour.
-/

namespace SeymourEight.BSevenKOne

open Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- After deleting `v → u`, every reached vertex other than `u` that lies
outside the retained first neighborhood is an original strict second
neighbor of `v`. -/
private theorem deletionExpansion_erase_subset_second {v u : V}
    (_hG : G.IsOriented) (_hu : G.Adj v u) :
    (G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase u) \
        ((G.outNeighborFinset v |>.erase u) ∪ {v})).erase u ⊆
      G.secondOutNeighborFinset v := by
  intro w hw
  have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
  have hwE := Finset.mem_of_mem_erase hw
  rcases Finset.mem_sdiff.mp hwE with ⟨hwReach, hwOutside⟩
  obtain ⟨middle, hmRetained, hmw⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
  have hvm : G.Adj v middle := by
    apply (Digraph.mem_outNeighborFinset (G := G)).mp
    exact Finset.mem_of_mem_erase hmRetained
  have hwNotRetained : w ∉ (G.outNeighborFinset v |>.erase u) := by
    intro hwRetained
    exact hwOutside (Finset.mem_union_left _ hwRetained)
  have hvw : ¬G.Adj v w := by
    intro hvw
    have hwFirst : w ∈ G.outNeighborFinset v :=
      (Digraph.mem_outNeighborFinset (G := G)).mpr hvw
    exact hwNotRetained (Finset.mem_erase.mpr ⟨hwu, hwFirst⟩)
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact hwOutside (Finset.mem_union_right _ (Finset.mem_singleton_self v))
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨middle, hvm, hmw⟩, hvw, hwv⟩

/-- The common `x=1` argument when the external contribution
`z + epsilon_s` is six.  This covers both the tight epsilon-one row
`(x,z)=(1,5)` and the tight epsilon-zero row `(x,z)=(1,6)`. -/
theorem tightXOneExternalSixImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (_hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 1) (hExternal : C.z + epsilonS G C = 6) : False := by
  classical
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hA1Card : C.A1.card = 1 := hk
  have hXCard : C.X.card = 1 := hx
  obtain ⟨u, hA1⟩ := Finset.card_eq_one.mp hA1Card
  obtain ⟨x, hX⟩ := Finset.card_eq_one.mp hXCard
  have huA1 : u ∈ C.A1 := by simp [hA1]
  have hxX : x ∈ C.X := by simp [hX]
  have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have hxA := Digraph.LocalConfiguration.X_subset_A (G := G) C hxX
  have huInternalSubset : C.A.filter (G.Adj u) ⊆ C.X := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwA, huw⟩
    by_cases hwA1 : w ∈ C.A1
    · have hwu : w = u := by simpa [hA1] using hwA1
      subst w
      exact (hG.1 u huw).elim
    · apply Finset.mem_inter.mpr
      constructor
      · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        exact ⟨u, Finset.mem_union_left C.P huA1, huw⟩
      · apply Finset.mem_sdiff.mpr
        refine ⟨hwA, ?_⟩
        intro hwParts
        rcases Finset.mem_union.mp hwParts with hwA1' | hwa1
        · exact hwA1 hwA1'
        · have hwa1Eq : w = C.a1 := Finset.mem_singleton.mp hwa1
          subst w
          have ha1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
          exact hG.2 ha1u huw
  have huInternalMin : 1 ≤ (C.A.filter (G.Adj u)).card := by
    simpa [hk] using (hPivot u huA).1
  have huInternalLe : (C.A.filter (G.Adj u)).card ≤ 1 := by
    calc
      _ ≤ C.X.card := Finset.card_le_card huInternalSubset
      _ = 1 := hXCard
  have huInternal : (C.A.filter (G.Adj u)).card = 1 := by omega
  have huInternalEqX : C.A.filter (G.Adj u) = C.X := by
    apply Finset.eq_of_subset_of_card_le huInternalSubset
    omega
  have hux : G.Adj u x := by
    have hxFilter : x ∈ C.A.filter (G.Adj u) := by
      rw [huInternalEqX]
      exact hxX
    exact (Finset.mem_filter.mp hxFilter).2
  have huBLower : 7 ≤ (C.B.filter (G.Adj u)).card := by
    have := (hPivot u huA).2 (by omega)
    simpa [r_eq_seven G C hG hMin hBCard hk] using this
  have huBFilter : C.B.filter (G.Adj u) = C.B := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    omega
  have huP : ∀ p ∈ C.P, G.Adj u p := by
    intro p hp
    have hpB : p ∈ C.B := Digraph.LocalConfiguration.P_subset_B (G := G) C hp
    have hpFilter : p ∈ C.B.filter (G.Adj u) := by
      rw [huBFilter]
      exact hpB
    exact (Finset.mem_filter.mp hpFilter).2
  have huH : u ∈ C.H := Finset.mem_union_left C.X huA1
  have huOut : G.outNeighborFinset u = C.X ∪ C.P := by
    ext w
    constructor
    · intro hw
      have hwCaptured := Shared.H_outgoingCaptured G C hG hPB u huH hw
      rcases Finset.mem_union.mp hwCaptured with hwA | hwP
      · exact Finset.mem_union_left C.P
          (huInternalSubset (Finset.mem_filter.mpr
            ⟨hwA, (Digraph.mem_outNeighborFinset (G := G)).mp hw⟩))
      · exact Finset.mem_union_right C.X hwP
    · intro hw
      rcases Finset.mem_union.mp hw with hwX | hwP
      · have hwEq : w = x := by simpa [hX] using hwX
        subst w
        exact (Digraph.mem_outNeighborFinset (G := G)).mpr hux
      · exact (Digraph.mem_outNeighborFinset (G := G)).mpr (huP w hwP)
  have huDegree : G.outdegree u = 8 := by
    unfold Digraph.outdegree
    rw [huOut, Finset.card_union_of_disjoint]
    · omega
    · exact Digraph.LocalConfiguration.disjoint_H_P (G := G) C |>.mono
        (fun _ hw ↦ Finset.mem_union_right C.A1 hw) (fun _ hw ↦ hw)
  let E := G.outNeighborFinsetOf (G.outNeighborFinset C.a1 |>.erase u) \
    ((G.outNeighborFinset C.a1 |>.erase u) ∪ {C.a1})
  have huNotE : u ∉ E := by
    intro huE
    rcases Finset.mem_sdiff.mp huE with ⟨huReach, _⟩
    obtain ⟨middle, hmRetained, hmu⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp huReach
    have hmOut : middle ∈ C.A1 ∪ C.P := by
      rw [← Shared.outNeighborFinset_a1_eq_A1_union_P G C hG]
      exact Finset.mem_of_mem_erase hmRetained
    rcases Finset.mem_union.mp hmOut with hmA1 | hmP
    · have hmuEq : middle = u := by simpa [hA1] using hmA1
      subst middle
      exact (Finset.mem_erase.mp hmRetained).1 rfl
    · exact hG.2 (huP middle hmP) hmu
  have hECard : 7 ≤ E.card := by
    simpa [E] using Digraph.oneArcDeletionExpansion G hBound hG hNoSeymour
      (outdegree_a1_eq_eight G C hG hMin hBCard hk)
      (Finset.mem_filter.mp huA1).2
  have hTCard : (G.secondOutNeighborFinset C.a1).card = 7 := by
    change G.secondOutdegree C.a1 = 7
    rw [Shared.secondOutdegree_a1_eq_x_add_z_add_epsilonS G C hG hPB,
      hx]
    omega
  have hESubset : E ⊆ G.secondOutNeighborFinset C.a1 := by
    intro w hw
    have hwu : w ≠ u := fun h ↦ huNotE (h ▸ hw)
    exact deletionExpansion_erase_subset_second G hG
      (Finset.mem_filter.mp huA1).2 (Finset.mem_erase.mpr ⟨hwu, hw⟩)
  have hEEquals : E = G.secondOutNeighborFinset C.a1 := by
    apply Finset.eq_of_subset_of_card_le hESubset
    omega
  have hxSecond : x ∈ G.secondOutNeighborFinset C.a1 := by
    rw [Shared.secondOutNeighborFinset_a1_eq G C hG hPB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hxX)
  have hxE : x ∈ E := by simpa [hEEquals] using hxSecond
  rcases Finset.mem_sdiff.mp hxE with ⟨hxReach, _⟩
  obtain ⟨p, hpRetained, hpx⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hxReach
  have hpOut : p ∈ C.A1 ∪ C.P := by
    rw [← Shared.outNeighborFinset_a1_eq_A1_union_P G C hG]
    exact Finset.mem_of_mem_erase hpRetained
  have hpP : p ∈ C.P := by
    rcases Finset.mem_union.mp hpOut with hpA1 | hpP
    · have hpEq : p = u := by simpa [hA1] using hpA1
      subst p
      exact ((Finset.mem_erase.mp hpRetained).1 rfl).elim
    · exact hpP
  have hxInternalMin : 1 ≤ (C.A.filter (G.Adj x)).card := by
    simpa [hk] using (hPivot x hxA).1
  have hxInternal : 2 ≤ (C.A.filter (G.Adj x)).card := by
    by_contra hNot
    have hxInternalEq : (C.A.filter (G.Adj x)).card = 1 := by omega
    have hxBLower := (hPivot x hxA).2 (by omega)
    have hxBFilter : C.B.filter (G.Adj x) = C.B := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hBCard]
      simpa [r_eq_seven G C hG hMin hBCard hk] using hxBLower
    have hpB : p ∈ C.B := Digraph.LocalConfiguration.P_subset_B (G := G) C hpP
    have hxp : G.Adj x p := by
      have : p ∈ C.B.filter (G.Adj x) := by simpa [hxBFilter] using hpB
      exact (Finset.mem_filter.mp this).2
    exact hG.2 hpx hxp
  have hExternalCard : (externalTargets G C).card = 6 := by
    rw [card_externalTargets, hExternal]
  have hExternalSecond : externalTargets G C ⊆
      G.secondOutNeighborFinset u := by
    intro w hw
    have hwNotDirect : ¬G.Adj u w := by
      intro huw
      have hwOut : w ∈ C.X ∪ C.P := by
        rw [← huOut]
        exact (Digraph.mem_outNeighborFinset (G := G)).mpr huw
      rcases Finset.mem_union.mp hwOut with hwX | hwP
      · have hwA := Digraph.LocalConfiguration.X_subset_A (G := G) C hwX
        rcases Finset.mem_union.mp hw with hwZ | hwRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hwA))
        · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
          · have hws : w = C.s := by simpa [rootSecondFinset, hReach] using hwRoot
            subst w
            exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hwA
          · simp [rootSecondFinset, hReach] at hwRoot
      · have hwB := Digraph.LocalConfiguration.P_subset_B (G := G) C hwP
        rcases Finset.mem_union.mp hw with hwZ | hwRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
              (Finset.mem_union_right ({C.s} ∪ C.A) hwB)
        · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
          · have hws : w = C.s := by simpa [rootSecondFinset, hReach] using hwRoot
            subst w
            exact Digraph.LocalConfiguration.s_notMem_B (G := G) C hwB
          · simp [rootSecondFinset, hReach] at hwRoot
    have hwu : w ≠ u := by
      intro hwu
      subst w
      rcases Finset.mem_union.mp hw with huZ | huRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) huZ
            (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} huA))
      · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
        · have hus : u = C.s := by simpa [rootSecondFinset, hReach] using huRoot
          subst u
          exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 huA
        · simp [rootSecondFinset, hReach] at huRoot
    obtain ⟨middle, hmP, hmw⟩ : ∃ middle ∈ C.P, G.Adj middle w := by
      rcases Finset.mem_union.mp hw with hwZ | hwRoot
      · rcases Finset.mem_sdiff.mp hwZ with ⟨hwReach, _⟩
        exact (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
      · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
        · have hws : w = C.s := by simpa [rootSecondFinset, hReach] using hwRoot
          subst w
          exact hReach
        · simp [rootSecondFinset, hReach] at hwRoot
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨middle, huP middle hmP, hmw⟩, hwNotDirect, hwu⟩
  have hxASecond : C.A.filter (G.Adj x) ⊆
      G.secondOutNeighborFinset u := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwA, hxw⟩
    have huw : ¬G.Adj u w := by
      intro huw
      have hwX : w ∈ C.X := huInternalSubset (Finset.mem_filter.mpr ⟨hwA, huw⟩)
      have hwEq : w = x := by simpa [hX] using hwX
      subst w
      exact hG.1 x hxw
    have hwu : w ≠ u := by
      intro hwu
      subst w
      exact hG.2 hux hxw
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨x, hux, hxw⟩, huw, hwu⟩
  have hDisjoint : Disjoint (externalTargets G C) (C.A.filter (G.Adj x)) := by
    rw [Finset.disjoint_left]
    intro w hwExternal hwA
    have hwA' := (Finset.mem_filter.mp hwA).1
    rcases Finset.mem_union.mp hwExternal with hwZ | hwRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
          (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hwA'))
    · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
      · have hws : w = C.s := by simpa [rootSecondFinset, hReach] using hwRoot
        subst w
        exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hwA'
      · simp [rootSecondFinset, hReach] at hwRoot
  have hUnionSubset : externalTargets G C ∪ C.A.filter (G.Adj x) ⊆
      G.secondOutNeighborFinset u := Finset.union_subset hExternalSecond hxASecond
  have hSecondEight : 8 ≤ G.secondOutdegree u := by
    unfold Digraph.secondOutdegree
    have hCardLe := Finset.card_le_card hUnionSubset
    have hUnionCard :
        (externalTargets G C ∪ C.A.filter (G.Adj x)).card =
          6 + (C.A.filter (G.Adj x)).card := by
      rw [Finset.card_union_of_disjoint hDisjoint, hExternalCard]
    omega
  apply hNoSeymour
  exact ⟨u, by
    unfold Digraph.IsSeymourVertex
    omega⟩

/-- Complete tight `epsilon_s=1`, `(x,z)=(1,5)` row. -/
theorem tightEpsilonOneXOneImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 1)
    (hx : C.x = 1) (hz : C.z = 5) : False := by
  apply tightXOneExternalSixImpossible G hBound C hG hMin hNoSeymour
    hRootDegree hPivot hBCard hk hx
  omega

end SeymourEight.BSevenKOne
