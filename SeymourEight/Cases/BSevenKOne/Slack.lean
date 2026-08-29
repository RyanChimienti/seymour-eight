import SeymourEight.Cases.BSevenKOne.Counting
import SeymourEight.Reduction

set_option linter.style.header false

/-!
# The one-unit-slack rows

When `x + z + epsilon_s = 6`, the pivot `a1` has six strict second
neighbors.  Deleting any one of its eight outgoing arcs leaves seven first
neighbors, so the degree-seven theorem forces a sharp equality: the deleted
head is reached again and every original second neighbor still has a retained
predecessor.  The three possible values `x=1,2,3` then admit short graph
arguments; no finite certificate is needed.
-/

namespace SeymourEight.BSevenKOneSlack

open BSevenKOne BSevenKOneCounting Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Apart from the deleted head, every vertex reached after deleting one
outgoing arc was already a strict second neighbor. -/
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
    exact hwNotRetained (Finset.mem_erase.mpr
      ⟨hwu, (Digraph.mem_outNeighborFinset (G := G)).mpr hvw⟩)
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact hwOutside (Finset.mem_union_right _ (Finset.mem_singleton_self v))
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨middle, hvm, hmw⟩, hvw, hwv⟩

/-- With exactly six original second neighbors, the head of every deleted arc is
forced to be reached from another retained first neighbor. -/
theorem deletedHead_reached_of_secondDegree_six {v u : V}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree v = 8) (hSecond : G.secondOutdegree v = 6)
    (hu : G.Adj v u) :
    ∃ middle, G.Adj v middle ∧ G.Adj middle u ∧ middle ≠ u := by
  let E := G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase u) \
    ((G.outNeighborFinset v |>.erase u) ∪ {v})
  let T := G.secondOutNeighborFinset v
  have hECard : 7 ≤ E.card := by
    simpa [E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hu
  have hTCard : T.card = 6 := hSecond
  have hEraseSubset : E.erase u ⊆ T := by
    simpa [E, T] using deletionExpansion_erase_subset_second G hG hu
  have huE : u ∈ E := by
    by_contra hNot
    have hErase : E.erase u = E := Finset.erase_eq_of_notMem hNot
    have hLe := Finset.card_le_card hEraseSubset
    rw [hErase, hTCard] at hLe
    omega
  rcases Finset.mem_sdiff.mp huE with ⟨huReach, _⟩
  obtain ⟨middle, hmRetained, hmu⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp huReach
  exact ⟨middle,
    (Digraph.mem_outNeighborFinset (G := G)).mp
      (Finset.mem_of_mem_erase hmRetained),
    hmu, (Finset.mem_erase.mp hmRetained).1⟩

/-- Every original strict second neighbor has two distinct predecessors in the
original first neighborhood. -/
theorem two_first_predecessors_of_secondDegree_six {v w : V}
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (hG : G.IsOriented)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : G.outdegree v = 8) (hSecond : G.secondOutdegree v = 6)
    (hw : w ∈ G.secondOutNeighborFinset v) :
    ∃ p q, p ≠ q ∧ G.Adj v p ∧ G.Adj p w ∧ G.Adj v q ∧ G.Adj q w := by
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet] at hw
  rcases hw with ⟨⟨p, hvp, hpw⟩, hvw, hwv⟩
  let E := G.outNeighborFinsetOf (G.outNeighborFinset v |>.erase p) \
    ((G.outNeighborFinset v |>.erase p) ∪ {v})
  let T := G.secondOutNeighborFinset v
  have hECard : 7 ≤ E.card := by
    simpa [E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hvp
  have hTCard : T.card = 6 := hSecond
  have hEraseSubset : E.erase p ⊆ T := by
    simpa [E, T] using deletionExpansion_erase_subset_second G hG hvp
  have hEraseCard : 6 ≤ (E.erase p).card := by
    by_cases hpE : p ∈ E
    · have hCardEq := Finset.card_erase_add_one hpE
      omega
    · rw [Finset.erase_eq_of_notMem hpE]
      omega
  have hEraseEq : E.erase p = T := by
    apply Finset.eq_of_subset_of_card_le hEraseSubset
    rw [hTCard]
    exact hEraseCard
  have hwE : w ∈ E.erase p := by simpa [hEraseEq, T] using
    (show w ∈ G.secondOutNeighborFinset v from by
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨p, hvp, hpw⟩, hvw, hwv⟩)
  rcases Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hwE) with
    ⟨hwReach, _⟩
  obtain ⟨q, hqRetained, hqw⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
  have hvq : G.Adj v q := (Digraph.mem_outNeighborFinset (G := G)).mp
    (Finset.mem_of_mem_erase hqRetained)
  have hqp : q ≠ p := (Finset.mem_erase.mp hqRetained).1
  exact ⟨p, q, hqp.symm, hvp, hpw, hvq, hqw⟩

/-- In every slack row, `a1` has exactly six strict second neighbors. -/
theorem secondOutdegree_a1_eq_six (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hSlack : C.x + C.z + epsilonS G C = 6) :
    G.secondOutdegree C.a1 = 6 := by
  have hPB := p_eq_B G C hG hMin hBCard hk
  rw [secondOutdegree_a1_eq_x_add_z_add_epsilonS G C hG hPB]
  exact hSlack

/-- Pointwise degree accounting for a vertex of `H`. -/
theorem outdegree_H_eq_A_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (u : V) (hu : u ∈ C.H) :
    G.outdegree u = directCount G C.A u + directCount G C.P u := by
  have hCaptured := H_outgoingCaptured G C hG hPB u hu
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  have hEq : G.outNeighborFinset u = (C.A ∪ C.P).filter (G.Adj u) := by
    ext v
    simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro huv
      exact ⟨by simpa only [Finset.mem_union] using
        hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩
    · exact fun hv => hv.2
  rw [hEq, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter (p := G.Adj u) (q := G.Adj u) (by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP))

/-- The unique `A1` vertex can point inside `A` only toward `X`. -/
theorem AOne_internal_subset_X (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hk : C.k = 1) (u : V) (huA1 : u ∈ C.A1) :
    C.A.filter (G.Adj u) ⊆ C.X := by
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwA, huw⟩
  apply Finset.mem_inter.mpr
  constructor
  · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
    exact ⟨u, Finset.mem_union_left C.P huA1, huw⟩
  · apply Finset.mem_sdiff.mpr
    refine ⟨hwA, ?_⟩
    intro hwParts
    rcases Finset.mem_union.mp hwParts with hwA1 | hwa1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hk
      have hwu : w = u := by
        have hwEq : w = a := by simpa [ha] using hwA1
        have huEq : u = a := by simpa [ha] using huA1
        exact hwEq.trans huEq.symm
      subst w
      exact hG.1 u huw
    · have hwa1Eq : w = C.a1 := Finset.mem_singleton.mp hwa1
      subst w
      exact hG.2 (Finset.mem_filter.mp huA1).2 huw

/-- External targets are disjoint from the root outneighborhood `A`. -/
theorem disjoint_A_externalTargets (C : G.LocalConfiguration)
    (hG : G.IsOriented) : Disjoint C.A (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvA hvE
  rcases Finset.mem_union.mp hvE with hvZ | hvRoot
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
        (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA))
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
    · simp [rootSecondFinset, hReach] at hvRoot

/-- External targets are disjoint from `P`. -/
theorem disjoint_P_externalTargets (C : G.LocalConfiguration) :
    Disjoint C.P (externalTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvP hvE
  rcases Finset.mem_union.mp hvE with hvZ | hvRoot
  · exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
      subst v
      exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
    · simp [rootSecondFinset, hReach] at hvRoot

omit [Fintype V] in
/-- Arc counts add when the source is a disjoint union. -/
theorem edgeCount_source_union (S T U : Finset V) (hST : Disjoint S T) :
    edgeCount G (S ∪ T) U = edgeCount G S U + edgeCount G T U := by
  classical
  unfold edgeCount
  rw [Finset.sum_union hST]

omit [Fintype V] [DecidableEq V] in
/-- A row which attains the full target-set cardinality contains every arc. -/
theorem adj_of_directCount_eq_card (S : Finset V) (u v : V)
    (hCount : directCount G S u = S.card) (hv : v ∈ S) : G.Adj u v := by
  classical
  have hSubset : S.filter (G.Adj u) ⊆ S := Finset.filter_subset _ _
  have hEq : S.filter (G.Adj u) = S := by
    apply Finset.eq_of_subset_of_card_le hSubset
    simpa [directCount, CertificateBridge.internalFirstNeighbors] using
      hCount.symm.le
  have : v ∈ S.filter (G.Adj u) := by rw [hEq]; exact hv
  exact (Finset.mem_filter.mp this).2

/-- The slack row `x=1` is impossible by deletion saturation alone. -/
theorem xOneImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hSlack : C.x + C.z + epsilonS G C = 6)
    (hx : C.x = 1) : False := by
  classical
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hA1Card : C.A1.card = 1 := hk
  obtain ⟨u, hA1⟩ := Finset.card_eq_one.mp hA1Card
  have huA1 : u ∈ C.A1 := by simp [hA1]
  have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have ha1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
  obtain ⟨p, ha1p, hpu, hpuNe⟩ := deletedHead_reached_of_secondDegree_six
    G hBound hG hNoSeymour
      (outdegree_a1_eq_eight G C hG hMin hBCard hk)
      (secondOutdegree_a1_eq_six G C hG hMin hBCard hk hSlack) ha1u
  have hpParts : p ∈ C.A1 ∪ C.P := by
    rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
    exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1p
  have hpP : p ∈ C.P := by
    rcases Finset.mem_union.mp hpParts with hpA1 | hpP
    · have hpuEq : p = u := by simpa [hA1] using hpA1
      exact (hpuNe hpuEq).elim
    · exact hpP
  have huInternalSubset : C.A.filter (G.Adj u) ⊆ C.X := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwA, huw⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨u, Finset.mem_union_left C.P huA1, huw⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨hwA, ?_⟩
      intro hwParts
      rcases Finset.mem_union.mp hwParts with hwA1 | hwa1
      · have hwu : w = u := by simpa [hA1] using hwA1
        subst w
        exact hG.1 u huw
      · have hwa1Eq : w = C.a1 := Finset.mem_singleton.mp hwa1
        subst w
        exact hG.2 ha1u huw
  have huInternalMin : 1 ≤ (C.A.filter (G.Adj u)).card := by
    simpa [hk] using (hPivot u huA).1
  have huInternalLe : (C.A.filter (G.Adj u)).card ≤ 1 := by
    calc
      _ ≤ C.X.card := Finset.card_le_card huInternalSubset
      _ = 1 := hx
  have huInternal : (C.A.filter (G.Adj u)).card = 1 := by omega
  have huBLower := (hPivot u huA).2 (by
    simpa [hk] using huInternal)
  have hup : G.Adj u p := by
    have hBFilter : C.B.filter (G.Adj u) = C.B := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hBCard]
      simpa [r_eq_seven G C hG hMin hBCard hk] using huBLower
    have hpB : p ∈ C.B := by simpa [hPB] using hpP
    have hpFilter : p ∈ C.B.filter (G.Adj u) := by
      rw [hBFilter]
      exact hpB
    exact (Finset.mem_filter.mp hpFilter).2
  exact hG.2 hup hpu

/-- The slack row `x=2` is impossible by a sharpened degree-sum count. -/
theorem xTwoImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hSlack : C.x + C.z + epsilonS G C = 6)
    (hx : C.x = 2) : False := by
  classical
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hA1Card : C.A1.card = 1 := hk
  obtain ⟨u, hA1⟩ := Finset.card_eq_one.mp hA1Card
  have huA1 : u ∈ C.A1 := by simp [hA1]
  have huH : u ∈ C.H := Finset.mem_union_left C.X huA1
  have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have ha1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
  have hA1Degree := outdegree_a1_eq_eight G C hG hMin hBCard hk
  have hA1Second := secondOutdegree_a1_eq_six G C hG hMin hBCard hk hSlack
  obtain ⟨p0, ha1p0, hp0u, hp0ne⟩ :=
    deletedHead_reached_of_secondDegree_six G hBound hG hNoSeymour
      hA1Degree hA1Second ha1u
  have hp0Parts : p0 ∈ C.A1 ∪ C.P := by
    rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
    exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1p0
  have hp0P : p0 ∈ C.P := by
    rcases Finset.mem_union.mp hp0Parts with hp0A1 | hp0P
    · have hp0Eq : p0 = u := by simpa [hA1] using hp0A1
      exact (hp0ne hp0Eq).elim
    · exact hp0P
  have hup0 : ¬G.Adj u p0 := fun hup0 => hG.2 hup0 hp0u
  have huInternalSubset := AOne_internal_subset_X G C hG hk u huA1
  have huInternalMin : 1 ≤ directCount G C.A u := by
    simpa [directCount, CertificateBridge.internalFirstNeighbors, hk] using
      (hPivot u huA).1
  have huInternalLe : directCount G C.A u ≤ 2 := by
    calc
      _ ≤ C.X.card := Finset.card_le_card huInternalSubset
      _ = 2 := hx
  have huInternal : directCount G C.A u = 2 := by
    by_contra hNot
    have hEq : directCount G C.A u = 1 := by omega
    have hBLower := (hPivot u huA).2 (by
      simpa [directCount, CertificateBridge.internalFirstNeighbors, hk]
        using hEq)
    have hBFilter : C.B.filter (G.Adj u) = C.B := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hBCard]
      simpa [r_eq_seven G C hG hMin hBCard hk] using hBLower
    have hp0B : p0 ∈ C.B := by simpa [hPB] using hp0P
    have hp0Filter : p0 ∈ C.B.filter (G.Adj u) := by
      rw [hBFilter]
      exact hp0B
    exact hup0 (Finset.mem_filter.mp hp0Filter).2
  have huInternalEqX : C.A.filter (G.Adj u) = C.X := by
    apply Finset.eq_of_subset_of_card_le huInternalSubset
    have hXCard : C.X.card = 2 := hx
    change (C.A.filter (G.Adj u)).card = 2 at huInternal
    omega
  have huPSubset : C.P.filter (G.Adj u) ⊆ C.P.erase p0 := by
    intro p hp
    exact Finset.mem_erase.mpr ⟨fun h => hup0 (h ▸ (Finset.mem_filter.mp hp).2),
      (Finset.mem_filter.mp hp).1⟩
  have huPLe : directCount G C.P u ≤ 6 := by
    have hCard := Finset.card_le_card huPSubset
    rw [Finset.card_erase_of_mem hp0P, hPCard] at hCard
    exact hCard
  have huDegreeEq := outdegree_H_eq_A_add_P G C hG hPB u huH
  have hMinU := hMin u
  have huPLower : 6 ≤ directCount G C.P u := by omega
  have huPCount : directCount G C.P u = 6 := by omega
  have huDegree : G.outdegree u = 8 := by omega
  have huPFilterEq : C.P.filter (G.Adj u) = C.P.erase p0 := by
    apply Finset.eq_of_subset_of_card_le huPSubset
    rw [Finset.card_erase_of_mem hp0P, hPCard]
    simpa [directCount, CertificateBridge.internalFirstNeighbors]
      using huPCount.symm.le
  have huX : ∀ x ∈ C.X, G.Adj u x := by
    intro x hxX
    have hxFilter : x ∈ C.A.filter (G.Adj u) := by
      rw [huInternalEqX]
      exact hxX
    exact (Finset.mem_filter.mp hxFilter).2
  have hp0Second : p0 ∈ G.secondOutNeighborFinset u := by
    obtain ⟨q, ha1q, hqp0, hqne⟩ :=
      deletedHead_reached_of_secondDegree_six G hBound hG hNoSeymour
        hA1Degree hA1Second ha1p0
    have hqParts : q ∈ C.A1 ∪ C.P := by
      rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
      exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1q
    have hqP : q ∈ C.P := by
      rcases Finset.mem_union.mp hqParts with hqA1 | hqP
      · have hqu : q = u := by simpa [hA1] using hqA1
        exact (hup0 (hqu ▸ hqp0)).elim
      · exact hqP
    have hqErase : q ∈ C.P.erase p0 := Finset.mem_erase.mpr ⟨hqne, hqP⟩
    have huq : G.Adj u q := by
      have : q ∈ C.P.filter (G.Adj u) := by simpa [huPFilterEq] using hqErase
      exact (Finset.mem_filter.mp this).2
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨q, huq, hqp0⟩, hup0,
      fun hp0uEq => (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) huA
          (hp0uEq ▸ (by simpa [hPB] using hp0P))⟩
  have hExternalSecond : externalTargets G C ⊆
      G.secondOutNeighborFinset u := by
    intro e heE
    have heA1Second : e ∈ G.secondOutNeighborFinset C.a1 := by
      rw [secondOutNeighborFinset_a1_eq G C hG hPB]
      simpa [externalTargets] using Finset.mem_union_right C.X heE
    obtain ⟨p, q, hpq, ha1p, hpe, ha1q, hqe⟩ :=
      two_first_predecessors_of_secondDegree_six G hBound hG hNoSeymour
        hA1Degree hA1Second heA1Second
    have pred_in_P : ∀ r, G.Adj C.a1 r → G.Adj r e → r ∈ C.P := by
      intro r ha1r hre
      have hrParts : r ∈ C.A1 ∪ C.P := by
        rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
        exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1r
      rcases Finset.mem_union.mp hrParts with hrA1 | hrP
      · have hru : r = u := by simpa [hA1] using hrA1
        have heCaptured := H_outgoingCaptured G C hG hPB u huH
          ((Digraph.mem_outNeighborFinset (G := G)).mpr (hru ▸ hre))
        rcases Finset.mem_union.mp heCaptured with heA | heP
        · exact ((Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG))
            heA heE).elim
        · exact ((Finset.disjoint_left.mp (disjoint_P_externalTargets G C))
            heP heE).elim
      · exact hrP
    have hpP := pred_in_P p ha1p hpe
    have hqP := pred_in_P q ha1q hqe
    obtain ⟨r, hrP, hre, hrne⟩ :
        ∃ r, r ∈ C.P ∧ G.Adj r e ∧ r ≠ p0 := by
      by_cases hpp0 : p = p0
      · exact ⟨q, hqP, hqe, fun hqp0 => hpq (hpp0.trans hqp0.symm)⟩
      · exact ⟨p, hpP, hpe, hpp0⟩
    have hur : G.Adj u r := by
      have hrErase : r ∈ C.P.erase p0 := Finset.mem_erase.mpr ⟨hrne, hrP⟩
      have : r ∈ C.P.filter (G.Adj u) := by simpa [huPFilterEq] using hrErase
      exact (Finset.mem_filter.mp this).2
    have hue : ¬G.Adj u e := by
      intro hue
      have heCaptured := H_outgoingCaptured G C hG hPB u huH
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hue)
      rcases Finset.mem_union.mp heCaptured with heA | heP
      · exact (Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG))
          heA heE
      · exact (Finset.disjoint_left.mp (disjoint_P_externalTargets G C))
          heP heE
    have heu : e ≠ u := by
      intro heu
      exact (Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG))
        huA (heu ▸ heE)
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨r, hur, hre⟩, hue, heu⟩
  let F : Finset V := {C.a1} ∪ C.R
  let K : Finset V := F ∩ G.outNeighborFinsetOf C.X
  have hKSecond : K ⊆ G.secondOutNeighborFinset u := by
    intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwF, hwReach⟩
    obtain ⟨x, hxX, hxw⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwReach
    have hwA : w ∈ C.A := by
      rcases Finset.mem_union.mp hwF with hwa1 | hwR
      · have : w = C.a1 := Finset.mem_singleton.mp hwa1
        subst w
        exact C.a1_mem_root_outNeighbors
      · exact Digraph.LocalConfiguration.R_subset_A (G := G) C hwR
    have hwNotX : w ∉ C.X := by
      intro hwX
      rcases Finset.mem_union.mp hwF with hwa1 | hwR
      · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C
          (Finset.mem_singleton.mp hwa1 ▸ hwX)
      · exact (Finset.mem_sdiff.mp hwR).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hwX))
    have huw : ¬G.Adj u w := by
      intro huw
      have : w ∈ C.A.filter (G.Adj u) := Finset.mem_filter.mpr ⟨hwA, huw⟩
      exact hwNotX (by simpa [huInternalEqX] using this)
    have hwu : w ≠ u := by
      intro hwu
      subst w
      rcases Finset.mem_union.mp hwF with hua1 | huR
      · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1
          (Finset.mem_singleton.mp hua1 ▸ huA1)
      · exact (Finset.mem_sdiff.mp huR).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X huA1))
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨x, huX x hxX, hxw⟩, huw, hwu⟩
  have hECard : (externalTargets G C).card = 4 := by
    rw [card_externalTargets]
    omega
  have hSecondULe : G.secondOutdegree u ≤ 7 := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hs
      exact hNoSeymour ⟨u, hs⟩
    have := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
    omega
  have hEP : Disjoint (externalTargets G C) {p0} := by
    rw [Finset.disjoint_left]
    intro v hvE hvp0
    have hv : v = p0 := Finset.mem_singleton.mp hvp0
    subst v
    exact (Finset.disjoint_left.mp (disjoint_P_externalTargets G C)) hp0P hvE
  have hEPK : Disjoint (externalTargets G C ∪ {p0}) K := by
    rw [Finset.disjoint_left]
    intro v hvEP hvK
    have hvA : v ∈ C.A := by
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hvK).1 with hva1 | hvR
      · exact Finset.mem_singleton.mp hva1 ▸ C.a1_mem_root_outNeighbors
      · exact Digraph.LocalConfiguration.R_subset_A (G := G) C hvR
    rcases Finset.mem_union.mp hvEP with hvE | hvp0
    · exact (Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG)) hvA hvE
    · have hv : v = p0 := Finset.mem_singleton.mp hvp0
      subst v
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (by simpa [hPB] using hp0P)
  have hUnionSubset : externalTargets G C ∪ {p0} ∪ K ⊆
      G.secondOutNeighborFinset u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvEP | hvK
    · rcases Finset.mem_union.mp hvEP with hvE | hvp0
      · exact hExternalSecond hvE
      · exact Finset.mem_singleton.mp hvp0 ▸ hp0Second
    · exact hKSecond hvK
  have hKCard : K.card ≤ 2 := by
    have hCardLe := Finset.card_le_card hUnionSubset
    rw [Finset.card_union_of_disjoint hEPK,
      Finset.card_union_of_disjoint hEP, hECard] at hCardLe
    simp only [Finset.card_singleton] at hCardLe
    change (G.secondOutNeighborFinset u).card ≤ 7 at hSecondULe
    omega
  have hHCard : C.H.card = 3 := by
    change C.h = 3
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hRCard : C.R.card = 4 := by
    have hXR := x_add_card_R_eq_six G C hG hRootDegree hk
    omega
  have hHF : C.H ∪ F = C.A := by
    simpa [F, Digraph.LocalConfiguration.H, Finset.union_assoc] using
      Digraph.LocalConfiguration.local_parts_union_R (G := G) C
  have hHFDisjoint : Disjoint C.H F := by
    rw [Finset.disjoint_left]
    intro v hvH hvF
    rcases Finset.mem_union.mp hvF with hva1 | hvR
    · have hv : v = C.a1 := Finset.mem_singleton.mp hva1
      subst v
      rcases Finset.mem_union.mp hvH with hvA1 | hvX
      · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
      · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C))
        (Finset.mem_union_left {C.a1} (by
          simpa [Digraph.LocalConfiguration.H] using hvH)) hvR
  have hXF_eq : edgeCount G C.X F = edgeCount G C.X K := by
    unfold edgeCount
    apply Finset.sum_congr rfl
    intro x hxX
    unfold directCount CertificateBridge.internalFirstNeighbors
    congr 1
    ext w
    simp only [Finset.mem_filter, K, Finset.mem_inter]
    constructor
    · rintro ⟨hwF, hxw⟩
      exact ⟨⟨hwF, (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨x, hxX, hxw⟩⟩, hxw⟩
    · exact fun hw => ⟨hw.1.1, hw.2⟩
  have hA1FZero : edgeCount G C.A1 F = 0 := by
    unfold edgeCount
    apply Finset.sum_eq_zero
    intro a ha
    have hau : a = u := by simpa [hA1] using ha
    subst a
    unfold directCount CertificateBridge.internalFirstNeighbors
    apply Finset.card_eq_zero.mpr
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hwF, huw⟩
      have hwA : w ∈ C.A := by
        rcases Finset.mem_union.mp hwF with hwa1 | hwR
        · exact Finset.mem_singleton.mp hwa1 ▸ C.a1_mem_root_outNeighbors
        · exact Digraph.LocalConfiguration.R_subset_A (G := G) C hwR
      have hwFilter : w ∈ C.A.filter (G.Adj u) :=
        Finset.mem_filter.mpr ⟨hwA, huw⟩
      have hwX : w ∈ C.X := by simpa [huInternalEqX] using hwFilter
      rcases Finset.mem_union.mp hwF with hwa1 | hwR
      · exact (Digraph.LocalConfiguration.a1_notMem_X (G := G) C
          (Finset.mem_singleton.mp hwa1 ▸ hwX)).elim
      · exact ((Finset.mem_sdiff.mp hwR).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hwX))).elim
    · intro hw
      simp at hw
  have hHAUpper : edgeCount G C.H C.A ≤ 7 := by
    have hInternal := internal_edgeCount_le_choose_two G C.H hG
    have hXK := edgeCount_le_card_mul_card G C.X K
    have hXCard : C.X.card = 2 := hx
    rw [hHCard] at hInternal
    simp [Nat.choose] at hInternal
    rw [hXCard] at hXK
    have hSource := edgeCount_source_union G C.A1 C.X F
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
    have hTarget := edgeCount_union_of_disjoint G C.H C.H F hHFDisjoint
    change edgeCount G C.H F = edgeCount G C.A1 F + edgeCount G C.X F at hSource
    rw [hA1FZero, Nat.zero_add, hXF_eq] at hSource
    rw [hHF] at hTarget
    omega
  have hHPLower : 17 ≤ edgeCount G C.H C.P := by
    have hDegreeLower : 24 ≤ ∑ h ∈ C.H, G.outdegree h := by
      calc
        24 = ∑ _h ∈ C.H, 8 := by simp [hHCard]
        _ ≤ ∑ h ∈ C.H, G.outdegree h := by
          apply Finset.sum_le_sum
          intro h hh
          exact hMin h
    have hSplit := degreeSum_H_eq_A_add_P G C hG hPB
    omega
  have hPHUpper : edgeCount G C.P C.H ≤ 4 := by
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hCross
    omega
  have hDegreeLowerP : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternalEq := edgeCount_externalTargets G C
  rw [← hExternalEq] at hAccounting
  have hExternalUpper := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, hECard] at hExternalUpper
  have hInternalUpper := internal_edgeCount_le_twentyOne G C.P hG hPCard
  omega

set_option linter.flexible false in
/-- The slack row `x=3` is impossible by equality in all degree capacities
and a four-vertex tournament score count on `H=A1∪X`. -/
theorem xThreeImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPivot : IsMinimalPivot G C)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hSlack : C.x + C.z + epsilonS G C = 6)
    (hx : C.x = 3) : False := by
  classical
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hHCard : C.H.card = 4 := by
    change C.h = 4
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hECard : (externalTargets G C).card = 3 := by
    rw [card_externalTargets]
    omega
  have hRCard : C.R.card = 3 := by
    have hXR := x_add_card_R_eq_six G C hG hRootDegree hk
    omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hPDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hHPLower : 14 ≤ edgeCount G C.H C.P := by
    have hFive := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB
      hRootDegree hk
    simp [hx, Nat.choose] at hFive
    exact hFive
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHUpper : edgeCount G C.P C.H ≤ 14 := by omega
  have hExternalUpper := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, hECard] at hExternalUpper
  have hPPUpper := internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hPAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternalEq := edgeCount_externalTargets G C
  rw [← hExternalEq] at hPAccounting
  have hPDegreeSum : ∑ p ∈ C.P, G.outdegree p = 56 := by omega
  have hPExternal : edgeCount G C.P (externalTargets G C) = 21 := by omega
  have hPH : edgeCount G C.P C.H = 14 := by omega
  have hHP : edgeCount G C.H C.P = 14 := by omega
  have hPP : edgeCount G C.P C.P = 21 := by omega
  have hHAUpper := H_to_A_le_internal_add_x_add_xR G C hG
  rw [hHCard, hx, hRCard] at hHAUpper
  simp [Nat.choose] at hHAUpper
  have hHDegreeLower : 32 ≤ ∑ h ∈ C.H, G.outdegree h := by
    calc
      32 = ∑ _h ∈ C.H, 8 := by simp [hHCard]
      _ ≤ ∑ h ∈ C.H, G.outdegree h := by
        apply Finset.sum_le_sum
        intro h hh
        exact hMin h
  have hHSplit := degreeSum_H_eq_A_add_P G C hG hPB
  have hHA : edgeCount G C.H C.A = 18 := by omega
  have hHDegreeSum : ∑ h ∈ C.H, G.outdegree h = 32 := by omega
  have hHa1Disjoint : Disjoint C.H {C.a1} := by
    rw [Finset.disjoint_left]
    intro v hvH hva1
    have hv : v = C.a1 := Finset.mem_singleton.mp hva1
    subst v
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  have hPartsR : Disjoint (C.H ∪ {C.a1}) C.R := by
    simpa [Digraph.LocalConfiguration.H] using
      Digraph.LocalConfiguration.disjoint_local_parts_R (G := G) C
  have hADecomp : C.H ∪ {C.a1} ∪ C.R = C.A := by
    simpa [Digraph.LocalConfiguration.H] using
      Digraph.LocalConfiguration.local_parts_union_R (G := G) C
  have hHADecomp : edgeCount G C.H C.A =
      edgeCount G C.H C.H + edgeCount G C.H {C.a1} +
        edgeCount G C.H C.R := by
    have hR := edgeCount_union_of_disjoint G C.H (C.H ∪ {C.a1}) C.R hPartsR
    have hA1 := edgeCount_union_of_disjoint G C.H C.H {C.a1} hHa1Disjoint
    rw [hADecomp] at hR
    omega
  have hHHUpper := internal_edgeCount_le_choose_two G C.H hG
  rw [hHCard] at hHHUpper
  simp [Nat.choose] at hHHUpper
  have hHa1Upper := H_to_a1_le_x G C hG
  rw [hx] at hHa1Upper
  have hHRUpper := H_to_R_le_x_mul_card_R G C
  rw [hx, hRCard] at hHRUpper
  have hHH : edgeCount G C.H C.H = 6 := by omega
  have hHa1 : edgeCount G C.H {C.a1} = 3 := by omega
  have hHR : edgeCount G C.H C.R = 9 := by omega
  have hHDegreeEight : ∀ h ∈ C.H, G.outdegree h = 8 := by
    intro h hh
    have hRestLower : 24 ≤ ∑ q ∈ C.H.erase h, G.outdegree q := by
      calc
        24 = ∑ _q ∈ C.H.erase h, 8 := by
          simp [Finset.card_erase_of_mem hh, hHCard]
        _ ≤ ∑ q ∈ C.H.erase h, G.outdegree q := by
          apply Finset.sum_le_sum
          intro q hq
          exact hMin q
    have hSplit := Finset.sum_erase_add C.H G.outdegree hh
    have hMinH := hMin h
    omega
  have hPExternalFull : ∀ p ∈ C.P,
      directCount G (externalTargets G C) p = 3 := by
    intro p hp
    have hRowUpper : directCount G (externalTargets G C) p ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
    have hRestUpper : ∑ q ∈ C.P.erase p,
        directCount G (externalTargets G C) q ≤ 18 := by
      calc
        _ ≤ ∑ _q ∈ C.P.erase p, 3 := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        _ = 18 := by simp [Finset.card_erase_of_mem hp, hPCard]
    have hSplit := Finset.sum_erase_add C.P
      (directCount G (externalTargets G C)) hp
    change (∑ q ∈ C.P, directCount G (externalTargets G C) q) = 21
      at hPExternal
    omega
  have hPToExternal : ∀ p ∈ C.P, ∀ e ∈ externalTargets G C,
      G.Adj p e := by
    intro p hp e he
    exact adj_of_directCount_eq_card G (externalTargets G C) p e
      (by rw [hPExternalFull p hp, hECard]) he
  have hXToA1 : ∀ x ∈ C.X, G.Adj x C.a1 := by
    intro x hxX
    have hIncoming : internalInDegree G C.H C.a1 = 3 := by
      have hCount := edgeCount_eq_sum_incoming G C.H {C.a1}
      simp only [Finset.sum_singleton] at hCount
      omega
    have hSubset : C.H.filter (fun q => G.Adj q C.a1) ⊆ C.X := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqH, hqa1⟩
      rcases Finset.mem_union.mp hqH with hqA1 | hqX
      · exact (hG.2 (Finset.mem_filter.mp hqA1).2 hqa1).elim
      · exact hqX
    have hEq : C.H.filter (fun q => G.Adj q C.a1) = C.X := by
      apply Finset.eq_of_subset_of_card_le hSubset
      change C.X.card ≤ internalInDegree G C.H C.a1
      have hXCard : C.X.card = 3 := hx
      omega
    have : x ∈ C.H.filter (fun q => G.Adj q C.a1) := by rw [hEq]; exact hxX
    exact (Finset.mem_filter.mp this).2
  have hA1RZero : edgeCount G C.A1 C.R = 0 := by
    unfold edgeCount
    apply Finset.sum_eq_zero
    intro a ha
    unfold directCount CertificateBridge.internalFirstNeighbors
    apply Finset.card_eq_zero.mpr
    ext r
    constructor
    · intro hr
      rcases Finset.mem_filter.mp hr with ⟨hrR, har⟩
      have hrX : r ∈ C.X := by
        apply Finset.mem_inter.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          exact ⟨a, Finset.mem_union_left C.P ha, har⟩
        · exact Finset.mem_sdiff.mpr ⟨
            Digraph.LocalConfiguration.R_subset_A (G := G) C hrR, by
              intro hparts
              exact (Finset.mem_sdiff.mp hrR).2 (by
                rcases Finset.mem_union.mp hparts with hrA1 | hra1
                · exact Finset.mem_union_left {C.a1}
                    (Finset.mem_union_left C.X hrA1)
                · exact Finset.mem_union_right (C.A1 ∪ C.X) hra1)⟩
      exact ((Finset.mem_sdiff.mp hrR).2
        (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))).elim
    · intro hr
      simp at hr
  have hXR : edgeCount G C.X C.R = 9 := by
    have hSource := edgeCount_source_union G C.A1 C.X C.R
      (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
    change edgeCount G C.H C.R = edgeCount G C.A1 C.R + edgeCount G C.X C.R
      at hSource
    omega
  have hXToR : ∀ x ∈ C.X, ∀ r ∈ C.R, G.Adj x r := by
    intro x hxX r hrR
    have hRowUpper : directCount G C.R x ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hRCard
    have hRestUpper : ∑ q ∈ C.X.erase x, directCount G C.R q ≤ 6 := by
      have hXCard : C.X.card = 3 := hx
      calc
        _ ≤ ∑ _q ∈ C.X.erase x, 3 := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hRCard
        _ = 6 := by simp [Finset.card_erase_of_mem hxX, hXCard]
    have hSplit := Finset.sum_erase_add C.X (directCount G C.R) hxX
    have hRow : directCount G C.R x = 3 := by
      change (∑ q ∈ C.X, directCount G C.R q) = 9 at hXR
      omega
    exact adj_of_directCount_eq_card G C.R x r (by rw [hRow, hRCard]) hrR
  have hA1Card : C.A1.card = 1 := hk
  obtain ⟨u, hA1⟩ := Finset.card_eq_one.mp hA1Card
  have huA1 : u ∈ C.A1 := by simp [hA1]
  have huH : u ∈ C.H := Finset.mem_union_left C.X huA1
  have huA := Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1
  have ha1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
  obtain ⟨p0, ha1p0, hp0u, hp0ne⟩ :=
    deletedHead_reached_of_secondDegree_six G hBound hG hNoSeymour
      (outdegree_a1_eq_eight G C hG hMin hBCard hk)
      (secondOutdegree_a1_eq_six G C hG hMin hBCard hk hSlack) ha1u
  have hp0Parts : p0 ∈ C.A1 ∪ C.P := by
    rw [← outNeighborFinset_a1_eq_A1_union_P G C hG]
    exact (Digraph.mem_outNeighborFinset (G := G)).mpr ha1p0
  have hp0P : p0 ∈ C.P := by
    rcases Finset.mem_union.mp hp0Parts with hp0A1 | hp0P
    · have hp0Eq : p0 = u := by simpa [hA1] using hp0A1
      exact (hp0ne hp0Eq).elim
    · exact hp0P
  have hup0 : ¬G.Adj u p0 := fun hup0 => hG.2 hup0 hp0u
  have huInternalSubset := AOne_internal_subset_X G C hG hk u huA1
  have huInternalMin : 1 ≤ directCount G C.A u := by
    simpa [directCount, CertificateBridge.internalFirstNeighbors, hk] using
      (hPivot u huA).1
  have huInternalTwo : 2 ≤ directCount G C.A u := by
    by_contra hNot
    have hEq : directCount G C.A u = 1 := by omega
    have hBLower := (hPivot u huA).2 (by
      simpa [directCount, CertificateBridge.internalFirstNeighbors, hk] using hEq)
    have hBFilter : C.B.filter (G.Adj u) = C.B := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hBCard]
      simpa [r_eq_seven G C hG hMin hBCard hk] using hBLower
    have hp0B : p0 ∈ C.B := by simpa [hPB] using hp0P
    have hp0Filter : p0 ∈ C.B.filter (G.Adj u) := by rw [hBFilter]; exact hp0B
    exact hup0 (Finset.mem_filter.mp hp0Filter).2
  have hXPointwise : ∀ x ∈ C.X,
      (G.Adj u x → directCount G C.H x = 0) ∧
      (¬G.Adj u x → directCount G C.H x ≤ 1) := by
    intro x hxX
    have hxH : x ∈ C.H := Finset.mem_union_right C.A1 hxX
    have hxDegree : G.outdegree x = 8 := hHDegreeEight x hxH
    have hxA := Digraph.LocalConfiguration.X_subset_A (G := G) C hxX
    have hxA1 := hXToA1 x hxX
    have hxPCountEq : directCount G C.P x + directCount G C.H x = 4 := by
      have hxDegreeSplit := outdegree_H_eq_A_add_P G C hG hPB x hxH
      have hHHa1 : Disjoint C.H {C.a1} := hHa1Disjoint
      have hHA1 := directCount_union_of_disjoint G C.H {C.a1} x hHHa1
      have hParts := directCount_union_of_disjoint G (C.H ∪ {C.a1}) C.R x hPartsR
      have hHCountLe : directCount G C.H x ≤ 3 := by
        have hSubset : C.H.filter (G.Adj x) ⊆ C.H.erase x := by
          intro v hv
          exact Finset.mem_erase.mpr ⟨fun hvx => hG.1 x (hvx ▸ (Finset.mem_filter.mp hv).2),
            (Finset.mem_filter.mp hv).1⟩
        have hc := Finset.card_le_card hSubset
        rw [Finset.card_erase_of_mem hxH, hHCard] at hc
        exact hc
      have hA1Count : directCount G {C.a1} x = 1 := by
        simp [directCount_singleton, epsilonAt, hxA1]
      have hRCount : directCount G C.R x = 3 := by
        apply le_antisymm
        · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hRCard
        · change 3 ≤ (C.R.filter (G.Adj x)).card
          have hSub : C.R ⊆ C.R.filter (G.Adj x) := by
            intro r hr
            exact Finset.mem_filter.mpr ⟨hr, hXToR x hxX r hr⟩
          simpa [hRCard] using Finset.card_le_card hSub
      rw [hADecomp] at hParts
      omega
    have hxPPositive : 1 ≤ directCount G C.P x := by
      have hHCountLe : directCount G C.H x ≤ 3 := by
        have hSubset : C.H.filter (G.Adj x) ⊆ C.H.erase x := by
          intro v hv
          exact Finset.mem_erase.mpr ⟨fun hvx => hG.1 x
            (hvx ▸ (Finset.mem_filter.mp hv).2), (Finset.mem_filter.mp hv).1⟩
        have hc := Finset.card_le_card hSubset
        rw [Finset.card_erase_of_mem hxH, hHCard] at hc
        exact hc
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by
      simpa [directCount, CertificateBridge.internalFirstNeighbors] using hxPPositive)
    have hpP := (Finset.mem_filter.mp hp).1
    have hxp := (Finset.mem_filter.mp hp).2
    let PM := C.P \ C.P.filter (G.Adj x)
    have hPMCard : PM.card = 7 - directCount G C.P x := by
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hPCard]
      rfl
    have hExternalSecond : externalTargets G C ⊆ G.secondOutNeighborFinset x := by
      intro e heE
      have hpe := hPToExternal p hpP e heE
      have hxe : ¬G.Adj x e := by
        intro hxe
        have hCaptured := H_outgoingCaptured G C hG hPB x hxH
          ((Digraph.mem_outNeighborFinset (G := G)).mpr hxe)
        rcases Finset.mem_union.mp hCaptured with heA | heP
        · exact (Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG))
            heA heE
        · exact (Finset.disjoint_left.mp (disjoint_P_externalTargets G C))
            heP heE
      have hex : e ≠ x := by
        intro hex
        exact (Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG))
          hxA (hex ▸ heE)
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨p, hxp, hpe⟩, hxe, hex⟩
    have hPMSecond : PM ⊆ G.secondOutNeighborFinset x := by
      intro q hq
      rcases Finset.mem_sdiff.mp hq with ⟨hqP, hqNot⟩
      have hxq : ¬G.Adj x q := fun hxq => hqNot (Finset.mem_filter.mpr ⟨hqP, hxq⟩)
      have hqNe : q ≠ x := by
        intro hqx
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hxH
            (hqx ▸ hqP)
      have ha1q : G.Adj C.a1 q := (Finset.mem_filter.mp hqP).2
      rw [Digraph.mem_secondOutNeighborFinset,
        Digraph.mem_secondOutNeighborSet]
      exact ⟨⟨C.a1, hxA1, ha1q⟩, hxq, hqNe⟩
    have hEPMDisjoint : Disjoint (externalTargets G C) PM := by
      rw [Finset.disjoint_left]
      intro v hvE hvPM
      exact (Finset.disjoint_left.mp (disjoint_P_externalTargets G C))
        (Finset.mem_sdiff.mp hvPM).1 hvE
    have hBaseSubset : externalTargets G C ∪ PM ⊆
        G.secondOutNeighborFinset x := Finset.union_subset hExternalSecond hPMSecond
    have hNotSeymour : ¬G.IsSeymourVertex x := by
      intro hs
      exact hNoSeymour ⟨x, hs⟩
    have hSecondLt := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      hNotSeymour
    constructor
    · intro hux
      have hxu : ¬G.Adj x u := fun hxu => hG.2 hux hxu
      have huxNe : u ≠ x := by
        intro hEq
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) huA1
            (hEq ▸ hxX)
      have huSecond : u ∈ G.secondOutNeighborFinset x := by
        rw [Digraph.mem_secondOutNeighborFinset,
          Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨C.a1, hxA1, ha1u⟩, hxu, huxNe⟩
      have hBaseUDisjoint : Disjoint (externalTargets G C ∪ PM) {u} := by
        rw [Finset.disjoint_left]
        intro v hvBase hvU
        have hv : v = u := Finset.mem_singleton.mp hvU
        subst v
        rcases Finset.mem_union.mp hvBase with huE | huPM
        · exact (Finset.disjoint_left.mp (disjoint_A_externalTargets G C hG))
            huA huE
        · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) huA
            (by simpa [hPB] using (Finset.mem_sdiff.mp huPM).1)
      have hAllSubset : externalTargets G C ∪ PM ∪ {u} ⊆
          G.secondOutNeighborFinset x :=
        Finset.union_subset hBaseSubset (fun _ hv =>
          Finset.mem_singleton.mp hv ▸ huSecond)
      have hCardLe := Finset.card_le_card hAllSubset
      rw [Finset.card_union_of_disjoint hBaseUDisjoint,
        Finset.card_union_of_disjoint hEPMDisjoint, hECard,
        Finset.card_singleton, hPMCard] at hCardLe
      rw [hxDegree] at hSecondLt
      change (G.secondOutNeighborFinset x).card < 8 at hSecondLt
      omega
    · intro hNotUx
      have hCardLe := Finset.card_le_card hBaseSubset
      rw [Finset.card_union_of_disjoint hEPMDisjoint, hECard, hPMCard] at hCardLe
      rw [hxDegree] at hSecondLt
      change (G.secondOutNeighborFinset x).card < 8 at hSecondLt
      omega
  let U : Finset V := C.X.filter (G.Adj u)
  have hUCard : U.card = directCount G C.H u := by
    have hUH : C.H.filter (G.Adj u) = U := by
      ext v
      simp only [Finset.mem_filter, U]
      constructor
      · rintro ⟨hvH, huv⟩
        rcases Finset.mem_union.mp hvH with hvA1 | hvX
        · have hvu : v = u := by simpa [hA1] using hvA1
          subst v
          exact (hG.1 u huv).elim
        · exact ⟨hvX, huv⟩
      · rintro ⟨hvX, huv⟩
        exact ⟨Finset.mem_union_right C.A1 hvX, huv⟩
    simp [directCount, CertificateBridge.internalFirstNeighbors, hUH]
  have hUTwo : 2 ≤ U.card := by
    have hUA : C.A.filter (G.Adj u) = U := by
      apply Finset.Subset.antisymm
      · intro v hv
        exact Finset.mem_filter.mpr ⟨huInternalSubset hv, (Finset.mem_filter.mp hv).2⟩
      · intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvX, huv⟩
        exact Finset.mem_filter.mpr
          ⟨Digraph.LocalConfiguration.X_subset_A (G := G) C hvX, huv⟩
    change 2 ≤ (C.A.filter (G.Adj u)).card at huInternalTwo
    simpa [hUA] using huInternalTwo
  have hUXDisjoint : Disjoint U (C.X \ U) := by
    rw [Finset.disjoint_left]
    intro v hvU hvDiff
    exact (Finset.mem_sdiff.mp hvDiff).2 hvU
  have hUXUnion : U ∪ (C.X \ U) = C.X := by
    exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
  have hUHZero : edgeCount G U C.H = 0 := by
    unfold edgeCount
    apply Finset.sum_eq_zero
    intro x hxU
    have hxX := (Finset.mem_filter.mp hxU).1
    have hux := (Finset.mem_filter.mp hxU).2
    exact hXPointwise x hxX |>.1 hux
  have hXminusUpper : edgeCount G (C.X \ U) C.H ≤ (C.X \ U).card := by
    unfold edgeCount
    calc
      (∑ x ∈ C.X \ U, directCount G C.H x) ≤
          ∑ _x ∈ C.X \ U, 1 := by
        apply Finset.sum_le_sum
        intro x hx
        have hxX := (Finset.mem_sdiff.mp hx).1
        have hNotUx : ¬G.Adj u x := by
          intro hux
          exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨hxX, hux⟩)
        exact hXPointwise x hxX |>.2 hNotUx
      _ = (C.X \ U).card := by simp
  have hXHUpper : edgeCount G C.X C.H ≤ 3 - U.card := by
    have hSource := edgeCount_source_union G U (C.X \ U) C.H hUXDisjoint
    rw [hUXUnion, hUHZero, Nat.zero_add] at hSource
    have hCardDiff : (C.X \ U).card = 3 - U.card := by
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      change C.X.card - U.card = 3 - U.card
      have hXCard : C.X.card = 3 := hx
      omega
    omega
  have hULe : U.card ≤ 3 := by
    have := Finset.card_le_card (Finset.filter_subset (G.Adj u) C.X)
    have hXCard : C.X.card = 3 := hx
    simpa [U, hXCard] using this
  have hA1H : edgeCount G C.A1 C.H = directCount G C.H u := by
    unfold edgeCount
    rw [hA1]
    simp
  have hHHDecomp := edgeCount_source_union G C.A1 C.X C.H
    (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)
  change edgeCount G C.H C.H = edgeCount G C.A1 C.H + edgeCount G C.X C.H
    at hHHDecomp
  omega

/-- All six one-unit-slack rows, grouped into the three values of `x`. -/
theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hSlack : C.x + C.z + epsilonS G C = 6) : False := by
  have hRows := parameterRows G C hG hMin hNoSeymour hRootDegree
    hPivot hBCard hk
  rcases hRows with h1 | h2 | h3 | h4
  · exact xOneImpossible G hBound C hG hMin hNoSeymour hPivot hBCard hk
      hSlack h1.1
  · exact xTwoImpossible G hBound C hG hMin hNoSeymour hPivot hRootDegree
      hBCard hk hSlack h2.1
  · exact xThreeImpossible G hBound C hG hMin hNoSeymour hPivot hRootDegree
      hBCard hk hSlack h3.1
  · omega

end SeymourEight.BSevenKOneSlack
