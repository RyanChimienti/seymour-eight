import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.LowDefect.FullUnion
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.FiveZUnionEightCapacity
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.AlphaZeroBetaZero
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.AlphaZeroBetaOne
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.AlphaZeroBetaTwo
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.AlphaOneBetaZero
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.AlphaOneBetaOne
import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.DegreeTen

set_option linter.style.header false

/-!
# The one-missing-incidence three-`Z` branch

The unique deficient `P` row misses a unique vertex `z₀`.  Its other two
`Z`-neighbors have an external outneighborhood union of size at least seven.
That union, together with `z₀` in the equality case, supplies the terminal
per-row inequality already checked by the epsilon-one certificates.
-/

namespace SeymourEight.ThreeZOneMissingBridge

open CertificateBridge FiveZExactGraphBridge FiveZExactPBridge
  FiveZUnionEightCapacity Shared TerminalAlphaBeta TerminalCore
  TerminalCoreGraphBridge BSevenKOneCounting BSevenKOne

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- Exactly one missing incidence in a `7 × 3` rectangle gives one row of
size two and six full rows. -/
theorem exists_exceptional_row (P Z : Finset V)
    (hPCard : P.card = 7) (hZCard : Z.card = 3)
    (hPZ : edgeCount G P Z = 20) :
    ∃ p0 ∈ P, directCount G Z p0 = 2 ∧
      ∀ p ∈ P, p ≠ p0 → directCount G Z p = 3 := by
  classical
  have hSum : ∑ p ∈ P, directCount G Z p = 20 := hPZ
  have hEachLe : ∀ p ∈ P, directCount G Z p ≤ 3 := by
    intro p _hp
    exact (Finset.card_le_card
      (Finset.filter_subset (p := G.Adj p) Z)).trans_eq hZCard
  by_contra hNot
  push Not at hNot
  have hAllThree : ∀ p ∈ P, directCount G Z p = 3 := by
    intro p hp
    have hpLe := hEachLe p hp
    by_contra hne
    have hpTwo : directCount G Z p ≤ 2 := by omega
    have hRestLe : ∑ q ∈ P.erase p, directCount G Z q ≤ 18 := by
      calc
        _ ≤ ∑ _q ∈ P.erase p, 3 := by
          apply Finset.sum_le_sum
          intro q hq
          exact hEachLe q (Finset.mem_of_mem_erase hq)
        _ = 18 := by simp [Finset.card_erase_of_mem hp, hPCard]
    have hSplit := Finset.sum_erase_add P (directCount G Z) hp
    have hpEq : directCount G Z p = 2 := by omega
    obtain ⟨q, hqP, hqNe, hqNotThree⟩ := hNot p hp hpEq
    have hqLe := hEachLe q hqP
    have hqTwo : directCount G Z q ≤ 2 := by omega
    have hOthersLe : ∑ r ∈ (P.erase p).erase q,
        directCount G Z r ≤ 15 := by
      calc
        _ ≤ ∑ _r ∈ (P.erase p).erase q, 3 := by
          apply Finset.sum_le_sum
          intro r hr
          exact hEachLe r
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
        _ = 15 := by
          have hqErase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hqNe, hqP⟩
          simp [Finset.card_erase_of_mem hqErase,
            Finset.card_erase_of_mem hp, hPCard]
    have hqErase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hqNe, hqP⟩
    have hSplitRest := Finset.sum_erase_add (P.erase p)
      (directCount G Z) hqErase
    omega
  have hTotalThree : (∑ _p ∈ P, 3) = 21 := by simp [hPCard]
  have hEq : (∑ p ∈ P, directCount G Z p) = ∑ _p ∈ P, 3 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hAllThree p hp
  omega

omit [Fintype V] [DecidableEq V] in
theorem all_adj_of_directCount_eq_card (Z : Finset V) (p : V)
    (hCount : directCount G Z p = Z.card) :
    ∀ z ∈ Z, G.Adj p z := by
  have hEq : internalFirstNeighbors G Z p = Z := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    unfold directCount internalFirstNeighbors at hCount
    omega
  intro z hz
  have : z ∈ internalFirstNeighbors G Z p := by simpa [hEq] using hz
  exact (Finset.mem_filter.mp this).2

omit [Fintype V] [DecidableEq V] in
/-- Choose the exceptional row and its unique missed column. -/
theorem exists_exceptional_pair (P Z : Finset V)
    (hPCard : P.card = 7) (hZCard : Z.card = 3)
    (hPZ : edgeCount G P Z = 20) :
    ∃ p0 ∈ P, ∃ z0 ∈ Z,
      ¬G.Adj p0 z0 ∧
      (∀ z ∈ Z, z ≠ z0 → G.Adj p0 z) ∧
      (∀ p ∈ P, p ≠ p0 → G.Adj p z0) ∧
      (∀ p ∈ P, directCount G Z p = 2 + epsilonAt G p z0) := by
  classical
  obtain ⟨p0, hp0P, hp0Two, hOtherRows⟩ :=
    exists_exceptional_row G P Z hPCard hZCard hPZ
  let M := Z \ internalFirstNeighbors G Z p0
  have hInternalSubset : internalFirstNeighbors G Z p0 ⊆ Z :=
    Finset.filter_subset _ _
  have hMCard : M.card = 1 := by
    rw [Finset.card_sdiff_of_subset hInternalSubset]
    change Z.card - directCount G Z p0 = 1
    omega
  obtain ⟨z0, hMEq⟩ := Finset.card_eq_one.mp hMCard
  have hz0M : z0 ∈ M := by simp [hMEq]
  have hz0Z : z0 ∈ Z := (Finset.mem_sdiff.mp hz0M).1
  have hp0z0 : ¬G.Adj p0 z0 := by
    have hz0Not := (Finset.mem_sdiff.mp hz0M).2
    intro hAdj
    exact hz0Not (Finset.mem_filter.mpr ⟨hz0Z, hAdj⟩)
  refine ⟨p0, hp0P, z0, hz0Z, hp0z0, ?_, ?_, ?_⟩
  · intro z hzZ hzNe
    by_contra hNotAdj
    have hzM : z ∈ M := Finset.mem_sdiff.mpr
      ⟨hzZ, fun hzInternal ↦ hNotAdj (Finset.mem_filter.mp hzInternal).2⟩
    have : z = z0 := by simpa [hMEq] using hzM
    exact hzNe this
  · intro p hpP hpNe
    exact all_adj_of_directCount_eq_card G Z p
      (by rw [hOtherRows p hpP hpNe, hZCard]) z0 hz0Z
  · intro p hpP
    by_cases hp : p = p0
    · subst p
      simp [epsilonAt, hp0z0, hp0Two]
    · have hpAdj := all_adj_of_directCount_eq_card G Z p
        (by rw [hOtherRows p hpP hp, hZCard]) z0 hz0Z
      simp [epsilonAt, hpAdj, hOtherRows p hpP hp]

/-- The two direct `Z`-neighbors of the exceptional row have at least seven
distinct external outneighbors. -/
theorem seven_le_directZExternalUnion_card (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hZCard : C.Z.card = 3)
    (p0 : V) (_hp0P : p0 ∈ C.P)
    (hp0Two : directCount G C.Z p0 = 2)
    (hPToS : ∀ p ∈ C.P, ∀ z ∈ directZNeighbors G C p0, G.Adj p z) :
    7 ≤ (directZExternalUnion G C p0).card := by
  let S := directZNeighbors G C p0
  let W := directZExternalUnion G C p0
  have hSCard : S.card = 2 := by simpa [S] using hp0Two
  have hSSubset : S ⊆ C.Z := directZNeighbors_subset_Z G C p0
  have hSP : edgeCount G S C.P = 0 := by
    unfold edgeCount
    apply Finset.sum_eq_zero
    intro z hzS
    have hCountZero : directCount G C.P z = 0 := by
      unfold directCount internalFirstNeighbors
      apply Finset.card_eq_zero.mpr
      apply Finset.Subset.antisymm
      · intro p hpFilter
        exact (hG.2 (hPToS p (Finset.mem_filter.mp hpFilter).1 z hzS)
          (Finset.mem_filter.mp hpFilter).2).elim
      · exact Finset.empty_subset _
    exact hCountZero
  have hSZ : edgeCount G S C.Z ≤ 3 := by
    have hMono : edgeCount G S C.Z ≤ edgeCount G C.Z C.Z := by
      unfold edgeCount
      exact Finset.sum_le_sum_of_subset hSSubset
    have hInternal := internal_edgeCount_le_choose_two G C.Z hG
    rw [hZCard] at hInternal
    simpa [Nat.choose] using hMono.trans hInternal
  have hCapacity := directZ_capacity_lower G C hMin p0
  change S.card * (8 - W.card) ≤ edgeCount G S C.Z + edgeCount G S C.P
    at hCapacity
  rw [hSCard, hSP] at hCapacity
  dsimp [W] at hCapacity ⊢
  by_contra hNot
  have hWLe : (directZExternalUnion G C p0).card ≤ 6 := by omega
  omega

/-- If the direct external union has exactly seven vertices, the missed
`Z`-vertex is a strict second neighbor of the exceptional `P`-vertex. -/
theorem missing_mem_secondOutNeighborFinset (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (_hZCard : C.Z.card = 3)
    (p0 z0 : V) (hp0P : p0 ∈ C.P) (hz0Z : z0 ∈ C.Z)
    (hp0Two : directCount G C.Z p0 = 2)
    (hp0z0 : ¬G.Adj p0 z0)
    (hOtherZ : ∀ z ∈ C.Z, z ≠ z0 → G.Adj p0 z)
    (hPToS : ∀ p ∈ C.P, ∀ z ∈ directZNeighbors G C p0, G.Adj p z)
    (hWCard : (directZExternalUnion G C p0).card = 7) :
    z0 ∈ G.secondOutNeighborFinset p0 := by
  classical
  let S := directZNeighbors G C p0
  let W := directZExternalUnion G C p0
  have hSSubset : S ⊆ C.Z := directZNeighbors_subset_Z G C p0
  have hSCard : S.card = 2 := by simpa [S] using hp0Two
  have hNoBack : ∀ z ∈ S, directCount G C.P z = 0 := by
    intro z hzS
    unfold directCount internalFirstNeighbors
    apply Finset.card_eq_zero.mpr
    apply Finset.Subset.antisymm
    · intro p hpFilter
      exact (hG.2 (hPToS p (Finset.mem_filter.mp hpFilter).1 z hzS)
        (Finset.mem_filter.mp hpFilter).2).elim
    · exact Finset.empty_subset _
  have hInternalOne : ∀ z ∈ S, 1 ≤ directCount G C.Z z := by
    intro z hzS
    have hDegree := z_outdegree_eq_retainedCounts G C z (hSSubset hzS)
    have hExternal := directCount_external_le_unionCard G C p0 z hzS
    have hzMin := hMin z
    rw [hNoBack z hzS] at hDegree
    change directCount G (zExternalUnion G C) z ≤ W.card at hExternal
    change W.card = 7 at hWCard
    omega
  have hEdgeLower : 2 ≤ edgeCount G S C.Z := by
    unfold edgeCount
    calc
      2 = ∑ _z ∈ S, 1 := by
        simp [hSCard]
      _ ≤ ∑ z ∈ S, directCount G C.Z z := by
        apply Finset.sum_le_sum
        intro z hzS
        exact hInternalOne z hzS
  by_contra hNotSecond
  have hNoToMissing : ∀ z ∈ S, ¬G.Adj z z0 := by
    intro z hzS hzz0
    have hp0z : G.Adj p0 z := (Finset.mem_filter.mp hzS).2
    have hzNeP : z0 ≠ p0 := by
      intro hEq
      subst z0
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hz0Z hp0P
    apply hNotSecond
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨z, hp0z, hzz0⟩, hp0z0, hzNeP⟩
  have hCountEq : ∀ z ∈ S, directCount G C.Z z = directCount G S z := by
    intro z hzS
    unfold directCount internalFirstNeighbors
    congr 1
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hvZ, hzv⟩
      refine ⟨?_, hzv⟩
      by_contra hvNotS
      have hvEq : v = z0 := by
        by_contra hvNe
        exact hvNotS (Finset.mem_filter.mpr ⟨hvZ, hOtherZ v hvZ hvNe⟩)
      subst v
      exact (hNoToMissing z hzS) hzv
    · rintro ⟨hvS, hzv⟩
      exact ⟨hSSubset hvS, hzv⟩
  have hEdgeEq : edgeCount G S C.Z = edgeCount G S S := by
    unfold edgeCount
    apply Finset.sum_congr rfl
    intro z hzS
    exact hCountEq z hzS
  have hUpper := internal_edgeCount_le_choose_two G S hG
  rw [hEdgeEq] at hEdgeLower
  rw [hSCard] at hUpper
  simp [Nat.choose] at hUpper
  omega

/-- The direct union gives the terminal equation.  At union size seven the
one missing `Z`-vertex contributes the extra second neighbor required at the
exceptional row; at size at least eight the union alone suffices. -/
theorem terminal_equation_of_direct_union (C : G.LocalConfiguration)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P)
    (hEpsilon : epsilonS G C = 0)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (p0 z0 : V) (_hp0P : p0 ∈ C.P) (hz0Z : z0 ∈ C.Z)
    (hPToS : ∀ p ∈ C.P, ∀ z ∈ directZNeighbors G C p0, G.Adj p z)
    (hZeroUnique : ∀ p ∈ C.P, epsilonAt G p z0 = 0 → p = p0)
    (hDegree : ∀ p ∈ C.P, G.outdegree p =
      2 + epsilonAt G p z0 + directCount G C.H p + directCount G C.P p)
    (hWSeven : 7 ≤ (directZExternalUnion G C p0).card)
    (hExactExtra : (directZExternalUnion G C p0).card = 7 →
      z0 ∈ G.secondOutNeighborFinset p0) :
    ∀ p ∈ C.P, qCount G C.P C.H p + 7 ≤
      directCount G C.P p + 2 * directCount G C.H p +
        2 * epsilonAt G p z0 := by
  intro p hp
  let W := directZExternalUnion G C p0
  let Wnew := W.filter fun v ↦ ¬G.Adj p v
  let Q := secondNeighborsThrough G C.P (C.P ∪ C.H) p
  have hWSub := directZExternalUnion_subset_externalUnion G C p0
  have hWP : Disjoint W C.P := by
    exact Finset.disjoint_of_subset_left hWSub
      (disjoint_P_zExternalUnion G C).symm
  have hWZ : Disjoint W C.Z := by
    exact Finset.disjoint_of_subset_left hWSub
      (disjoint_Z_zExternalUnion G C).symm
  have hWnewSecond : Wnew ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvW, hNotAdj⟩
    rcases Finset.mem_sdiff.mp hvW with ⟨hvReach, _hvOutside⟩
    obtain ⟨z, hzS, hzv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hvp : v ≠ p := by
      intro hEq
      subst v
      exact (Finset.disjoint_left.mp hWP) hvW hp
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨z, hPToS p hp z hzS, hzv⟩, hNotAdj, hvp⟩
  have hQSecond : Q ⊆ G.secondOutNeighborFinset p :=
    secondNeighborsThrough_subset_secondOutNeighborFinset
      G C.P (C.P ∪ C.H) p
  have hWQ : Disjoint Wnew Q := by
    rw [Finset.disjoint_left]
    intro v hvWnew hvQ
    have hvW : v ∈ W := (Finset.mem_filter.mp hvWnew).1
    have hvP : v ∈ C.P := (Finset.mem_filter.mp hvQ).1
    exact (Finset.disjoint_left.mp hWP) hvW hvP
  have hSecondCard : Wnew.card + qCount G C.P C.H p ≤
      G.secondOutdegree p := by
    have hSubset : Wnew ∪ Q ⊆ G.secondOutNeighborFinset p :=
      Finset.union_subset hWnewSecond hQSecond
    have hCard := Finset.card_le_card hSubset
    rw [Finset.card_union_of_disjoint hWQ] at hCard
    exact hCard
  have hWSplit : (W.filter (G.Adj p)).card + Wnew.card = W.card :=
    Finset.card_filter_add_card_filter_not (G.Adj p)
  have hDirectW := direct_W_bound_of_captured G C hCaptured W hWZ hWP p hp
  have hNoRoot : epsilonAt G p C.s = 0 := by
    simp [epsilonAt, no_P_to_s_of_epsilonS_zero G C hEpsilon p hp]
  rw [hNoRoot] at hDirectW
  have hSecondLt : G.secondOutdegree p < G.outdegree p := by
    have hNot : ¬G.IsSeymourVertex p := fun hpS ↦ hNoSeymour ⟨p, hpS⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  have hDeg := hDegree p hp
  have hEpsLe : epsilonAt G p z0 ≤ 1 := by
    unfold epsilonAt
    split <;> omega
  by_cases hEight : 8 ≤ W.card
  · dsimp [W, Wnew, Q] at hSecondCard hWSplit hDirectW hEight ⊢
    omega
  · have hWCard : W.card = 7 := by
      change 7 ≤ W.card at hWSeven
      omega
    by_cases hEpsZero : epsilonAt G p z0 = 0
    · have hpEq : p = p0 := hZeroUnique p hp hEpsZero
      have hzSecond : z0 ∈ G.secondOutNeighborFinset p := by
        subst p
        exact hExactExtra (by simpa [W] using hWCard)
      have hzNotWnew : z0 ∉ Wnew := by
        intro hzWnew
        exact (Finset.disjoint_left.mp hWZ)
          (Finset.mem_filter.mp hzWnew).1 hz0Z
      have hzNotQ : z0 ∉ Q := by
        intro hzQ
        have hzP : z0 ∈ C.P := (Finset.mem_filter.mp hzQ).1
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hz0Z hzP
      have hzNotUnion : z0 ∉ Wnew ∪ Q := by simp [hzNotWnew, hzNotQ]
      have hExtraSubset : insert z0 (Wnew ∪ Q) ⊆
          G.secondOutNeighborFinset p := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hzSecond
        · exact Finset.union_subset hWnewSecond hQSecond hv
      have hExtraCard := Finset.card_le_card hExtraSubset
      rw [Finset.card_insert_of_notMem hzNotUnion,
        Finset.card_union_of_disjoint hWQ] at hExtraCard
      change Wnew.card + qCount G C.P C.H p + 1 ≤
        G.secondOutdegree p at hExtraCard
      dsimp [W, Wnew, Q] at hWSplit hDirectW hExtraCard ⊢
      omega
    · have hEpsOne : epsilonAt G p z0 = 1 := by omega
      dsimp [W, Wnew, Q] at hSecondCard hWSplit hDirectW ⊢
      omega

/-- Graph-level closure of the one-missing-incidence branch. -/
theorem impossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 3)
    (hEpsilon : epsilonS G C = 0)
    (hPZ : edgeCount G C.P C.Z = 20) : False := by
  classical
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hZCard : C.Z.card = 3 := hz
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hPB := p_eq_B G C hG hMin hBCard hk
  obtain ⟨p0, hp0P, z0, hz0Z, hp0z0, hOtherZ, hOtherPZ0, hZCount⟩ :=
    exists_exceptional_pair G C.P C.Z hPCard hZCard hPZ
  have hp0Two : directCount G C.Z p0 = 2 := by
    simpa [epsilonAt, hp0z0] using hZCount p0 hp0P
  have hPToS : ∀ p ∈ C.P, ∀ z ∈ directZNeighbors G C p0, G.Adj p z := by
    intro p hp z hzS
    have hzZ : z ∈ C.Z := directZNeighbors_subset_Z G C p0 hzS
    by_cases hpEq : p = p0
    · subst p
      exact (Finset.mem_filter.mp hzS).2
    · have hCountThree : directCount G C.Z p = 3 := by
        have hpz0 := hOtherPZ0 p hp hpEq
        simpa [epsilonAt, hpz0] using hZCount p hp
      exact all_adj_of_directCount_eq_card G C.Z p
        (by rw [hCountThree, hZCard]) z hzZ
  have hZeroUnique : ∀ p ∈ C.P, epsilonAt G p z0 = 0 → p = p0 := by
    intro p hp hZero
    by_contra hpNe
    have hpz0 := hOtherPZ0 p hp hpNe
    simp [epsilonAt, hpz0] at hZero
  have hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
    intro p hp
    exact outgoingCaptured_of_p_eq_B G C hG hPB p hp
  have hDegree : ∀ p ∈ C.P, G.outdegree p =
      2 + epsilonAt G p z0 + directCount G C.H p + directCount G C.P p := by
    intro p hp
    have hLocal := P_outdegree_eq_Z_add_H_add_P
      G C hG hPB hEpsilon p hp
    rw [hZCount p hp] at hLocal
    omega
  have hWSeven := seven_le_directZExternalUnion_card
    G C hG hMin hZCard p0 hp0P hp0Two hPToS
  have hExactExtra : (directZExternalUnion G C p0).card = 7 →
      z0 ∈ G.secondOutNeighborFinset p0 := by
    intro hSeven
    exact missing_mem_secondOutNeighborFinset G C hG hMin hZCard p0 z0
      hp0P hz0Z hp0Two hp0z0 hOtherZ hPToS hSeven
  have hEquation := terminal_equation_of_direct_union G C hCaptured hEpsilon
    hNoSeymour p0 z0 hp0P hz0Z hPToS hZeroUnique hDegree hWSeven hExactExtra
  have hRootCount : ∑ p ∈ C.P, epsilonAt G p z0 = 6 := by
    have hp0Zero : epsilonAt G p0 z0 = 0 := by simp [epsilonAt, hp0z0]
    have hOtherOne : ∀ p ∈ C.P.erase p0, epsilonAt G p z0 = 1 := by
      intro p hpErase
      have hpP := Finset.mem_of_mem_erase hpErase
      have hpNe := (Finset.mem_erase.mp hpErase).1
      simp [epsilonAt, hOtherPZ0 p hpP hpNe]
    have hSplit := Finset.sum_erase_add C.P (epsilonAt G · z0) hp0P
    calc
      (∑ p ∈ C.P, epsilonAt G p z0) =
          ∑ p ∈ C.P.erase p0, epsilonAt G p z0 := by omega
      _ = ∑ _p ∈ C.P.erase p0, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hOtherOne p hp
      _ = 6 := by simp [Finset.card_erase_of_mem hp0P, hPCard]
  have hHP : 18 ≤ edgeCount G C.H C.P := by
    have hc := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    simpa [hx, Nat.choose] using hc
  have hPHUpper : edgeCount G C.P C.H ≤ 17 := by
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hCross
    omega
  have hPPUpper : edgeCount G C.P C.P ≤ 21 :=
    internal_edgeCount_le_twentyOne G C.P hG hPCard
  let alpha := 17 - edgeCount G C.P C.H
  let beta := 21 - edgeCount G C.P C.P
  have hAlpha : edgeCount G C.P C.H + alpha = 17 := by
    dsimp [alpha]
    omega
  have hBeta : edgeCount G C.P C.P + beta = 21 := by
    dsimp [beta]
    omega
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ p ∈ C.P, epsilonAt G p C.s = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [epsilonAt, no_P_to_s_of_epsilonS_zero G C hEpsilon p hp]
  rw [hNoRoot, hPZ] at hAccounting
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 58 - alpha - beta := by
    omega
  have hDefects : alpha + beta ≤ 2 := by
    have hLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
      calc
        56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
        _ ≤ ∑ p ∈ C.P, G.outdegree p := by
          apply Finset.sum_le_sum
          intro p hp
          exact hMin p
    omega
  have hBoundsTen : ∀ p ∈ C.P,
      8 ≤ G.outdegree p ∧ G.outdegree p ≤ 10 := by
    intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) :=
      Finset.single_le_sum (s := C.P) (f := fun q ↦ G.outdegree q - 8)
        (fun _ _ ↦ Nat.zero_le _) hp
    have hRewrite : (∑ q ∈ C.P, G.outdegree q) =
        56 + ∑ q ∈ C.P, (G.outdegree q - 8) := by
      calc
        _ = ∑ q ∈ C.P, (8 + (G.outdegree q - 8)) := by
          apply Finset.sum_congr rfl
          intro q hq
          have := hMin q
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hPCard]
    rw [hDegreeSum] at hRewrite
    exact ⟨hMin p, by omega⟩
  have hBoundsNineOfPositive (hPositive : 1 ≤ alpha + beta) : ∀ p ∈ C.P,
      8 ≤ G.outdegree p ∧ G.outdegree p ≤ 9 := by
    intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) :=
      Finset.single_le_sum (s := C.P) (f := fun q ↦ G.outdegree q - 8)
        (fun _ _ ↦ Nat.zero_le _) hp
    have hRewrite : (∑ q ∈ C.P, G.outdegree q) =
        56 + ∑ q ∈ C.P, (G.outdegree q - 8) := by
      calc
        _ = ∑ q ∈ C.P, (8 + (G.outdegree q - 8)) := by
          apply Finset.sum_congr rfl
          intro q hq
          have := hMin q
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hPCard]
    rw [hDegreeSum] at hRewrite
    exact ⟨hMin p, by omega⟩
  rcases (show (alpha = 0 ∧ beta = 0) ∨
      (alpha = 0 ∧ beta = 1) ∨ (alpha = 0 ∧ beta = 2) ∨
      (alpha = 1 ∧ beta = 0) ∨ (alpha = 1 ∧ beta = 1) ∨
      (alpha = 2 ∧ beta = 0) by omega) with
      h00 | h01 | h02 | h10 | h11 | h20
  · rcases h00 with ⟨hA, hB⟩
    apply degreeTen_impossible_of_graphData G C.P C.H z0 hPCard hHCard
      hG.1 hG.2
    · omega
    · omega
    · exact hHP
    · exact hRootCount
    · exact hDegree
    · exact hBoundsTen
    · exact hEquation
    · omega
  · rcases h01 with ⟨hA, hB⟩
    have hBoundsNine := hBoundsNineOfPositive (by omega)
    have hZero : (0 : BitVec 8).toNat = 0 := by decide
    have hTwenty : (20 : BitVec 8).toNat = 20 := by decide
    have hFiftySeven : (57 : BitVec 8).toNat = 57 := by decide
    exact orderedEdge_impossible_of_graphData G C.P C.H z0 0 20 57
      alphaZeroBetaOne_unsat hPCard hHCard hG.1 hG.2 (by omega) (by omega)
      hHP hRootCount hDegree hBoundsNine hEquation (by omega)
  · rcases h02 with ⟨hA, hB⟩
    have hBoundsNine := hBoundsNineOfPositive (by omega)
    have hZero : (0 : BitVec 8).toNat = 0 := by decide
    have hNineteen : (19 : BitVec 8).toNat = 19 := by decide
    have hFiftySix : (56 : BitVec 8).toNat = 56 := by decide
    exact orderedEdge_impossible_of_graphData G C.P C.H z0 0 19 56
      alphaZeroBetaTwo_unsat hPCard hHCard hG.1 hG.2 (by omega) (by omega)
      hHP hRootCount hDegree hBoundsNine hEquation (by omega)
  · rcases h10 with ⟨hA, hB⟩
    have hBoundsNine := hBoundsNineOfPositive (by omega)
    have hTournament : ∀ {u : V}, u ∈ C.P → ∀ {v : V}, v ∈ C.P →
        u ≠ v → G.Adj u v ∨ G.Adj v u :=
      RawFinalBranch.tournament_of_edgeCount_eq_twentyOne
        G C.P hPCard hG (by omega : edgeCount G C.P C.P = 21)
    exact alphaOne_impossible_of_graphData G C.P C.H z0 hPCard hHCard
      hG.1 hG.2 hTournament (by omega) hHP hRootCount hDegree hBoundsNine
      hEquation (by omega)
  · rcases h11 with ⟨hA, hB⟩
    have hBoundsNine := hBoundsNineOfPositive (by omega)
    have hOne : (1 : BitVec 8).toNat = 1 := by decide
    have hTwenty : (20 : BitVec 8).toNat = 20 := by decide
    have hFiftySix : (56 : BitVec 8).toNat = 56 := by decide
    exact orderedEdge_impossible_of_graphData G C.P C.H z0 1 20 56
      alphaOneBetaOne_unsat hPCard hHCard hG.1 hG.2 (by omega) (by omega)
      hHP hRootCount hDegree hBoundsNine hEquation (by omega)
  · rcases h20 with ⟨hA, hB⟩
    have hBoundsNine := hBoundsNineOfPositive (by omega)
    have hTournament : ∀ {u : V}, u ∈ C.P → ∀ {v : V}, v ∈ C.P →
        u ≠ v → G.Adj u v ∨ G.Adj v u :=
      RawFinalBranch.tournament_of_edgeCount_eq_twentyOne
        G C.P hPCard hG (by omega : edgeCount G C.P C.P = 21)
    apply alphaBetaTwoZero_impossible_of_equation18 G C.P C.H z0 hPCard
      hG hTournament
    · intro p hp
      have hpMin := hMin p
      have hSum : ∑ p ∈ C.P, G.outdegree p = 56 := by
        omega
      have hAll : G.outdegree p = 8 := by
        by_contra hNe
        have hRestLower : 8 * (C.P.erase p).card ≤
            ∑ q ∈ C.P.erase p, G.outdegree q := by
          calc
            _ = ∑ _q ∈ C.P.erase p, 8 := by simp [Nat.mul_comm]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro q hq
              exact hMin q
        have hSplit := Finset.sum_erase_add C.P G.outdegree hp
        rw [Finset.card_erase_of_mem hp, hPCard] at hRestLower
        omega
      rw [← hDegree p hp, hAll]
    · exact hEquation

end SeymourEight.ThreeZOneMissingBridge
