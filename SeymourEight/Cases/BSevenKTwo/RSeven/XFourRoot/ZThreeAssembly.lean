import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.ZThreeLabels
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.BroadFourAssembly
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.RootCoreGraphBridge
import SeymourEight.Cases.BSixKTwo.CoreGraphBridge

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Assembly of the three-`Z` projected core

The graph has exactly two missing incidences in `P × Z`.  The lemmas below
specialize the effective-target capacity argument to this smaller rectangle;
the final bridge then invokes one checked certificate for each possible pair
of total degree defects.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeBridge

open CertificateBridge Shared
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeCore
open FiveZExactGraphBridge FiveZUnionEightCapacity
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.IndividualEffective
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)}) : Encoding :=
  XFourNoRoot.ZThreeBridge.coreBits G.Adj (fun i ↦ (eP i).1) (fun i ↦ (eH i).1)
    (fun i ↦ (eZ i).1)

theorem row_missing_le_total_missing_three (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hZCard : (externalTargets G C).card = 3)
    (p : V) (hpP : p ∈ C.P) :
    3 - directCount G (externalTargets G C) p ≤
      21 - edgeCount G C.P (externalTargets G C) := by
  have hOther : ∑ q ∈ C.P.erase p, directCount G (externalTargets G C) q ≤ 18 := by
    calc
      ∑ q ∈ C.P.erase p, directCount G (externalTargets G C) q ≤
          ∑ _q ∈ C.P.erase p, 3 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      _ = 18 := by simp [Finset.card_erase_of_mem hpP, hPCard]
  have hSplit := Finset.sum_erase_add C.P (fun q => directCount G (externalTargets G C) q) hpP
  have hBound : edgeCount G C.P (externalTargets G C) ≤
      18 + directCount G (externalTargets G C) p := by
    unfold edgeCount
    omega
  have hTotal : edgeCount G C.P (externalTargets G C) ≤ 21 := by
    exact (edgeCount_le_card_mul_card G C.P (externalTargets G C)).trans_eq (by
      rw [hPCard, hZCard])
  omega

theorem directZ_to_P_capacity_three (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 7)
    (hZCard : (externalTargets G C).card = 3) (p : V) (hpP : p ∈ C.P)
    (hps : ¬G.Adj p C.s) :
    edgeCount G (directZNeighbors G C p) C.P ≤
      (21 - edgeCount G C.P (externalTargets G C)) -
        (3 - (directZNeighbors G C p).card) := by
  let S := directZNeighbors G C p
  let T := (externalTargets G C) \ S
  have hS : S ⊆ (externalTargets G C) :=
    (directZNeighbors_subset_Z G C p).trans Finset.subset_union_left
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = (externalTargets G C) := Finset.union_sdiff_of_subset hS
  have hTCard : T.card = 3 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS, hZCard]
  have hpT : directCount G T p = 0 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    apply Finset.card_eq_zero.mpr
    ext z
    simp only [Finset.notMem_empty, iff_false]
    intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzT, hpz⟩
    have hzE := (Finset.mem_sdiff.mp hzT).1
    rcases Finset.mem_union.mp hzE with hzZ | hzRoot
    · exact (Finset.mem_sdiff.mp hzT).2
        (Finset.mem_filter.mpr ⟨hzZ, hpz⟩)
    · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
      · have hzs : z = C.s := by simpa [rootSecondFinset, hReach] using hzRoot
        exact hps (hzs ▸ hpz)
      · simp [rootSecondFinset, hReach] at hzRoot
  have hPT : edgeCount G C.P T ≤ 6 * T.card := by
    calc
      edgeCount G C.P T ≤ ∑ q ∈ C.P, if q = p then 0 else T.card := by
        unfold edgeCount
        apply Finset.sum_le_sum
        intro q hq
        by_cases hqp : q = p
        · subst q
          simp [hpT]
        · simp only [hqp, ↓reduceIte]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 * T.card := by
        rw [← Finset.sum_erase_add C.P
          (fun q => if q = p then 0 else T.card) hpP]
        rw [if_pos rfl, Nat.add_zero]
        calc
          (∑ x ∈ C.P.erase p, if x = p then 0 else T.card) =
              ∑ _x ∈ C.P.erase p, T.card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_neg (Finset.mem_erase.mp hx).1]
          _ = (C.P.erase p).card * T.card := by simp
          _ = 6 * T.card := by
            rw [Finset.card_erase_of_mem hpP, hPCard]
  have hPZSplit : edgeCount G C.P (externalTargets G C) =
      edgeCount G C.P S + edgeCount G C.P T := by
    rw [← hUnion, edgeCount_union_of_disjoint G C.P S T hST]
  have hCross := cross_edgeCount_add_reverse_le G S C.P hG
  rw [hPCard] at hCross
  have hSCard : S.card + T.card = 3 := by
    rw [hTCard]
    have hSLe : S.card ≤ 3 := (Finset.card_le_card hS).trans_eq hZCard
    omega
  have hPZUpper := edgeCount_le_card_mul_card G C.P (externalTargets G C)
  rw [hPCard, hZCard] at hPZUpper
  change edgeCount G S C.P ≤
    (21 - edgeCount G C.P (externalTargets G C)) - (3 - S.card)
  omega

/-- At external defect two, a row with one direct `Z` neighbor supplies at
least eight effective targets; rows with two or three supply at least seven. -/
theorem zThree_effective_lower (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hPCard : C.P.card = 7) (hZCard : (externalTargets G C).card = 3)
    (hMissing : 21 - edgeCount G C.P (externalTargets G C) = 2)
    (p : V) (hpP : p ∈ C.P) (hps : ¬G.Adj p C.s) :
    (if (directZNeighbors G C p).card = 1 then 8 else 7) ≤
      (directZEffectiveUnion G C p).card := by
  let S := directZNeighbors G C p
  let U := directZEffectiveUnion G C p
  have hsLe : S.card ≤ 3 :=
    (Finset.card_le_card ((directZNeighbors_subset_Z G C p).trans
      Finset.subset_union_left)).trans_eq hZCard
  have hsPos : 1 ≤ S.card := by
    have hRow := row_missing_le_total_missing_three G C hPCard hZCard p hpP
    rw [SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
      G C p hpP] at hRow
    have hEpsilon : epsilonAt G p C.s = 0 := by simp [epsilonAt, hps]
    rw [hEpsilon, Nat.add_zero, ← card_directZNeighbors G C p] at hRow
    change 3 - S.card ≤ 21 - edgeCount G C.P (externalTargets G C) at hRow
    rw [hMissing] at hRow
    omega
  have hLower := directZ_effective_capacity_lower G C hMin p
  have hInternal := internal_edgeCount_le_choose_two G S hG
  have hToP := directZ_to_P_capacity_three G C hG hPCard hZCard p hpP hps
  change S.card * (8 - U.card) ≤
    edgeCount G S S + edgeCount G S C.P at hLower
  change edgeCount G S S ≤ S.card.choose 2 at hInternal
  rw [hMissing] at hToP
  change edgeCount G S C.P ≤ 2 - (3 - S.card) at hToP
  change (if S.card = 1 then 8 else 7) ≤ U.card
  interval_cases hS : S.card <;> simp_all [Nat.choose] <;> omega

theorem pDegree_toNat (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Nat) (hp : p < 7) :
    (pDegree (graphBits G C eP eH eZ) p).toNat =
      G.outdegree (eP ⟨p, hp⟩).1 := by
  let v := (eP ⟨p, hp⟩).1
  have hBlocks := pBlockCounts G C.P C.H (externalTargets G C) eP eH eZ hG p hp
  have hCaptured : G.outNeighborFinset v ⊆ (externalTargets G C) ∪ C.H ∪ C.P := by
    intro w hw
    have hc := outgoingCaptured_of_p_eq_B G C hG hPB v (eP ⟨p, hp⟩).2 hw
    simp only [Finset.mem_union, Finset.mem_singleton] at hc ⊢
    rcases hc with ((hwZ | hws) | hwH) | hwP
    · exact Or.inl (Or.inl (Finset.mem_union_left _ hwZ))
    · subst w
      have hvs : G.Adj v C.s :=
        (Digraph.mem_outNeighborFinset (G := G)).mp hw
      exact Or.inl (Or.inl (Finset.mem_union_right _ (by
        simp [rootSecondFinset,
          show ∃ q ∈ C.P, G.Adj q C.s from ⟨v, (eP ⟨p, hp⟩).2, hvs⟩])))
    · exact Or.inl (Or.inr hwH)
    · exact Or.inr hwP
  have hZH : Disjoint (externalTargets G C) C.H := by
    rw [Finset.disjoint_left]
    intro w hwE hwH
    rcases Finset.mem_union.mp hwE with hwZ | hwRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hwZ hwH
    · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
      · have hws : w = C.s := by simpa [rootSecondFinset, hReach] using hwRoot
        subst w
        exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
      · simp [rootSecondFinset, hReach] at hwRoot
  have hZHP : Disjoint ((externalTargets G C) ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro w hw hwP
    rcases Finset.mem_union.mp hw with hwZ | hwH
    · rcases Finset.mem_union.mp hwZ with hwZ | hwRoot
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
      · by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
        · have hws : w = C.s := by simpa [rootSecondFinset, hReach] using hwRoot
          subst w
          exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hwP
        · simp [rootSecondFinset, hReach] at hwRoot
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hwH hwP
  have hDegree := outdegree_eq_directCount_of_captured G
    ((externalTargets G C) ∪ C.H ∪ C.P) v hCaptured
  rw [directCount_union_of_disjoint G ((externalTargets G C) ∪ C.H) C.P v hZHP,
    directCount_union_of_disjoint G (externalTargets G C) C.H v hZH] at hDegree
  have hPLe : directCount G C.P v ≤ 7 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr eP).symm)
  have hHLe : directCount G C.H v ≤ 6 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr eH).symm)
  have hZLe : directCount G (externalTargets G C) v ≤ 3 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr eZ).symm)
  dsimp [v] at hPLe hHLe hZLe hDegree
  simp only [pDegree, BitVec.toNat_add]
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem pSecondCount_le_qCount (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (p : Nat) (hp : p < 7) :
    (pSecondCount (graphBits G C eP eH eZ) p).toNat ≤
      TerminalAlphaBeta.qCount G C.P C.H (eP ⟨p, hp⟩).1 := by
  unfold pSecondCount TerminalAlphaBeta.qCount
  unfold TerminalAlphaBeta.secondNeighborsThrough
  apply XFourNoRoot.ZThreeBridge.count_le_filterCard C.P eP
    (pSecond (graphBits G C eP eH eZ) p)
    (fun v => ¬G.Adj (eP ⟨p, hp⟩).1 v ∧
      v ≠ (eP ⟨p, hp⟩).1 ∧ ∃ w ∈ C.P ∪ C.H,
        G.Adj (eP ⟨p, hp⟩).1 w ∧ G.Adj w v) (by omega)
  intro j hj
  simp only [pSecond, Bool.and_eq_true, decide_eq_true_eq] at hj
  rcases hj with ⟨⟨hpj, hNot⟩, hReach⟩
  have hNotAdj : ¬G.Adj (eP ⟨p, hp⟩).1 (eP j).1 := by
    intro ha
    have hArc : pArc (graphBits G C eP eH eZ) p j = true := by
      rw [pArc_coreBits G.Adj _ _ _ p j hp j.isLt]
      simp [hpj, ha]
    simp [hArc] at hNot
  have hNe : (eP j).1 ≠ (eP ⟨p, hp⟩).1 := by
    intro heq
    have hfin : j = ⟨p, hp⟩ := eP.injective (Subtype.ext heq)
    exact hpj (congrArg Fin.val hfin).symm
  refine ⟨hNotAdj, hNe, ?_⟩
  rw [pReached] at hReach
  simp only [Bool.or_eq_true] at hReach
  rcases hReach with (hPPart | hViaH)
  · rcases hPPart with hDirect | hViaP
    · exact (hNotAdj (by
        rw [pArc_coreBits G.Adj _ _ _ p j hp j.isLt] at hDirect
        simpa [hpj] using of_decide_eq_true hDirect)).elim
    · obtain ⟨middle, hm, hMiddle⟩ :=
        (XFourNoRoot.ZThreeBridge.any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hMiddle
      rcases hMiddle with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
      rw [pArc_coreBits G.Adj _ _ _ p middle hp hm] at hFirst
      rw [pArc_coreBits G.Adj _ _ _ middle j hm j.isLt] at hLast
      exact ⟨(eP ⟨middle, hm⟩).1, Finset.mem_union_left _ (eP _).2,
        (of_decide_eq_true hFirst).2, (of_decide_eq_true hLast).2⟩
  · obtain ⟨middle, hm, hMiddle⟩ :=
      (XFourNoRoot.ZThreeBridge.any_eq_true_iff 6 _).mp hViaH
    simp only [Bool.and_eq_true] at hMiddle
    rcases hMiddle with ⟨hFirst, hLast⟩
    rw [pToH_coreBits G.Adj _ _ _ p middle hp hm] at hFirst
    rw [hToP_coreBits G.Adj _ _ _ middle j hm j.isLt] at hLast
    exact ⟨(eH ⟨middle, hm⟩).1, Finset.mem_union_right _ (eH _).2,
      of_decide_eq_true hFirst, of_decide_eq_true hLast⟩

theorem pConditions_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hMissing : 21 - edgeCount G C.P (externalTargets G C) = 2) :
    pConditions (graphBits G C eP eH eZ) = true := by
  let bits := graphBits G C eP eH eZ
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr eP).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr eH).symm
  have hECard : (externalTargets G C).card = 3 := by
    simpa using (Fintype.card_congr eZ).symm
  rw [pConditions, XFourNoRoot.ZThreeBridge.all_eq_true_iff]
  intro p hp
  let v := (eP ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (eP ⟨p, hp⟩).2
  have hBlocks := pBlockCounts G C.P C.H (externalTargets G C) eP eH eZ hG p hp
  have hDegree := pDegree_toNat G C eP eH eZ hG hPB p hp
  have hSecondGraph :=
    pSecondCount_le_graph G C.P C.H (externalTargets G C) eP eH eZ p hp
  have hMinimum : (8 : BitVec 8).ule (pDegree bits p) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (pDegree bits p).toNat = G.outdegree v by
      simpa [bits, v] using hDegree]
    exact hMin v
  have hEffNat : (effectiveLower bits p).toNat =
      (if directCount G (externalTargets G C) v = 1 then 8 else 7) := by
    have hZNat : (pZOut bits p).toNat =
        directCount G (externalTargets G C) v := by
      simpa [bits, v] using hBlocks.2.2
    by_cases hs : directCount G (externalTargets G C) v = 1
    · have hEq : pZOut bits p = 1 := by
        apply BitVec.eq_of_toNat_eq
        rw [hZNat, hs]
        decide
      simp [effectiveLower, hEq, hs]
    · have hNe : pZOut bits p ≠ 1 := by
        intro hEq
        have := congrArg BitVec.toNat hEq
        rw [hZNat] at this
        simp [hs] at this
      have hEqBool : (pZOut bits p == 1) = false := decide_eq_false hNe
      rw [effectiveLower, hEqBool]
      simp [hs]
  have hIneqNat : (pSecondCount bits p).toNat +
      (effectiveLower bits p).toNat + 1 ≤
      (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut bits p).toNat := by
    by_cases hps : G.Adj v C.s
    · have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
        G C hG hPB hNoSeymour hRootDegree v hvP hps
      have hSecond : (pSecondCount bits p).toNat ≤
          TerminalAlphaBeta.qCount G C.P C.H v := by
        simpa [bits, v] using pSecondCount_le_qCount G C eP eH eZ p hp
      have hEpsilon : epsilonAt G v C.s = 1 := by simp [epsilonAt, hps]
      have hExternal :=
        SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
          G C v hvP
      have hEffLe : (effectiveLower bits p).toNat ≤ 8 := by
        rw [hEffNat]
        split <;> omega
      dsimp [v] at hEquation hSecond hEpsilon hExternal
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      omega
    · have hEff := zThree_effective_lower G C hG hMin hPCard hECard
        hMissing v hvP hps
      have hUnion :=
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.PSecond_add_directZEffective_card_le_second_add_H
          G C hG hPB v hvP hps
      have hNot : ¬G.IsSeymourVertex v := fun h => hNoSeymour ⟨v, h⟩
      have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNot
      have hEpsilon : epsilonAt G v C.s = 0 := by simp [epsilonAt, hps]
      have hExternal :=
        SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
          G C v hvP
      have hEZ : directCount G (externalTargets G C) v =
          directCount G C.Z v := by omega
      have hEff' : (if directCount G (externalTargets G C) v = 1
          then 8 else 7) ≤ (directZEffectiveUnion G C v).card := by
        rw [hEZ]
        simpa [card_directZNeighbors G C v] using hEff
      have hSecond' : (pSecondCount bits p).toNat ≤
          (C.P.filter fun w => w ∈ G.secondOutNeighborFinset v).card := by
        simpa [bits, v] using hSecondGraph
      have hU : (pSecondCount bits p).toNat +
          (directZEffectiveUnion G C v).card ≤
          G.secondOutdegree v + directCount G C.H v :=
        (Nat.add_le_add_right hSecond' _).trans (by simpa using hUnion)
      have hU' : (pSecondCount bits p).toNat +
          (directZEffectiveUnion G C (eP ⟨p, hp⟩).1).card ≤
          G.secondOutdegree (eP ⟨p, hp⟩).1 +
            directCount G C.H (eP ⟨p, hp⟩).1 := by
        simpa [v] using hU
      have hDegreeBlocks : G.outdegree (eP ⟨p, hp⟩).1 =
          directCount G C.P (eP ⟨p, hp⟩).1 +
          directCount G C.H (eP ⟨p, hp⟩).1 +
          directCount G (externalTargets G C) (eP ⟨p, hp⟩).1 := by
        have hpLe : directCount G C.P (eP ⟨p, hp⟩).1 ≤ 7 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
        have hhLe : directCount G C.H (eP ⟨p, hp⟩).1 ≤ 6 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
        have heLe : directCount G (externalTargets G C)
            (eP ⟨p, hp⟩).1 ≤ 3 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
        have hd := hDegree
        simp only [pDegree, BitVec.toNat_add] at hd
        rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2] at hd
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hd
        omega
      dsimp [v] at hNS hEff'
      have hGoal : (pSecondCount bits p).toNat +
          (if directCount G (externalTargets G C) (eP ⟨p, hp⟩).1 = 1
            then 8 else 7) + 1 ≤
          directCount G C.P (eP ⟨p, hp⟩).1 +
            2 * directCount G C.H (eP ⟨p, hp⟩).1 +
            directCount G (externalTargets G C) (eP ⟨p, hp⟩).1 := by
        omega
      rw [hEffNat, hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      simpa [v] using hGoal
  have hBool :
      (pSecondCount bits p + effectiveLower bits p + 1).ule
        (pOut bits p + 2 * pHOut bits p + pZOut bits p) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_mul]
    norm_num [BitVec.toNat_ofNat]
    change ((pSecondCount bits p).toNat +
        (effectiveLower bits p).toNat + 1) % 256 ≤
      ((pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut bits p).toNat) % 256
    have hSecondCap : (pSecondCount bits p).toNat ≤ 7 := by
      have hs : (pSecondCount bits p).toNat ≤
          (C.P.filter fun w => w ∈
            G.secondOutNeighborFinset (eP ⟨p, hp⟩).1).card := by
        simpa [bits] using hSecondGraph
      exact hs.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        hPCard)
    have hEffCap : (effectiveLower bits p).toNat ≤ 8 := by
      rw [hEffNat]
      split <;> omega
    have hL : (pSecondCount bits p).toNat +
        (effectiveLower bits p).toNat + 1 < 256 := by omega
    have hR : (pOut bits p).toNat + 2 * (pHOut bits p).toNat +
        (pZOut bits p).toNat < 256 := by
      rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
      have hpLe : directCount G C.P (eP ⟨p, hp⟩).1 ≤ 7 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
      have hhLe : directCount G C.H (eP ⟨p, hp⟩).1 ≤ 6 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
      have heLe : directCount G (externalTargets G C)
          (eP ⟨p, hp⟩).1 ≤ 3 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hECard
      omega
    rw [Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hR]
    exact hIneqNat
  rw [Bool.and_eq_true]
  exact ⟨hMinimum, hBool⟩

theorem pReachedWithinP_true_iff (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented)
    (p q : Nat) (hp : p < 7) (hq : q < 7) :
    pReachedWithinP (graphBits G C eP eH eZ) p q = true ↔
      G.Adj (eP ⟨p, hp⟩).1 (eP ⟨q, hq⟩).1 ∨
        ∃ w ∈ C.P, G.Adj (eP ⟨p, hp⟩).1 w ∧
          G.Adj w (eP ⟨q, hq⟩).1 := by
  rw [pReachedWithinP, Bool.or_eq_true,
    pArc_coreBits G.Adj _ _ _ p q hp hq,
    XFourNoRoot.ZThreeBridge.any_eq_true_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (hDirect | ⟨middle, hm, hMid⟩)
    · exact Or.inl hDirect.2
    · rcases hMid with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
      rw [pArc_coreBits G.Adj _ _ _ p middle hp hm] at hFirst
      rw [pArc_coreBits G.Adj _ _ _ middle q hm hq] at hLast
      exact Or.inr ⟨(eP ⟨middle, hm⟩).1, (eP ⟨middle, hm⟩).2,
        (of_decide_eq_true hFirst).2, (of_decide_eq_true hLast).2⟩
  · rintro (hDirect | ⟨w, hwP, hFirst, hLast⟩)
    · exact Or.inl ⟨fun h ↦ by
          subst q
          exact hG.1 _ hDirect, hDirect⟩
    · obtain ⟨middle, hmEq⟩ := eP.surjective ⟨w, hwP⟩
      refine Or.inr ⟨middle, middle.isLt, ?_⟩
      have hwEq : (eP middle).1 = w := congrArg Subtype.val hmEq
      subst w
      have hmp : middle.val ≠ p := by
        intro h
        have hm : middle = ⟨p, hp⟩ := Fin.ext h
        have hLoop : G.Adj (eP ⟨p, hp⟩).1 (eP ⟨p, hp⟩).1 := by
          simpa [hm] using hFirst
        exact hG.1 _ hLoop
      have hmq : middle.val ≠ q := by
        intro h
        have hm : middle = ⟨q, hq⟩ := Fin.ext h
        have hLoop : G.Adj (eP ⟨q, hq⟩).1 (eP ⟨q, hq⟩).1 := by
          simpa [hm] using hLast
        exact hG.1 _ hLoop
      have hpm : p ≠ middle.val := Ne.symm hmp
      refine ⟨⟨⟨hmp, hmq⟩, ?_⟩, ?_⟩
      · rw [pArc_coreBits G.Adj _ _ _ p middle hp middle.isLt]
        simp [hpm, hFirst]
      · rw [pArc_coreBits G.Adj _ _ _ middle q middle.isLt hq]
        simp [hmq, hLast]

theorem pReachWithinPCount_toNat (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented)
    (p : Nat) (hp : p < 7) :
    (pReachWithinPCount (graphBits G C eP eH eZ) p).toNat =
      (internalReachWithinTwo G C.P (eP ⟨p, hp⟩).1).card := by
  classical
  rw [pReachWithinPCount, XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 7 _ (by omega),
    internalReachWithinTwo,
    filterCard_eq_sum_fin C.P eP
      (fun v ↦ v ≠ (eP ⟨p, hp⟩).1 ∧
        (G.Adj (eP ⟨p, hp⟩).1 v ∨
          ∃ w ∈ C.P, G.Adj (eP ⟨p, hp⟩).1 w ∧ G.Adj w v))]
  apply Finset.sum_congr rfl
  intro q hq
  have hReach := pReachedWithinP_true_iff G C eP eH eZ hG p q hp q.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  by_cases hBool : p ≠ q.val ∧
      pReachedWithinP (graphBits G C eP eH eZ) p q = true
  · have hGraph : (eP q).1 ≠ (eP ⟨p, hp⟩).1 ∧
        (G.Adj (eP ⟨p, hp⟩).1 (eP q).1 ∨
          ∃ w ∈ C.P, G.Adj (eP ⟨p, hp⟩).1 w ∧ G.Adj w (eP q).1) := by
      exact ⟨fun h ↦ hBool.1 (by
        have hfin : q = ⟨p, hp⟩ := by
          apply eP.injective
          exact Subtype.ext h
        exact (Fin.ext_iff.mp hfin).symm), hReach.mp hBool.2⟩
    rw [if_pos hBool, if_pos hGraph]
  · have hGraph : ¬((eP q).1 ≠ (eP ⟨p, hp⟩).1 ∧
        (G.Adj (eP ⟨p, hp⟩).1 (eP q).1 ∨
          ∃ w ∈ C.P, G.Adj (eP ⟨p, hp⟩).1 w ∧ G.Adj w (eP q).1)) := by
      rintro ⟨hne, hGraph⟩
      apply hBool
      refine ⟨?_, hReach.mpr hGraph⟩
      intro hpq
      apply hne
      have hfin : q = ⟨p, hp⟩ := Fin.ext hpq.symm
      rw [hfin]
    rw [if_neg hBool, if_neg hGraph]

theorem pReachWithinPCount_le_out_second (bits : Encoding)
    (p : Nat) (_hp : p < 7) :
    (pReachWithinPCount bits p).toNat ≤
      (pOut bits p).toNat + (pSecondCount bits p).toNat := by
  rw [pReachWithinPCount]
  have hMono := XFourNoRoot.ZThreeBridge.count_mono (n := 7)
    (fun q ↦ decide (p ≠ q) && pReachedWithinP bits p q)
    (fun q ↦ pArc bits p q || pSecond bits p q) (by omega) (by
      intro q hq hReach
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hReach
      rcases hReach with ⟨hpq, hReach⟩
      by_cases hArc : pArc bits p q = true
      · simp [hArc]
      · have hArcFalse := Bool.eq_false_of_not_eq_true hArc
        have hFullReach : pReached bits p q = true := by
          rw [pReached]
          rw [pReachedWithinP] at hReach
          simp only [Bool.or_eq_true] at hReach ⊢
          rcases hReach with hDirect | hVia
          · exact (hArc hDirect).elim
          · exact Or.inl (Or.inr hVia)
        have hSecond : pSecond bits p q = true := by
          simp [pSecond, hpq, hArcFalse, hFullReach]
        simp [hSecond])
  refine hMono.trans ?_
  rw [XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  have hOrLe : (∑ i : Fin 7,
      if pArc bits p i || pSecond bits p i then 1 else 0) ≤
      ∑ i : Fin 7, ((if pArc bits p i then 1 else 0) +
        (if pSecond bits p i then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    cases hA : pArc bits p i <;> cases hS : pSecond bits p i <;>
      simp
  rw [Finset.sum_add_distrib, ← XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 7 _ (by omega),
    ← XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 7 _ (by omega)] at hOrLe
  simpa [pOut, pSecondCount] using hOrLe

theorem sharpKing_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (beta : Nat) (hBeta : beta ≤ 1)
    (hTotal : edgeCount G C.P C.P = 21 - beta) :
    sharpKing beta (graphBits G C eP eH eZ) = true := by
  let bits := graphBits G C eP eH eZ
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr eP).symm
  have hNonempty : C.P.Nonempty := ⟨(eP 0).1, (eP 0).2⟩
  obtain ⟨v, hvP, hKing⟩ :=
    exists_internalReachWithinTwo_add_missing_ge G C.P hNonempty hG
  obtain ⟨p, hpEq⟩ := eP.surjective ⟨v, hvP⟩
  have hvEq : (eP p).1 = v := congrArg Subtype.val hpEq
  have hMissing := card_internalMissingPairs_add_edgeCount G C.P hG
  rw [hPCard, hTotal] at hMissing
  norm_num [Nat.choose] at hMissing
  have hReach : 6 - beta ≤
      (internalReachWithinTwo G C.P (eP p).1).card := by
    simpa [hvEq, hPCard] using (show
      6 - beta ≤ (internalReachWithinTwo G C.P v).card by omega)
  have hReachBits := pReachWithinPCount_toNat G C eP eH eZ hG p p.isLt
  have hProjected := pReachWithinPCount_le_out_second bits p p.isLt
  have hOutSecond : 6 - beta ≤
      (pOut bits p).toNat + (pSecondCount bits p).toNat := by
    rw [hReachBits] at hProjected
    exact hReach.trans hProjected
  have hOutLe : (pOut bits p).toNat ≤ 7 := by
    rw [(pBlockCounts G C.P C.H (externalTargets G C) eP eH eZ hG p p.isLt).1]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hSecondLe : (pSecondCount bits p).toNat ≤ 7 := by
    have hs := pSecondCount_le_graph G C.P C.H (externalTargets G C) eP eH eZ p p.isLt
    exact hs.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      hPCard)
  rw [sharpKing, XFourNoRoot.ZThreeBridge.any_eq_true_iff]
  refine ⟨p, p.isLt, ?_⟩
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  have hSumLt : (pOut (graphBits G C eP eH eZ) p).toNat +
      (pSecondCount (graphBits G C eP eH eZ) p).toNat < 256 := by
    simpa [bits] using (show (pOut bits p).toNat +
      (pSecondCount bits p).toNat < 256 by omega)
  rw [Nat.mod_eq_of_lt hSumLt]
  interval_cases beta <;> simpa [bits] using hOutSecond

theorem pExact_true_iff (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Nat) (hp : p < 7) :
    pExact (graphBits G C eP eH eZ) p = true ↔
      G.outdegree (eP ⟨p, hp⟩).1 = 8 := by
  rw [pExact, beq_iff_eq]
  constructor
  · intro h
    have hNat := congrArg BitVec.toNat h
    rw [pDegree_toNat G C eP eH eZ hG hPB p hp] at hNat
    simpa using hNat
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [pDegree_toNat G C eP eH eZ hG hPB p hp, h]
    decide

theorem exactCount_toNat (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B) :
    (exactCount (graphBits G C eP eH eZ)).toNat =
      (C.P.filter fun p ↦ G.outdegree p = 8).card := by
  rw [exactCount, XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 7 _ (by omega),
    filterCard_eq_sum_fin C.P eP (fun p ↦ G.outdegree p = 8)]
  apply Finset.sum_congr rfl
  intro p hp
  have hExact := pExact_true_iff G C eP eH eZ hG hPB p p.isLt
  by_cases he : pExact (graphBits G C eP eH eZ) p = true
  · simp [he, hExact.mp he]
  · have hg : G.outdegree (eP p).1 ≠ 8 := fun h ↦ he (hExact.mpr h)
    have hef := Bool.eq_false_of_not_eq_true he
    simp [hef, hg]

theorem exactOutsideOut_toNat (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Nat) (hp : p < 7) :
    (exactOutsideOut (graphBits G C eP eH eZ) p).toNat =
      directCount G (C.P \ C.P.filter fun q ↦ G.outdegree q = 8)
        (eP ⟨p, hp⟩).1 := by
  let S := C.P.filter fun q ↦ G.outdegree q = 8
  rw [exactOutsideOut, XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  change _ = ((C.P \ S).filter (G.Adj (eP ⟨p, hp⟩).1)).card
  rw [show (C.P \ S).filter (G.Adj (eP ⟨p, hp⟩).1) =
      C.P.filter (fun q ↦ q ∉ S ∧ G.Adj (eP ⟨p, hp⟩).1 q) by
    ext q
    simp [and_assoc]]
  rw [filterCard_eq_sum_fin C.P eP
    (fun q ↦ q ∉ S ∧ G.Adj (eP ⟨p, hp⟩).1 q)]
  apply Finset.sum_congr rfl
  intro q hq
  have hExact := pExact_true_iff G C eP eH eZ hG hPB q q.isLt
  by_cases hd : G.outdegree (eP q).1 = 8
  · have he := hExact.mpr hd
    simp [he, S, hd]
  · have heNot : pExact (graphBits G C eP eH eZ) q ≠ true :=
      fun he ↦ hd (hExact.mp he)
    have heFalse := Bool.eq_false_of_not_eq_true heNot
    by_cases ha : G.Adj (eP ⟨p, hp⟩).1 (eP q).1
    · have hpq : p ≠ q.val := by
        intro hpq
        have hfin : q = ⟨p, hp⟩ := Fin.ext hpq.symm
        have hLoop : G.Adj (eP ⟨p, hp⟩).1 (eP ⟨p, hp⟩).1 := by
          simpa [hfin] using ha
        exact hG.1 _ hLoop
      rw [pArc_coreBits G.Adj _ _ _ p q hp q.isLt]
      simp [heFalse, S, hd, ha, hpq]
    · rw [pArc_coreBits G.Adj _ _ _ p q hp q.isLt]
      simp [heFalse, S, hd, ha]

theorem exactClassKing_betaZero_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hMissing : 21 - edgeCount G C.P (externalTargets G C) = 2)
    (hPP : edgeCount G C.P C.P = 21)
    (hS : (C.P.filter fun p ↦ G.outdegree p = 8).Nonempty) :
    exactClassKing (graphBits G C eP eH eZ) = true := by
  let bits := graphBits G C eP eH eZ
  let S := C.P.filter fun p ↦ G.outdegree p = 8
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr eP).symm
  have hHCard : C.H.card = 6 := by
    simpa using (Fintype.card_congr eH).symm
  have hZCard : (externalTargets G C).card = 3 := by
    simpa using (Fintype.card_congr eZ).symm
  have hSP : S ⊆ C.P := Finset.filter_subset _ _
  have hDegree : ∀ p ∈ S,
      directCount G (externalTargets G C) p + directCount G C.H p + directCount G C.P p = 8 := by
    intro v hvS
    have hvDegree : G.outdegree v = 8 := (Finset.mem_filter.mp hvS).2
    obtain ⟨p, hpEq⟩ := eP.surjective ⟨v, hSP hvS⟩
    have hvEq : (eP p).1 = v := congrArg Subtype.val hpEq
    have hd0 := pDegree_toNat G C eP eH eZ hG hPB p p.isLt
    have hd : (pDegree bits p).toNat = G.outdegree (eP p).1 := by
      simpa [bits] using hd0
    have hb := pBlockCounts G C.P C.H (externalTargets G C) eP eH eZ hG p p.isLt
    have hbP : (pOut bits p).toNat = directCount G C.P (eP p).1 := by
      simpa [bits] using hb.1
    have hbH : (pHOut bits p).toNat = directCount G C.H (eP p).1 := by
      simpa [bits] using hb.2.1
    have hbZ : (pZOut bits p).toNat = directCount G (externalTargets G C) (eP p).1 := by
      simpa [bits] using hb.2.2
    have hpLe : directCount G C.P (eP p).1 ≤ 7 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hhLe : directCount G C.H (eP p).1 ≤ 6 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hzLe : directCount G (externalTargets G C) (eP p).1 ≤ 3 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
    simp only [pDegree, BitVec.toNat_add] at hd
    rw [hbP, hbH, hbZ] at hd
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hd
    rw [hvEq] at hd
    omega
  have hSecond : ∀ p ∈ S,
      (internalSecondNeighbors (G := G) S p).card +
          (if directCount G (externalTargets G C) p = 1 then 8 else 7) ≤
        7 + directCount G C.H p := by
    intro v hvS
    have hvP : v ∈ C.P := hSP hvS
    by_cases hps : G.Adj v C.s
    · have hInternalQ : (internalSecondNeighbors (G := G) S v).card ≤
          TerminalAlphaBeta.qCount G C.P C.H v := by
        unfold TerminalAlphaBeta.qCount TerminalAlphaBeta.secondNeighborsThrough
        apply Finset.card_le_card
        intro w hw
        rcases Finset.mem_filter.mp hw with
          ⟨hwS, hNot, hwv, middle, hmS, hFirst, hLast⟩
        exact Finset.mem_filter.mpr ⟨hSP hwS, hNot, hwv, middle,
          Finset.mem_union_left _ (hSP hmS), hFirst, hLast⟩
      have hEquation := EpsilonOneRootCoreGraphBridge.rootNeighborhoodEquation
        G C hG hPB hNoSeymour hRootDegree v hvP hps
      have hExternal :=
        SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
          G C v hvP
      have hEpsilon : epsilonAt G v C.s = 1 := by simp [epsilonAt, hps]
      have hvDegree := hDegree v hvS
      have hEffLe :
          (if directCount G (externalTargets G C) v = 1 then 8 else 7) ≤ 8 := by
        split <;> omega
      omega
    · have hInternal : (internalSecondNeighbors (G := G) S v).card ≤
          (C.P.filter fun w ↦ w ∈ G.secondOutNeighborFinset v).card := by
        apply Finset.card_le_card
        intro w hw
        rcases Finset.mem_filter.mp hw with
          ⟨hwS, hNot, hwv, middle, hmS, hFirst, hLast⟩
        apply Finset.mem_filter.mpr
        refine ⟨hSP hwS, ?_⟩
        rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
        exact ⟨⟨middle, hFirst, hLast⟩, hNot, hwv⟩
      have hEff := zThree_effective_lower G C hG hMin hPCard hZCard
        hMissing v hvP hps
      have hUnion :=
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.PSecond_add_directZEffective_card_le_second_add_H
          G C hG hPB v hvP hps
      have hNS := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
        (fun h ↦ hNoSeymour ⟨v, h⟩)
      have hExternal :=
        SeymourEight.BSixKTwoCoreGraphBridge.directCount_externalTargets
          G C v hvP
      have hEpsilon : epsilonAt G v C.s = 0 := by simp [epsilonAt, hps]
      have hEZ : directCount G (externalTargets G C) v =
          directCount G C.Z v := by omega
      have hEff' : (if directCount G (externalTargets G C) v = 1
          then 8 else 7) ≤ (directZEffectiveUnion G C v).card := by
        rw [hEZ]
        simpa [card_directZNeighbors G C v] using hEff
      have hvDegree : G.outdegree v = 8 := (Finset.mem_filter.mp hvS).2
      omega
  let delta : V → Nat := fun p ↦ if directCount G (externalTargets G C) p = 1 then 1 else 0
  have hDeltaLeH : ∀ p ∈ S, delta p ≤ directCount G C.H p := by
    intro v hvS
    by_cases hz : directCount G (externalTargets G C) v = 1
    · have hPLe : directCount G C.P v ≤ 6 := by
        calc
          directCount G C.P v ≤ (C.P.erase v).card := by
            unfold directCount CertificateBridge.internalFirstNeighbors
            apply Finset.card_le_card
            intro w hw
            apply Finset.mem_erase.mpr
            refine ⟨?_, (Finset.mem_filter.mp hw).1⟩
            intro hwv
            subst w
            exact hG.1 _ (Finset.mem_filter.mp hw).2
          _ = 6 := by rw [Finset.card_erase_of_mem (hSP hvS), hPCard]
      have hd := hDegree v hvS
      simp [delta, hz]
      omega
    · simp [delta, hz]
  have hDegreeAdjusted : ∀ p ∈ S,
      (directCount G (externalTargets G C) p + delta p) +
          (directCount G C.H p - delta p) + directCount G C.P p = 8 := by
    intro v hvS
    have hd := hDegree v hvS
    have hdel := hDeltaLeH v hvS
    omega
  have hSecondAdjusted : ∀ p ∈ S,
      (internalSecondNeighbors (G := G) S p).card + 7 ≤
        7 + (directCount G C.H p - delta p) := by
    intro v hvS
    have hs := hSecond v hvS
    have hdel := hDeltaLeH v hvS
    by_cases hz : directCount G (externalTargets G C) v = 1
    · simp [delta, hz] at hs ⊢
      omega
    · simp [delta, hz] at hs ⊢
      omega
  obtain ⟨v, hvS, hBound⟩ := exists_noRootStatus_king_bound G C.P S
    (fun p ↦ directCount G (externalTargets G C) p + delta p)
    (fun p ↦ directCount G C.H p - delta p)
    7 hS hSP hG hDegreeAdjusted hSecondAdjusted
  have hPPEq : edgeCount G C.P C.P = C.P.card.choose 2 := by
    rw [hPP, hPCard]
    decide
  have hMissingP := card_internalMissingPairs_add_edgeCount G C.P hG
  have hpZero : (internalMissingPairs G C.P).card = 0 := by omega
  have hMissingS : (internalMissingPairs G S).card = 0 := by
    have hMono := internalMissingPairs_mono G hSP
    have hc := Finset.card_le_card hMono
    rw [hpZero] at hc
    omega
  rw [hMissingS] at hBound
  obtain ⟨p, hpEq⟩ := eP.surjective ⟨v, hSP hvS⟩
  have hvEq : (eP p).1 = v := congrArg Subtype.val hpEq
  have hExactBool : pExact bits p = true := by
    apply (pExact_true_iff G C eP eH eZ hG hPB p p.isLt).mpr
    simpa [hvEq] using (Finset.mem_filter.mp hvS).2
  have hCount := exactCount_toNat G C eP eH eZ hG hPB
  have hOutside := exactOutsideOut_toNat G C eP eH eZ hG hPB p p.isLt
  have hBlocks := pBlockCounts G C.P C.H (externalTargets G C) eP eH eZ hG p p.isLt
  have hEffNat : (effectiveLower bits p).toNat =
      (if directCount G (externalTargets G C) v = 1 then 8 else 7) := by
    have hZNat : (pZOut bits p).toNat = directCount G (externalTargets G C) v := by
      simpa [bits, hvEq] using hBlocks.2.2
    by_cases hs : directCount G (externalTargets G C) v = 1
    · have hEq : pZOut bits p = 1 := by
        apply BitVec.eq_of_toNat_eq
        rw [hZNat, hs]
        decide
      simp [effectiveLower, hs, hEq]
    · have hNe : pZOut bits p ≠ 1 := by
        intro he
        have := congrArg BitVec.toNat he
        rw [hZNat] at this
        simp [hs] at this
      have hEqBool : (pZOut bits p == 1) = false := decide_eq_false hNe
      rw [effectiveLower, hEqBool]
      simp [hs]
  rw [exactClassKing, XFourNoRoot.ZThreeBridge.any_eq_true_iff]
  refine ⟨p, p.isLt, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨hExactBool, ?_⟩
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  norm_num [BitVec.toNat_ofNat]
  have hL : (exactCount bits).toNat + (pZOut bits p).toNat +
      (effectiveLower bits p).toNat + (exactOutsideOut bits p).toNat < 256 := by
    have hc : (exactCount bits).toNat ≤ 7 := by
      rw [hCount]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hz : (pZOut bits p).toNat ≤ 3 := by rw [hBlocks.2.2]; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
    have he : (effectiveLower bits p).toNat ≤ 8 := by rw [hEffNat]; split <;> omega
    have ho : (exactOutsideOut bits p).toNat ≤ 7 := by
      rw [hOutside]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        ((Finset.card_le_card (Finset.sdiff_subset)).trans_eq hPCard)
    omega
  rw [Nat.mod_eq_of_lt hL]
  have hMissingLe : (exactMissingPairs bits).toNat ≤ 21 := by
    rw [exactMissingPairs, XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 21 _ (by omega)]
    calc
      (∑ i : Fin 21, if (let i' := i.val / 6
          let j0 := i.val % 6
          let j := if j0 < i' then j0 else j0 + 1
          decide (i' < j) && pExact bits i' && pExact bits j &&
            !pArc bits i' j && !pArc bits j i') then 1 else 0) ≤
          ∑ _i : Fin 21, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> omega
      _ = 21 := by simp
  have hR : 16 + (exactMissingPairs bits).toNat < 256 := by omega
  change (exactCount bits).toNat + (pZOut bits p).toNat +
      (effectiveLower bits p).toNat + (exactOutsideOut bits p).toNat ≤
    (16 + (exactMissingPairs bits).toNat) % 256
  rw [Nat.mod_eq_of_lt hR]
  rw [hCount, hBlocks.2.2, hEffNat, hOutside]
  rw [hvEq]
  change S.card + directCount G (externalTargets G C) v +
      (if directCount G (externalTargets G C) v = 1 then 8 else 7) +
      directCount G (C.P \ S) v ≤ 16 + (exactMissingPairs bits).toNat
  by_cases hz : directCount G (externalTargets G C) v = 1
  · simp [delta, hz] at hBound ⊢
    omega
  · simp [delta, hz] at hBound ⊢
    omega

theorem exactClassKing_betaOne_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPZ : edgeCount G C.P (externalTargets G C) = 19)
    (hAllExact : ∀ p ∈ C.P, G.outdegree p = 8) :
    exactClassKing (graphBits G C eP eH eZ) = true := by
  let bits := graphBits G C eP eH eZ
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr eP).symm
  have hZCard : (externalTargets G C).card = 3 := by
    simpa using (Fintype.card_congr eZ).symm
  have hDeficient : ∃ p ∈ C.P, directCount G (externalTargets G C) p ≤ 2 := by
    by_contra hNo
    push Not at hNo
    have hRows : ∀ p ∈ C.P, directCount G (externalTargets G C) p = 3 := by
      intro p hp
      have hLe : directCount G (externalTargets G C) p ≤ 3 := by
        unfold directCount CertificateBridge.internalFirstNeighbors
        exact (Finset.card_le_card
          (Finset.filter_subset (G.Adj p) (externalTargets G C))).trans_eq hZCard
      have hGt := hNo p hp
      omega
    have hSum : edgeCount G C.P (externalTargets G C) = 21 := by
      unfold edgeCount
      calc
        (∑ p ∈ C.P, directCount G (externalTargets G C) p) = ∑ _p ∈ C.P, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hRows p hp]
        _ = 21 := by simp [hPCard]
    omega
  obtain ⟨v, hvP, hvZ⟩ := hDeficient
  obtain ⟨p, hpEq⟩ := eP.surjective ⟨v, hvP⟩
  have hvEq : (eP p).1 = v := congrArg Subtype.val hpEq
  have hExactBool : pExact bits p = true := by
    apply (pExact_true_iff G C eP eH eZ hG hPB p p.isLt).mpr
    simpa [hvEq] using hAllExact v hvP
  have hCount := exactCount_toNat G C eP eH eZ hG hPB
  have hOutside := exactOutsideOut_toNat G C eP eH eZ hG hPB p p.isLt
  have hBlocks := pBlockCounts G C.P C.H (externalTargets G C) eP eH eZ hG p p.isLt
  have hSAll : C.P.filter (fun q ↦ G.outdegree q = 8) = C.P := by
    apply Finset.filter_eq_self.mpr
    exact hAllExact
  have hCountNat : (exactCount bits).toNat = 7 := by
    rw [hCount, hSAll, hPCard]
  have hOutsideNat : (exactOutsideOut bits p).toNat = 0 := by
    rw [hOutside, hSAll]
    unfold directCount CertificateBridge.internalFirstNeighbors
    simp
  have hZNat : (pZOut bits p).toNat = directCount G (externalTargets G C) v := by
    simpa [bits, hvEq] using hBlocks.2.2
  have hEffNat : (effectiveLower bits p).toNat =
      (if directCount G (externalTargets G C) v = 1 then 8 else 7) := by
    by_cases hs : directCount G (externalTargets G C) v = 1
    · have hEq : pZOut bits p = 1 := by
        apply BitVec.eq_of_toNat_eq
        rw [hZNat, hs]
        decide
      simp [effectiveLower, hs, hEq]
    · have hNe : pZOut bits p ≠ 1 := by
        intro he
        have := congrArg BitVec.toNat he
        rw [hZNat] at this
        simp [hs] at this
      have hEqBool : (pZOut bits p == 1) = false := decide_eq_false hNe
      rw [effectiveLower, hEqBool]
      simp [hs]
  rw [exactClassKing, XFourNoRoot.ZThreeBridge.any_eq_true_iff]
  refine ⟨p, p.isLt, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨hExactBool, ?_⟩
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
  norm_num [BitVec.toNat_ofNat]
  have hL : (exactCount bits).toNat + (pZOut bits p).toNat +
      (effectiveLower bits p).toNat + (exactOutsideOut bits p).toNat < 256 := by
    rw [hCountNat, hZNat, hEffNat, hOutsideNat]
    split <;> omega
  rw [Nat.mod_eq_of_lt hL]
  have hMissingLe : (exactMissingPairs bits).toNat ≤ 21 := by
    rw [exactMissingPairs, XFourNoRoot.ZThreeBridge.toNat_count_eq_fin_sum 21 _ (by omega)]
    calc
      (∑ i : Fin 21, if (let i' := i.val / 6
          let j0 := i.val % 6
          let j := if j0 < i' then j0 else j0 + 1
          decide (i' < j) && pExact bits i' && pExact bits j &&
            !pArc bits i' j && !pArc bits j i') then 1 else 0) ≤
          ∑ _i : Fin 21, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> omega
      _ = 21 := by simp
  have hR : 16 + (exactMissingPairs bits).toNat < 256 := by omega
  change (exactCount bits).toNat + (pZOut bits p).toNat +
      (effectiveLower bits p).toNat + (exactOutsideOut bits p).toNat ≤
    (16 + (exactMissingPairs bits).toNat) % 256
  rw [Nat.mod_eq_of_lt hR, hCountNat, hZNat, hEffNat, hOutsideNat]
  split <;> omega

theorem allExternalReached_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)}) :
    allZReached (graphBits G C eP eH eZ) = true := by
  rw [allZReached, XFourNoRoot.ZThreeBridge.all_eq_true_iff]
  intro z hz
  rw [XFourNoRoot.ZThreeBridge.any_eq_true_iff]
  have hzMem := (eZ ⟨z, hz⟩).2
  rcases Finset.mem_union.mp hzMem with hzMem | hRootMem
  · rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
        (Finset.mem_sdiff.mp hzMem).1 with ⟨p, hp, hpz⟩
    obtain ⟨i, hi⟩ := eP.surjective ⟨p, hp⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt hz]
    simpa [congrArg Subtype.val hi] using hpz
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · obtain ⟨p, hp, hps⟩ := hReach
      have hLabel : (eZ ⟨z, hz⟩).1 = C.s := by
        simpa [rootSecondFinset, show ∃ q ∈ C.P, G.Adj q C.s from
          ⟨p, hp, hps⟩] using hRootMem
      obtain ⟨i, hi⟩ := eP.surjective ⟨p, hp⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [pToZ_coreBits G.Adj _ _ _ i z i.isLt hz]
      simpa [hLabel, congrArg Subtype.val hi] using hps
    · simp [rootSecondFinset, hReach] at hRootMem

theorem core_true (C : G.LocalConfiguration)
    (eP : Fin 7 ≃ {v : V // v ∈ C.P})
    (eH : Fin 6 ≃ {v : V // v ∈ C.H})
    (eZ : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)})
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (alpha beta : Nat) (hAlphaBeta : alpha + beta ≤ 1)
    (hPZ : edgeCount G C.P (externalTargets G C) = 19)
    (hPH : edgeCount G C.P C.H = 17 - alpha)
    (hPP : edgeCount G C.P C.P = 21 - beta)
    (hHP : 25 ≤ edgeCount G C.H C.P) :
    core alpha beta (graphBits G C eP eH eZ) = true := by
  let bits := graphBits G C eP eH eZ
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr eP).symm
  have hOrP := orientedP_true G C.P C.H (externalTargets G C) eP eH eZ hG
  have hOrPH := orientedPH_true G C.P C.H (externalTargets G C) eP eH eZ hG
  have hZReach := allExternalReached_true G C eP eH eZ
  have hPZNat := totalPToZ_toNat G C.P C.H (externalTargets G C) eP eH eZ hG
  have hPHNat := totalPToH_toNat G C.P C.H (externalTargets G C) eP eH eZ hG
  have hPPNat := totalPOut_toNat G C.P C.H (externalTargets G C) eP eH eZ hG
  have hHPNat := totalHToP_toNat G C.P C.H (externalTargets G C) eP eH eZ
  have hCond := pConditions_true G C eP eH eZ hG hPB hMin hNoSeymour
    hRootDegree (by omega)
  have hSharp := sharpKing_true G C eP eH eZ hG beta (by omega) hPP
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternal := edgeCount_externalTargets G C
  rw [← hExternal, hPZ, hPH, hPP] at hAccounting
  have hExact : exactClassKing bits = true := by
    rcases Nat.eq_zero_or_pos beta with rfl | hBetaPos
    · have hS : (C.P.filter fun p ↦ G.outdegree p = 8).Nonempty := by
        by_contra hEmpty
        rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
        have hNine : ∀ p ∈ C.P, 9 ≤ G.outdegree p := by
          intro p hp
          have hNe : G.outdegree p ≠ 8 := by
            intro he
            have : p ∈ C.P.filter (fun q ↦ G.outdegree q = 8) :=
              Finset.mem_filter.mpr ⟨hp, he⟩
            simp [hEmpty] at this
          have := hMin p
          omega
        have hLower : 63 ≤ ∑ p ∈ C.P, G.outdegree p := by
          calc
            63 = ∑ _p ∈ C.P, 9 := by simp [hPCard]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro p hp
              exact hNine p hp
        omega
      exact exactClassKing_betaZero_true G C eP eH eZ hG hPB hMin
        hNoSeymour hRootDegree (by omega) (by simpa using hPP) hS
    · have hBetaOne : beta = 1 := by omega
      subst beta
      have hAll : ∀ p ∈ C.P, G.outdegree p = 8 := by
        have hSum : ∑ p ∈ C.P, G.outdegree p = 56 := by omega
        exact pointwise_eq_of_sum_eq_card_mul C.P G.outdegree 8
          (fun p hp ↦ hMin p) (by simpa [hPCard] using hSum)
      exact exactClassKing_betaOne_true G C eP eH eZ hG hPB hPZ hAll
  have hPZBool : (totalPToZ bits == 19) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [show (totalPToZ bits).toNat = edgeCount G C.P (externalTargets G C) by
      simpa [bits] using hPZNat, hPZ]
    decide
  have hPHBool : (totalPToH bits == (17 - alpha)) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [show (totalPToH bits).toNat = edgeCount G C.P C.H by
      simpa [bits] using hPHNat, hPH]
    have : alpha ≤ 1 := by omega
    interval_cases alpha <;> decide
  have hPPBool : (totalPOut bits == (21 - beta)) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [show (totalPOut bits).toNat = edgeCount G C.P C.P by
      simpa [bits] using hPPNat, hPP]
    have : beta ≤ 1 := by omega
    interval_cases beta <;> decide
  have hHPBool : (25 : BitVec 8).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (totalHToP bits).toNat = edgeCount G C.H C.P by
      simpa [bits] using hHPNat]
    exact hHP
  simp only [core, Bool.and_eq_true]
  refine ⟨?_, hExact⟩
  refine ⟨?_, hSharp⟩
  refine ⟨?_, hCond⟩
  refine ⟨?_, hHPBool⟩
  refine ⟨?_, hPPBool⟩
  refine ⟨?_, hPHBool⟩
  refine ⟨?_, hPZBool⟩
  refine ⟨?_, hZReach⟩
  exact ⟨hOrP, hOrPH⟩

end SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeBridge
