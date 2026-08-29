import SeymourEight.Cases.BSevenKTwo.RSix.XFourNoRoot.Effective
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.LowUnsat

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.LowCoreBridge

open CertificateBridge Shared Labels
open Core Shared.FiniteCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev bits (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) : Encoding :=
  Bridge.coreBits G.Adj (fun i => (L.p i).1) (fun i => (L.h i).1)
    (fun i => (L.e i).1)

theorem pRowKey_toNat (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (hG : G.IsOriented)
    (hCaptured : ∀ p ∈ C.P, G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ E)
    (hPHE : Disjoint (C.P ∪ C.H) E)
    (p : Nat) (hp : p < 6) :
    (pRowKey (bits G C E L) p).toNat = pKey G C E (L.p ⟨p, hp⟩).1 := by
  have hBlocks := Bridge.pBlockCounts G C.P C.H E L.p L.h L.e hG p hp
  have hDegree : G.outdegree (L.p ⟨p, hp⟩).1 =
      directCount G C.P (L.p ⟨p, hp⟩).1 +
      directCount G C.H (L.p ⟨p, hp⟩).1 +
      directCount G E (L.p ⟨p, hp⟩).1 := by
    have hPH : Disjoint C.P C.H := by
      rw [Finset.disjoint_left]
      intro v hvP hvH
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
        (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have h := outdegree_eq_directCount_of_captured G (C.P ∪ C.H ∪ E)
      (L.p ⟨p, hp⟩).1 (hCaptured _ (L.p ⟨p, hp⟩).2)
    rw [directCount_union_of_disjoint G (C.P ∪ C.H) E _ hPHE,
      directCount_union_of_disjoint G C.P C.H _ hPH] at h
    exact h
  unfold pRowKey pKey
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  norm_num [BitVec.toNat_ofNat]
  change (((pOut (bits G C E L) p).toNat +
      (pHOut (bits G C E L) p).toNat +
      (pEOut (bits G C E L) p).toNat) % 256 * 4096 +
      (pEOut (bits G C E L) p).toNat * 256 +
      (pHOut (bits G C E L) p).toNat * 16 +
      (pOut (bits G C E L) p).toNat) % 65536 = _
  have hpLe : directCount G C.P (L.p ⟨p, hp⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.p).symm)
  have hhLe : directCount G C.H (L.p ⟨p, hp⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.h).symm)
  have heLe : directCount G E (L.p ⟨p, hp⟩).1 ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by
      simpa using (Fintype.card_congr L.e).symm)
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), ← hDegree]
  omega

theorem orderedP_true (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (hG : G.IsOriented)
    (hCaptured : ∀ p ∈ C.P, G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ E)
    (hPHE : Disjoint (C.P ∪ C.H) E)
    (hOrder : ∀ i : Fin 5,
      pKey G C E (L.p ⟨i.val + 1, by omega⟩).1 ≤
        pKey G C E (L.p ⟨i.val, by omega⟩).1) :
    orderedP (bits G C E L) = true := by
  rw [orderedP, Bridge.all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pRowKey_toNat G C E L hG hCaptured hPHE (p + 1) (by omega),
    pRowKey_toNat G C E L hG hCaptured hPHE p (by omega)]
  exact hOrder ⟨p, hp⟩

theorem hPOut_toNat (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (h : Nat) (hh : h < 6) :
    (hPOut (bits G C E L) h).toNat = directCount G C.P (L.h ⟨h, hh⟩).1 := by
  unfold hPOut
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega),
    directCount_eq_sum_fin G C.P L.p]
  apply Finset.sum_congr rfl
  intro p _
  rw [Bridge.hToP_coreBits G.Adj _ _ _ h p hh p.isLt]

theorem incomingP_le_six (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (v : V) :
    (∑ p ∈ C.P, if G.Adj p v then 1 else 0) ≤ 6 := by
  have hCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  calc
    _ ≤ ∑ _p ∈ C.P, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      split <;> omega
    _ = 6 := by simp [hCard]

theorem orderedH_true (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E)
    (hAOrder : RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 1).1 ≤
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 0).1)
    (hXOrder : ∀ i : Fin 3,
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.h ⟨i.val + 3, by omega⟩).1 ≤
        RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.h ⟨i.val + 2, by omega⟩).1) :
    orderedH (bits G C E L) = true := by
  unfold orderedH
  simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
  constructor
  · rw [hPOut_toNat G C E L 1 (by omega), hPOut_toNat G C E L 0 (by omega)]
    change directCount G C.P (L.h 1).1 ≤ directCount G C.P (L.h 0).1
    unfold RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey at hAOrder
    change 16 * directCount G C.P (L.h 1).1 +
        (∑ p ∈ C.P, if G.Adj p (L.h 1).1 then 1 else 0) ≤
      16 * directCount G C.P (L.h 0).1 +
        (∑ p ∈ C.P, if G.Adj p (L.h 0).1 then 1 else 0) at hAOrder
    have hIn0 := incomingP_le_six G C E L (L.h 0).1
    have hIn1 := incomingP_le_six G C E L (L.h 1).1
    omega
  · rw [Bridge.all_eq_true_iff]
    intro i hi
    simp only [decide_eq_true_eq]
    rw [hPOut_toNat G C E L (3 + i) (by omega),
      hPOut_toNat G C E L (2 + i) (by omega)]
    have hKey := hXOrder ⟨i, hi⟩
    unfold RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey at hKey
    change 16 * directCount G C.P (L.h ⟨i + 3, by omega⟩).1 +
          (∑ p ∈ C.P, if G.Adj p (L.h ⟨i + 3, by omega⟩).1 then 1 else 0) ≤
        16 * directCount G C.P (L.h ⟨i + 2, by omega⟩).1 +
          (∑ p ∈ C.P, if G.Adj p (L.h ⟨i + 2, by omega⟩).1 then 1 else 0)
      at hKey
    have hIn0 := incomingP_le_six G C E L (L.h ⟨i + 2, by omega⟩).1
    have hIn1 := incomingP_le_six G C E L (L.h ⟨i + 3, by omega⟩).1
    have hOut : directCount G C.P (L.h ⟨i + 3, by omega⟩).1 ≤
        directCount G C.P (L.h ⟨i + 2, by omega⟩).1 := by omega
    simpa [Nat.add_comm] using hOut

theorem orderedZ_true (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E)
    (hOrder : eIncoming G (fun i => (L.p i).1) (L.e 2).1 ≤
      eIncoming G (fun i => (L.p i).1) (L.e 1).1) :
    orderedZ (bits G C E L) = true := by
  simp only [orderedZ, BitVec.ule_eq_decide, decide_eq_true_eq, ePIn]
  rw [Bridge.toNat_count_eq_fin_sum 6 _ (by omega),
    Bridge.toNat_count_eq_fin_sum 6 _ (by omega)]
  simp only [bits]
  simpa [eIncoming] using hOrder

theorem case_false (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hE : E = auxiliarySet G C)
    (hCaptured : ∀ p ∈ C.P, G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ E)
    (hEight : ∀ p ∈ C.P, 8 ≤ (directAuxEffectiveUnion G C E p).card)
    (c m alpha beta : Nat) (hc : c ≤ 2) (hm : m ≤ 1)
    (hdefect : m + alpha + beta ≤ c)
    (hHP : 21 ≤ edgeCount G C.H C.P + c)
    (hPE : edgeCount G C.P E = 18 - m)
    (hPH : edgeCount G C.P C.H = 15 + c - alpha)
    (hPP : edgeCount G C.P C.P = 15 - beta)
    (hPOrder : ∀ i : Fin 5,
      pKey G C E (L.p ⟨i.val + 1, by omega⟩).1 ≤
        pKey G C E (L.p ⟨i.val, by omega⟩).1)
    (hAOrder : RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 1).1 ≤
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 0).1)
    (hXOrder : ∀ i : Fin 3,
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.h ⟨i.val + 3, by omega⟩).1 ≤
        RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.h ⟨i.val + 2, by omega⟩).1)
    (hEOrder : eIncoming G (fun i => (L.p i).1) (L.e 2).1 ≤
      eIncoming G (fun i => (L.p i).1) (L.e 1).1) : False := by
  let b := bits G C E L
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [Finset.disjoint_left]
    intro v hvPH hvE
    rcases Finset.mem_union.mp hvPH with hvP | hvH
    · have hvAux := hE ▸ hvE
      rcases Finset.mem_union.mp hvAux with hvQ | hvZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
          (Finset.mem_inter.mp hvQ).1
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by
              simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
          · simp [rootSecondFinset, hReach] at hvRoot
    · have hvAux := hE ▸ hvE
      rcases Finset.mem_union.mp hvAux with hvQ | hvZ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C
            (Finset.mem_inter.mp hvQ).1)
      · rcases Finset.mem_union.mp hvZ with hvZ | hvRoot
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
        · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
          · have hvs : v = C.s := by
              simpa [rootSecondFinset, hReach] using hvRoot
            subst v
            exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
              (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
          · simp [rootSecondFinset, hReach] at hvRoot
  have hPELower : 17 ≤ edgeCount G C.P E := by omega
  have hOP := orderedP_true G C E L hG hCaptured hPHE hPOrder
  have hOH := orderedH_true G C E L hAOrder hXOrder
  have hOZ := orderedZ_true G C E L hEOrder
  have hOr := Bridge.orientedBasic_true G C.P C.H E L.p L.h L.e hG
  have hPCond := pConditions_true_of_effective_eight G C E L hG hMin
    hNoSeymour hE hPELower hCaptured hEight
  have hHPb : (21 : BitVec 8).ule (totalHP b + c) = true := by
    dsimp [b, bits]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
      BitVec.toNat_add]
    rw [Bridge.totalHP_toNat G C.P C.H E L.p L.h L.e]
    have hCap := edgeCount_le_card_mul_card G C.H C.P
    have hHCard : C.H.card = 6 := by simpa using (Fintype.card_congr L.h).symm
    have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    rw [hHCard, hPCard] at hCap
    norm_num [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hHP
  have hPELowerB : (17 : BitVec 8).ule (totalPE b) = true := by
    dsimp [b, bits]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Bridge.totalPE_toNat G C.P C.H E L.p L.h L.e hG]
    exact hPELower
  have hPEb : (totalPE b == (18 - m)) = true := by
    dsimp [b, bits]
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [Bridge.totalPE_toNat G C.P C.H E L.p L.h L.e hG, hPE]
    interval_cases m <;> norm_num [BitVec.toNat_ofNat]
  have hPHb : (totalPH b == (15 + c - alpha)) = true := by
    dsimp [b, bits]
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [Bridge.totalPH_toNat G C.P C.H E L.p L.h L.e hG, hPH]
    have haLe : alpha ≤ 2 := by omega
    interval_cases c <;> interval_cases alpha <;>
      norm_num [BitVec.toNat_ofNat]
  have hPPb : (totalPP b == (15 - beta)) = true := by
    dsimp [b, bits]
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [Bridge.totalPP_toNat G C.P C.H E L.p L.h L.e hG, hPP]
    have hbLe : beta ≤ 2 := by omega
    interval_cases beta <;> norm_num [BitVec.toNat_ofNat]
  have hCore : coreCase c m alpha beta b = true := by
    dsimp [b, bits] at hOP hOH hOZ hOr hPCond hHPb hPELowerB hPEb hPHb hPPb ⊢
    simp only [coreCase, coreAt, Bool.and_eq_true]
    aesop
  rw [low_case_unsat c m alpha beta hc hm hdefect b] at hCore
  contradiction

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.LowCoreBridge
