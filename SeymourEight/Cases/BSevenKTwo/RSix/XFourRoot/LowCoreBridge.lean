import SeymourEight.Cases.BSevenKTwo.RSix.XFourRoot.Effective
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourRoot.CTwoMTwo

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XFourRoot.LowCoreBridge

open CertificateBridge Shared Shared.FiniteCore
open RSix.XFourNoRoot RSix.XFourNoRoot.Core RSix.XFourNoRoot.Bridge
open RSix.XFourNoRoot.Labels
open RSix.XFourRoot.Core

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem caseTwo_false (C : G.LocalConfiguration) (E : Finset V)
    (L : LowLabels G C E) (hG : G.IsOriented)
    (hE : E = auxiliarySet G C)
    (hCaptured : ∀ p ∈ C.P, G.outNeighborFinset p ⊆ C.P ∪ C.H ∪ E)
    (hPCond : rootPConditions
      (RSix.XFourNoRoot.LowCoreBridge.bits G C E L) = true)
    (hHP : 19 ≤ edgeCount G C.H C.P)
    (hPE : edgeCount G C.P E = 16)
    (hPH : edgeCount G C.P C.H = 17)
    (hPP : edgeCount G C.P C.P = 15)
    (hPOrder : ∀ i : Fin 5,
      RSix.XFourNoRoot.Labels.pKey G C E (L.p ⟨i.val + 1, by omega⟩).1 ≤
        RSix.XFourNoRoot.Labels.pKey G C E (L.p ⟨i.val, by omega⟩).1)
    (hAOrder : RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 1).1 ≤
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C (L.h 0).1)
    (hXOrder : ∀ i : Fin 3,
      RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.h ⟨i.val + 3, by omega⟩).1 ≤
        RSeven.XFourNoRoot.BroadFourLabels.hDegreeKey G C
          (L.h ⟨i.val + 2, by omega⟩).1)
    (hEOrder : RSix.XFourNoRoot.Labels.eIncoming G
        (fun i => (L.p i).1) (L.e 2).1 ≤
      RSix.XFourNoRoot.Labels.eIncoming G
        (fun i => (L.p i).1) (L.e 1).1) : False := by
  let b := RSix.XFourNoRoot.LowCoreBridge.bits G C E L
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [Finset.disjoint_left]
    intro v hvPH hvE
    have hvAux : v ∈ auxiliarySet G C := hE.symm ▸ hvE
    rcases Finset.mem_union.mp hvPH with hvP | hvH
    · rcases Finset.mem_union.mp hvAux with hvQ | hvExternal
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hvP
          (Finset.mem_inter.mp hvQ).1
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_B_externalTargets G C))
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP) hvExternal
    · rcases Finset.mem_union.mp hvAux with hvQ | hvExternal
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (Digraph.LocalConfiguration.H_subset_A (G := G) C hvH)
          (Digraph.LocalConfiguration.Q_subset_B (G := G) C
            (Finset.mem_inter.mp hvQ).1)
      · exact (Finset.disjoint_left.mp (BSixKThree.disjoint_H_externalTargets G C hG))
          hvH hvExternal
  have hOP := RSix.XFourNoRoot.LowCoreBridge.orderedP_true G C E L hG
    hCaptured hPHE hPOrder
  have hOH := RSix.XFourNoRoot.LowCoreBridge.orderedH_true G C E L
    hAOrder hXOrder
  have hOZ := RSix.XFourNoRoot.LowCoreBridge.orderedZ_true G C E L hEOrder
  have hOr := Bridge.orientedBasic_true G C.P C.H E L.p L.h L.e hG
  have hHPb : (21 : BitVec 8).ule (totalHP b + 2) = true := by
    dsimp [b, RSix.XFourNoRoot.LowCoreBridge.bits]
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
      BitVec.toNat_add]
    rw [Bridge.totalHP_toNat G C.P C.H E L.p L.h L.e]
    have hCap := edgeCount_le_card_mul_card G C.H C.P
    have hHCard : C.H.card = 6 := by simpa using (Fintype.card_congr L.h).symm
    have hPCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    rw [hHCard, hPCard] at hCap
    norm_num [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hPEb : (totalPE b == 16) = true := by
    dsimp [b, RSix.XFourNoRoot.LowCoreBridge.bits]
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [Bridge.totalPE_toNat G C.P C.H E L.p L.h L.e hG, hPE]
    decide
  have hPHb : (totalPH b == 17) = true := by
    dsimp [b, RSix.XFourNoRoot.LowCoreBridge.bits]
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [Bridge.totalPH_toNat G C.P C.H E L.p L.h L.e hG, hPH]
    decide
  have hPPb : (totalPP b == 15) = true := by
    dsimp [b, RSix.XFourNoRoot.LowCoreBridge.bits]
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [Bridge.totalPP_toNat G C.P C.H E L.p L.h L.e hG, hPP]
    decide
  have hCore : rootCoreCase 2 2 0 0 b = true := by
    dsimp [b, RSix.XFourNoRoot.LowCoreBridge.bits] at hOP hOH hOZ hOr hPCond hHPb hPEb hPHb hPPb ⊢
    simp only [rootCoreCase, rootCoreAt, Bool.and_eq_true]
    aesop
  rw [cTwo_mTwo_aZero_bZero_unsat b] at hCore
  contradiction

end SeymourEight.BSevenKTwo.RSix.XFourRoot.LowCoreBridge
