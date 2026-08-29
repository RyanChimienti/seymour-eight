import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.ZThreeLowAssembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeSimpleLabelsAlphaZeroBetaZero
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeSimpleLabelsAlphaZeroBetaOne
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeSimpleLabelsAlphaOneBetaZero

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# External-defect-two assembly for three `Z` vertices

The two missing incidences have three orbits under vertex relabeling.  The
canonical graph labels select one representative of those orbits and sort
only within the stabilizer blocks, so a single certificate per genuine
degree-defect leaf suffices.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeMtwoBridge

open CertificateBridge Shared
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeCore
open SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeLabels
open SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeBridge
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeBridge
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeLowCore
open SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeLowBridge
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeNormalization
open FiveZExactGraphBridge
open SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
open XFourNoRoot.ZThreeSimpleLabels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (C : G.LocalConfiguration) (L : Labels G C) :
    Encoding := XFourNoRoot.ZThreeBridge.coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.h i).1)
      (fun i ↦ (L.z i).1)

theorem simpleRowsOrdered_true (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (_hZCard : (externalTargets G C).card = 3) (start countRows : Nat)
    (hEnd : start + countRows < 7)
    (hKey : ∀ i : Fin countRows,
      pLowKey G C (L.p ⟨start + i.val, by have := i.isLt; omega⟩).1 ≥
        pLowKey G C
          (L.p ⟨start + i.val + 1, by have := i.isLt; omega⟩).1)
    (hSame : ∀ i : Fin countRows,
      directCount G (externalTargets G C)
          (L.p ⟨start + i.val, by have := i.isLt; omega⟩).1 =
        directCount G (externalTargets G C)
          (L.p ⟨start + i.val + 1, by have := i.isLt; omega⟩).1) :
    simpleRowsOrdered (graphBits G C L) start countRows = true := by
  let bits := graphBits G C L
  rw [simpleRowsOrdered, XFourNoRoot.ZThreeBridge.all_eq_true_iff]
  intro i hi
  let left := start + i
  let right := start + i + 1
  have hKL := hKey ⟨i, hi⟩
  have hS := hSame ⟨i, hi⟩
  have hKL' : pLowKey G C (L.p ⟨left, by dsimp [left]; omega⟩).1 ≥
      pLowKey G C (L.p ⟨right, by dsimp [right]; omega⟩).1 := by
    simpa [left, right] using hKL
  have hS' : directCount G (externalTargets G C)
      (L.p ⟨left, by dsimp [left]; omega⟩).1 = directCount G (externalTargets G C)
      (L.p ⟨right, by dsimp [right]; omega⟩).1 := by
    simpa [left, right] using hS
  have hDL := pDegree_toNat G C L.p L.h L.z hG hPB left (by
    dsimp [left]; omega)
  have hDR := pDegree_toNat G C L.p L.h L.z hG hPB right (by
    dsimp [right]; omega)
  have hBL := pBlockCounts G C.P C.H (externalTargets G C) L.p L.h L.z hG left (by
    dsimp [left]; omega)
  have hBR := pBlockCounts G C.P C.H (externalTargets G C) L.p L.h L.z hG right (by
    dsimp [right]; omega)
  have hPL : directCount G C.P (L.p ⟨left, by dsimp [left]; omega⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hPR : directCount G C.P (L.p ⟨right, by dsimp [right]; omega⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHL : directCount G C.H (L.p ⟨left, by dsimp [left]; omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hHR : directCount G C.H (L.p ⟨right, by dsimp [right]; omega⟩).1 ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  unfold pLowKey pExternalDefect at hKL'
  have hDegLe : G.outdegree (L.p ⟨right, by dsimp [right]; omega⟩).1 ≤
      G.outdegree (L.p ⟨left, by dsimp [left]; omega⟩).1 := by omega
  have hDegBool : (pDegree bits right).ule (pDegree bits left) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [show (pDegree bits right).toNat =
          G.outdegree (L.p ⟨right, by dsimp [right]; omega⟩).1 by
        simpa [bits] using hDR,
      show (pDegree bits left).toNat =
          G.outdegree (L.p ⟨left, by dsimp [left]; omega⟩).1 by
        simpa [bits] using hDL]
    exact hDegLe
  rw [Bool.and_eq_true]
  refine ⟨hDegBool, ?_⟩
  by_cases hDegEq : pDegree bits left == pDegree bits right
  · rw [if_pos hDegEq, Bool.and_eq_true]
    have hDegEqNat := congrArg BitVec.toNat (beq_iff_eq.mp hDegEq)
    rw [show (pDegree bits left).toNat =
          G.outdegree (L.p ⟨left, by dsimp [left]; omega⟩).1 by
        simpa [bits] using hDL,
      show (pDegree bits right).toNat =
          G.outdegree (L.p ⟨right, by dsimp [right]; omega⟩).1 by
        simpa [bits] using hDR] at hDegEqNat
    have hPLe : directCount G C.P
        (L.p ⟨right, by dsimp [right]; omega⟩).1 ≤
        directCount G C.P
          (L.p ⟨left, by dsimp [left]; omega⟩).1 := by omega
    have hPBool : (pOut bits right).ule (pOut bits left) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [show (pOut bits right).toNat = directCount G C.P
            (L.p ⟨right, by dsimp [right]; omega⟩).1 by
          simpa [bits] using hBR.1,
        show (pOut bits left).toNat = directCount G C.P
            (L.p ⟨left, by dsimp [left]; omega⟩).1 by
          simpa [bits] using hBL.1]
      exact hPLe
    refine ⟨hPBool, ?_⟩
    by_cases hPEq : pOut bits left == pOut bits right
    · rw [if_pos hPEq]
      have hPEqNat := congrArg BitVec.toNat (beq_iff_eq.mp hPEq)
      rw [show (pOut bits left).toNat = directCount G C.P
            (L.p ⟨left, by dsimp [left]; omega⟩).1 by
          simpa [bits] using hBL.1,
        show (pOut bits right).toNat = directCount G C.P
            (L.p ⟨right, by dsimp [right]; omega⟩).1 by
          simpa [bits] using hBR.1] at hPEqNat
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [show (pHOut bits right).toNat = directCount G C.H
            (L.p ⟨right, by dsimp [right]; omega⟩).1 by
          simpa [bits] using hBR.2.1,
        show (pHOut bits left).toNat = directCount G C.H
            (L.p ⟨left, by dsimp [left]; omega⟩).1 by
          simpa [bits] using hBL.2.1]
      omega
    · rw [if_neg hPEq]
  · rw [if_neg hDegEq]

private theorem directZ_eq_two_left (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (p : Nat) (hp : p < 7)
    (hPat : pZPattern (graphBits G C L) p false true true = true) :
    directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 = 2 := by
  have hBlocks := pBlockCounts G C.P C.H (externalTargets G C) L.p L.h L.z hG p hp
  have hBits : pZOut (graphBits G C L) p = 2 := by
    simp only [pZPattern, Bool.and_eq_true] at hPat
    rcases hPat with ⟨⟨h0, h1⟩, h2⟩
    simp only [beq_iff_eq] at h0 h1 h2
    simp [pZOut, count, h0, h1, h2, bitCount]
  rw [← hBlocks.2.2, hBits]
  decide

private theorem directZ_eq_two_middle (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (p : Nat) (hp : p < 7)
    (hPat : pZPattern (graphBits G C L) p true false true = true) :
    directCount G (externalTargets G C) (L.p ⟨p, hp⟩).1 = 2 := by
  have hBlocks := pBlockCounts G C.P C.H (externalTargets G C) L.p L.h L.z hG p hp
  have hBits : pZOut (graphBits G C L) p = 2 := by
    simp only [pZPattern, Bool.and_eq_true] at hPat
    rcases hPat with ⟨⟨h0, h1⟩, h2⟩
    simp only [beq_iff_eq] at h0 h1 h2
    simp [pZOut, count, h0, h1, h2, bitCount]
  rw [← hBlocks.2.2, hBits]
  decide

private theorem canonicalKeyBlock (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) (start countRows : Nat)
    (hEnd : start + countRows < 7) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    ∀ i : Fin countRows,
      pLowKey G C (L.p ⟨start + i.val, by have := i.isLt; omega⟩).1 ≥
        pLowKey G C
          (L.p ⟨start + i.val + 1, by have := i.isLt; omega⟩).1 := by
  let L := canonicalLabels G C hPCard hHCard hZCard
  change ∀ i : Fin countRows,
    pLowKey G C (L.p ⟨start + i.val, by have := i.isLt; omega⟩).1 ≥
      pLowKey G C
        (L.p ⟨start + i.val + 1, by have := i.isLt; omega⟩).1
  intro i
  exact canonicalLabels_p_key_anti G C hPCard hHCard hZCard
    (i := ⟨start + i.val, by have := i.isLt; omega⟩)
    (j := ⟨start + i.val + 1, by have := i.isLt; omega⟩)
    (Fin.mk_le_mk.mpr (by omega))

theorem simpleLabels_of_externalOrbit (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPCard : C.P.card = 7) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) (orbit : Nat) (hOrbit : orbit ≤ 2) :
    let L := canonicalLabels G C hPCard hHCard hZCard
    externalOrbit orbit (graphBits G C L) = true →
      simpleLabels orbit (graphBits G C L) = true := by
  let L := canonicalLabels G C hPCard hHCard hZCard
  let bits := graphBits G C L
  change externalOrbit orbit bits = true → simpleLabels orbit bits = true
  intro hExternal
  have hH : XFourNoRoot.ZThreeLowCore.orderedH bits = true := by
    have := ZThreeLowBridge.orderedH_true G C hPCard hHCard hZCard
    simpa [bits, L] using this
  have hHLex : all 5 (fun h ↦
      lexGe 14 (phColumnBit bits h) (phColumnBit bits (h + 1))) = true := by
    simpa [XFourNoRoot.ZThreeLowCore.orderedH] using hH
  interval_cases orbit
  · have hTail : ∀ q < 6,
        pZPattern bits (q + 1) true true true = true := by
      rw [externalOrbit, if_pos rfl, Bool.and_eq_true] at hExternal
      simpa only [XFourNoRoot.ZThreeBridge.all_eq_true_iff] using hExternal.2
    have hSame : ∀ i : Fin 5,
        directCount G (externalTargets G C) (L.p ⟨1 + i.val, by omega⟩).1 =
          directCount G (externalTargets G C) (L.p ⟨1 + i.val + 1, by omega⟩).1 := by
      intro i
      have hPatLeft : pZPattern bits (1 + i.val) true true true = true := by
        simpa [Nat.add_comm] using hTail i.val (by omega)
      have hLeft := ZThreeLowBridge.directZ_eq_three_of_pattern G C L hG
        (1 + i.val) (by omega) (by simpa [bits] using hPatLeft)
      have hPatRight :
          pZPattern bits (1 + i.val + 1) true true true = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hTail (i.val + 1) (by omega)
      have hRight := ZThreeLowBridge.directZ_eq_three_of_pattern G C L hG
        (1 + i.val + 1) (by omega) (by simpa [bits] using hPatRight)
      omega
    have hRows := simpleRowsOrdered_true G C L hG hPB hPCard
      hHCard hZCard 1 5 (by omega)
      (by simpa [L] using
        (canonicalKeyBlock G C hPCard hHCard hZCard 1 5 (by omega))) hSame
    have hRows' : simpleRowsOrdered bits 1 5 = true := by
      simpa [bits] using hRows
    simp [simpleLabels, hRows', hHLex]
  · norm_num [externalOrbit, Bool.and_eq_true] at hExternal
    rcases hExternal with ⟨⟨hDef0, hDef1⟩, hTailBool⟩
    have hTail : ∀ q < 5,
        pZPattern bits (q + 2) true true true = true := by
      simpa only [XFourNoRoot.ZThreeBridge.all_eq_true_iff] using hTailBool
    have hDefSame : ∀ _i : Fin 1,
        directCount G (externalTargets G C) (L.p 0).1 = directCount G (externalTargets G C) (L.p 1).1 := by
      intro _i
      have h0 := directZ_eq_two_left G C L hG 0 (by omega)
        (by simpa [bits] using hDef0)
      have h1 := directZ_eq_two_left G C L hG 1 (by omega)
        (by simpa [bits] using hDef1)
      exact h0.trans h1.symm
    have hSatSame : ∀ i : Fin 4,
        directCount G (externalTargets G C) (L.p ⟨2 + i.val, by omega⟩).1 =
          directCount G (externalTargets G C) (L.p ⟨2 + i.val + 1, by omega⟩).1 := by
      intro i
      have hPatLeft : pZPattern bits (2 + i.val) true true true = true := by
        simpa [Nat.add_comm] using hTail i.val (by omega)
      have hLeft := ZThreeLowBridge.directZ_eq_three_of_pattern G C L hG
        (2 + i.val) (by omega) (by simpa [bits] using hPatLeft)
      have hPatRight :
          pZPattern bits (2 + i.val + 1) true true true = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hTail (i.val + 1) (by omega)
      have hRight := ZThreeLowBridge.directZ_eq_three_of_pattern G C L hG
        (2 + i.val + 1) (by omega) (by simpa [bits] using hPatRight)
      omega
    have hDefRows := simpleRowsOrdered_true G C L hG hPB hPCard
      hHCard hZCard 0 1 (by omega)
      (by simpa [L] using
        (canonicalKeyBlock G C hPCard hHCard hZCard 0 1 (by omega)))
      (by simpa using hDefSame)
    have hSatRows := simpleRowsOrdered_true G C L hG hPB hPCard
      hHCard hZCard 2 4 (by omega)
      (by simpa [L] using
        (canonicalKeyBlock G C hPCard hHCard hZCard 2 4 (by omega))) hSatSame
    have hDefRows' : simpleRowsOrdered bits 0 1 = true := by
      simpa [bits] using hDefRows
    have hSatRows' : simpleRowsOrdered bits 2 4 = true := by
      simpa [bits] using hSatRows
    simp [simpleLabels, hDefRows', hSatRows', hHLex]
  · norm_num [externalOrbit, Bool.and_eq_true] at hExternal
    rcases hExternal with ⟨⟨hDef0, hDef1⟩, hTailBool⟩
    have hTail : ∀ q < 5,
        pZPattern bits (q + 2) true true true = true := by
      simpa only [XFourNoRoot.ZThreeBridge.all_eq_true_iff] using hTailBool
    have hDefSame : ∀ _i : Fin 1,
        directCount G (externalTargets G C) (L.p 0).1 = directCount G (externalTargets G C) (L.p 1).1 := by
      intro _i
      have h0 := directZ_eq_two_left G C L hG 0 (by omega)
        (by simpa [bits] using hDef0)
      have h1 := directZ_eq_two_middle G C L hG 1 (by omega)
        (by simpa [bits] using hDef1)
      exact h0.trans h1.symm
    have hSatSame : ∀ i : Fin 4,
        directCount G (externalTargets G C) (L.p ⟨2 + i.val, by omega⟩).1 =
          directCount G (externalTargets G C) (L.p ⟨2 + i.val + 1, by omega⟩).1 := by
      intro i
      have hPatLeft : pZPattern bits (2 + i.val) true true true = true := by
        simpa [Nat.add_comm] using hTail i.val (by omega)
      have hLeft := ZThreeLowBridge.directZ_eq_three_of_pattern G C L hG
        (2 + i.val) (by omega) (by simpa [bits] using hPatLeft)
      have hPatRight :
          pZPattern bits (2 + i.val + 1) true true true = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hTail (i.val + 1) (by omega)
      have hRight := ZThreeLowBridge.directZ_eq_three_of_pattern G C L hG
        (2 + i.val + 1) (by omega) (by simpa [bits] using hPatRight)
      omega
    have hDefRows := simpleRowsOrdered_true G C L hG hPB hPCard
      hHCard hZCard 0 1 (by omega)
      (by simpa [L] using
        (canonicalKeyBlock G C hPCard hHCard hZCard 0 1 (by omega)))
      (by simpa using hDefSame)
    have hSatRows := simpleRowsOrdered_true G C L hG hPB hPCard
      hHCard hZCard 2 4 (by omega)
      (by simpa [L] using
        (canonicalKeyBlock G C hPCard hHCard hZCard 2 4 (by omega))) hSatSame
    have hDefRows' : simpleRowsOrdered bits 0 1 = true := by
      simpa [bits] using hDefRows
    have hSatRows' : simpleRowsOrdered bits 2 4 = true := by
      simpa [bits] using hSatRows
    simp [simpleLabels, hDefRows', hSatRows', hHLex]

theorem zThree_defectTwo_impossible
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (_hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 4) (hRoot : epsilonS G C = 1)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 2)
    (hDefect : 21 - edgeCount G C.P (externalTargets G C) = 2) : False := by
  have hPB : C.P = C.B :=
    XFourNoRoot.RepeatedSharedOmissionBridge.p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : (externalTargets G C).card = 3 := by
    rw [card_externalTargets G C, hz, hRoot]
  have hPZLe : edgeCount G C.P (externalTargets G C) ≤ 21 := by
    exact (edgeCount_le_card_mul_card G C.P (externalTargets G C)).trans_eq (by
      rw [hPCard, hZCard])
  have hPZ : edgeCount G C.P (externalTargets G C) = 19 := by omega
  have hHP : 25 ≤ edgeCount G C.H C.P :=
    twentyFive_le_H_to_P G C hG hMin hRootDegree hk hx hy hPB
  have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCross
  have hPHLe : edgeCount G C.P C.H ≤ 17 := by omega
  have hPPLe : edgeCount G C.P C.P ≤ 21 := by
    have hInternal := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard] at hInternal
    norm_num [Nat.choose] at hInternal
    exact hInternal
  let alpha := 17 - edgeCount G C.P C.H
  let beta := 21 - edgeCount G C.P C.P
  have hPH : edgeCount G C.P C.H = 17 - alpha := by
    dsimp [alpha]
    omega
  have hPP : edgeCount G C.P C.P = 21 - beta := by
    dsimp [beta]
    omega
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hExternal := edgeCount_externalTargets G C
  rw [← hExternal, hPZ, hPH, hPP] at hAccounting
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hAlphaBeta : alpha + beta ≤ 1 := by omega
  let L := canonicalLabels G C hPCard hHCard hZCard
  let bits := graphBits G C L
  have hCore : core alpha beta bits = true := by
    simpa [bits] using ZThreeBridge.core_true G C L.p L.h L.z hG hPB hMin
      hNoSeymour hRootDegree alpha beta hAlphaBeta hPZ hPH hPP hHP
  have hTotal : (totalPToZ bits == 19) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    have hNat := totalPToZ_toNat G C.P C.H (externalTargets G C) L.p L.h L.z hG
    rw [show (totalPToZ bits).toNat = edgeCount G C.P (externalTargets G C) by
      simpa [bits] using hNat, hPZ]
    decide
  have hRows : orderedExternalRows bits = true := by
    have := ZThreeLowBridge.orderedExternalRows_true G C hG hPB
      hPCard hHCard hZCard
    simpa [bits, L] using this
  have hZOrder : orderedExternalZ bits = true := by
    have := ZThreeLowBridge.orderedExternalZ_true G C hPCard hHCard hZCard
    simpa [bits, L] using this
  have hOrbits := externalOrbit_of_ordered bits hTotal hRows hZOrder
  have hCombined :
      ((externalOrbit 0 bits && simpleLabels 0 bits) ||
        (externalOrbit 1 bits && simpleLabels 1 bits) ||
        (externalOrbit 2 bits && simpleLabels 2 bits)) = true := by
    by_cases h0 : externalOrbit 0 bits = true
    · have hLabel0 : simpleLabels 0 bits = true := by
        simpa [bits, L] using
          (simpleLabels_of_externalOrbit G C hG hPB hPCard hHCard
            hZCard 0 (by omega) (by simpa [bits] using h0))
      simp [h0, hLabel0]
    · by_cases h1 : externalOrbit 1 bits = true
      · have hLabel1 : simpleLabels 1 bits = true := by
          simpa [bits, L] using
            (simpleLabels_of_externalOrbit G C hG hPB hPCard hHCard
              hZCard 1 (by omega) (by simpa [bits] using h1))
        simp [h1, hLabel1]
      · have h2 : externalOrbit 2 bits = true := by
          simpa [h0, h1] using hOrbits
        have hLabel2 : simpleLabels 2 bits = true := by
          simpa [bits, L] using
            (simpleLabels_of_externalOrbit G C hG hPB hPCard hHCard
              hZCard 2 (by omega) (by simpa [bits] using h2))
        simp [h2, hLabel2]
  have hWitness : (core alpha beta bits &&
      ((externalOrbit 0 bits && simpleLabels 0 bits) ||
       (externalOrbit 1 bits && simpleLabels 1 bits) ||
       (externalOrbit 2 bits && simpleLabels 2 bits))) = true := by
    rw [Bool.and_eq_true]
    exact ⟨hCore, hCombined⟩
  have hAlpha : alpha ≤ 1 := by omega
  have hBeta : beta ≤ 1 := by omega
  interval_cases alpha <;> interval_cases beta
  · have hUnsat := XFourNoRoot.ZThreeSimpleLabels.alphaZeroBetaZero_unsat bits
    rw [hWitness] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hUnsat := XFourNoRoot.ZThreeSimpleLabels.alphaZeroBetaOne_unsat bits
    rw [hWitness] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hUnsat := XFourNoRoot.ZThreeSimpleLabels.alphaOneBetaZero_unsat bits
    rw [hWitness] at hUnsat
    exact Bool.noConfusion hUnsat
  · omega

end SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeMtwoBridge
