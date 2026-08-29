import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.RigidBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.APRigidDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.EligibleConsequence
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.DualCases

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDualBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts DefectBridge
  Assembly RigidBridge
open StrongDual APRigid
open HDeletion

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem dualHDeletionLeaf_true (C : G.LocalConfiguration) (L : Labels G 3 C)
    (m delta alphaValue betaValue etaValue hqValue crossValue : Nat)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true)
    (hDelete : hQDeletionConditions (graphArc G L) (graphPToZ G L) = true)
    (hm : externalMissing 1 3 (graphArc G L) (graphPToZ G L) =
      BitVec.ofNat 8 m)
    (hDelta : aMissing (graphArc G L) = BitVec.ofNat 8 delta)
    (hAlpha : alpha 1 (graphArc G L) = BitVec.ofNat 8 alphaValue)
    (hBeta : internalMissing (graphArc G L) = BitVec.ofNat 8 betaValue)
    (hEta : etaH (graphArc G L) = BitVec.ofNat 8 etaValue)
    (hQ : hQDefect 1 (graphArc G L) = BitVec.ofNat 8 hqValue)
    (hCross : crossMissing (graphArc G L) = BitVec.ofNat 8 crossValue) :
    dualHDeletionLeaf m delta alphaValue betaValue etaValue hqValue crossValue
      (graphArc G L) (graphPToZ G L) = true := by
  simp [dualHDeletionLeaf, hDeletionLeaf, hCommon, hDelete, hm, hDelta,
    hAlpha, hBeta, hEta, hQ, hCross]

/-- The isolated counting certificate supplies the redundant eligible-H
lower bound used by the larger dual certificates. -/
theorem eligibleHCount_lower_true (arc : Nat → Nat → Bool)
    (hA : aConditions arc = true)
    (etaValue hqValue lower : Nat)
    (hEta : etaH arc = BitVec.ofNat 8 etaValue)
    (hQ : hQDefect 1 arc = BitVec.ofNat 8 hqValue)
    (hSum : etaValue + hqValue + lower = 7)
    (hSmall : etaValue < 256) (hqSmall : hqValue < 256)
    (hlowerSmall : lower < 256) :
    (BitVec.ofNat 8 lower).ule (eligibleHCount arc) = true := by
  have h := eligibleConsequence_true arc
  rw [eligibleConsequence, hA, Bool.not_true, Bool.false_or, hEta, hQ] at h
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h ⊢
  norm_num [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSmall,
    Nat.mod_eq_of_lt hqSmall, Nat.mod_eq_of_lt hlowerSmall] at h ⊢
  rw [Nat.mod_eq_of_lt (by omega : etaValue + hqValue < 256)] at h
  have hSeven : (7 : BitVec 8).toNat = 7 := by decide
  rw [hSeven] at h
  have hSub : 256 - hqValue + (256 - etaValue + 7) = 512 + lower := by
    omega
  rw [hSub, Nat.add_mod] at h
  norm_num [Nat.mod_eq_of_lt hlowerSmall] at h
  omega

theorem etaH_le_49_true (arc : Nat → Nat → Bool)
    (hA : aConditions arc = true) : (etaH arc).ule 49 = true := by
  have h := etaBoundConsequence_true arc
  simpa [etaBoundConsequence, hA] using h

theorem crossMissing_toNat_le_42
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7) :
    (crossMissing (graphArc G L)).toNat ≤ 42 := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hCrossBound := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCrossBound
  have hFortyTwo : (42 : BitVec 8).toNat = 42 := by decide
  have hPLe : totalPToH (graphArc G L) ≤ (42 : BitVec 8) := by
    rw [BitVec.le_def, totalPToH_toNat G C L hG hHCard, hFortyTwo]
    omega
  have hFirstNat : ((42 : BitVec 8) - totalPToH (graphArc G L)).toNat =
      42 - edgeCount G C.P C.H := by
    rw [BitVec.toNat_sub_of_le hPLe,
      totalPToH_toNat G C L hG hHCard, hFortyTwo]
  have hHLe : totalHToP (graphArc G L) ≤
      (42 : BitVec 8) - totalPToH (graphArc G L) := by
    rw [BitVec.le_def, totalHToP_toNat G C L hHCard, hFirstNat]
    omega
  rw [crossMissing, BitVec.toNat_sub_of_le hHLe, hFirstNat,
    totalHToP_toNat G C L hHCard]
  omega

theorem dual_cases_of_alpha_one
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlpha : alpha 1 (graphArc G L) = 1) :
    ((etaH (graphArc G L) = 4 ∧ hQDefect 1 (graphArc G L) = 0 ∧
      crossMissing (graphArc G L) = 0) ∨
    (etaH (graphArc G L) = 3 ∧ hQDefect 1 (graphArc G L) = 1 ∧
      crossMissing (graphArc G L) = 0)) ∨
    (etaH (graphArc G L) = 3 ∧ hQDefect 1 (graphArc G L) = 0 ∧
      crossMissing (graphArc G L) = 1) := by
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true] at hDualParts
  have hEtaLower : (3 : BitVec 8).ule (etaH (graphArc G L)) = true := by
    simpa [hDelta] using hDualParts.1.2
  have hEtaUpper := etaH_le_49_true (graphArc G L) hA
  have hQNat := hQDefect_toNat_le_seven (graphArc G L)
  have hQUpper : (hQDefect 1 (graphArc G L)).ule 7 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hQNat
  have hCrossNat := crossMissing_toNat_le_42 G C L hG hHCard
  have hCrossUpper : (crossMissing (graphArc G L)).ule 42 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hCrossNat
  have hSum : etaH (graphArc G L) + hQDefect 1 (graphArc G L) +
      crossMissing (graphArc G L) = 4 := by
    have hEq := hDualParts.2
    have hEq' : (4 : BitVec 8) = etaH (graphArc G L) +
        hQDefect 1 (graphArc G L) + crossMissing (graphArc G L) := by
      simpa [hDelta, hAlpha, Nat.reduceAdd, Nat.reduceMul] using hEq
    exact hEq'.symm
  have hCases := DualCases.alphaOneCases_true (etaH (graphArc G L))
    (hQDefect 1 (graphArc G L)) (crossMissing (graphArc G L))
  rw [DualCases.alphaOneCases, hEtaLower, hEtaUpper, hQUpper,
    hCrossUpper, hSum] at hCases
  norm_num at hCases
  rcases hCases with (h1 | h2) | h3
  · exact Or.inl (Or.inl ⟨h1.1.1, h1.1.2, h1.2⟩)
  · exact Or.inl (Or.inr ⟨h2.1.1, h2.1.2, h2.2⟩)
  · exact Or.inr ⟨h3.1.1, h3.1.2, h3.2⟩

theorem dual_cases_of_alpha_two
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlpha : alpha 1 (graphArc G L) = 2) :
    (((((etaH (graphArc G L) = 5 ∧ hQDefect 1 (graphArc G L) = 0 ∧
      crossMissing (graphArc G L) = 0) ∨
    (etaH (graphArc G L) = 4 ∧ hQDefect 1 (graphArc G L) = 1 ∧
      crossMissing (graphArc G L) = 0)) ∨
    (etaH (graphArc G L) = 4 ∧ hQDefect 1 (graphArc G L) = 0 ∧
      crossMissing (graphArc G L) = 1)) ∨
    (etaH (graphArc G L) = 3 ∧ hQDefect 1 (graphArc G L) = 2 ∧
      crossMissing (graphArc G L) = 0)) ∨
    (etaH (graphArc G L) = 3 ∧ hQDefect 1 (graphArc G L) = 1 ∧
      crossMissing (graphArc G L) = 1)) ∨
    (etaH (graphArc G L) = 3 ∧ hQDefect 1 (graphArc G L) = 0 ∧
      crossMissing (graphArc G L) = 2) := by
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true] at hDualParts
  have hEtaLower : (3 : BitVec 8).ule (etaH (graphArc G L)) = true := by
    simpa [hDelta] using hDualParts.1.2
  have hEtaUpper := etaH_le_49_true (graphArc G L) hA
  have hQNat := hQDefect_toNat_le_seven (graphArc G L)
  have hQUpper : (hQDefect 1 (graphArc G L)).ule 7 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hQNat
  have hCrossNat := crossMissing_toNat_le_42 G C L hG hHCard
  have hCrossUpper : (crossMissing (graphArc G L)).ule 42 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hCrossNat
  have hSum : etaH (graphArc G L) + hQDefect 1 (graphArc G L) +
      crossMissing (graphArc G L) = 5 := by
    have hEq := hDualParts.2
    have hEq' : (5 : BitVec 8) = etaH (graphArc G L) +
        hQDefect 1 (graphArc G L) + crossMissing (graphArc G L) := by
      simpa [hDelta, hAlpha, Nat.reduceAdd, Nat.reduceMul] using hEq
    exact hEq'.symm
  have hCases := DualCases.alphaTwoCases_true (etaH (graphArc G L))
    (hQDefect 1 (graphArc G L)) (crossMissing (graphArc G L))
  rw [DualCases.alphaTwoCases, hEtaLower, hEtaUpper, hQUpper,
    hCrossUpper, hSum] at hCases
  norm_num at hCases
  rcases hCases with ((((h1 | h2) | h3) | h4) | h5) | h6
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨h1.1.1, h1.1.2, h1.2⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨h2.1.1, h2.1.2, h2.2⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr
      ⟨h3.1.1, h3.1.2, h3.2⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨h4.1.1, h4.1.2, h4.2⟩))
  · exact Or.inl (Or.inr ⟨h5.1.1, h5.1.2, h5.2⟩)
  · exact Or.inr ⟨h6.1.1, h6.1.2, h6.2⟩

inductive AlphaThreeDualCase (eta hq cross : BitVec 8) : Prop where
  | e6q0 : eta = 6 → hq = 0 → cross = 0 → AlphaThreeDualCase eta hq cross
  | e5q1 : eta = 5 → hq = 1 → cross = 0 → AlphaThreeDualCase eta hq cross
  | e4q2 : eta = 4 → hq = 2 → cross = 0 → AlphaThreeDualCase eta hq cross
  | e3q3 : eta = 3 → hq = 3 → cross = 0 → AlphaThreeDualCase eta hq cross
  | e5q0c1 : eta = 5 → hq = 0 → cross = 1 → AlphaThreeDualCase eta hq cross
  | e4q1c1 : eta = 4 → hq = 1 → cross = 1 → AlphaThreeDualCase eta hq cross
  | e3q2c1 : eta = 3 → hq = 2 → cross = 1 → AlphaThreeDualCase eta hq cross
  | e4q0c2 : eta = 4 → hq = 0 → cross = 2 → AlphaThreeDualCase eta hq cross
  | e3q1c2 : eta = 3 → hq = 1 → cross = 2 → AlphaThreeDualCase eta hq cross
  | e3q0c3 : eta = 3 → hq = 0 → cross = 3 → AlphaThreeDualCase eta hq cross

theorem dual_cross_cases_of_alpha_three
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlpha : alpha 1 (graphArc G L) = 3) :
    AlphaThreeDualCase (etaH (graphArc G L))
      (hQDefect 1 (graphArc G L)) (crossMissing (graphArc G L)) := by
  have hDualParts := hDual
  simp only [degreeAndDualConditions, Bool.and_eq_true] at hDualParts
  have hEtaLower : (3 : BitVec 8).ule (etaH (graphArc G L)) = true := by
    simpa [hDelta] using hDualParts.1.2
  have hEtaUpper := etaH_le_49_true (graphArc G L) hA
  have hQNat := hQDefect_toNat_le_seven (graphArc G L)
  have hQUpper : (hQDefect 1 (graphArc G L)).ule 7 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hQNat
  have hCrossNat := crossMissing_toNat_le_42 G C L hG hHCard
  have hCrossUpper : (crossMissing (graphArc G L)).ule 42 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    exact hCrossNat
  have hSum : etaH (graphArc G L) + hQDefect 1 (graphArc G L) +
      crossMissing (graphArc G L) = 6 := by
    have hEq := hDualParts.2
    have hEq' : (6 : BitVec 8) = etaH (graphArc G L) +
        hQDefect 1 (graphArc G L) + crossMissing (graphArc G L) := by
      simpa [hDelta, hAlpha, Nat.reduceAdd, Nat.reduceMul] using hEq
    exact hEq'.symm
  have hCases := DualCases.alphaThreeCases_true (etaH (graphArc G L))
    (hQDefect 1 (graphArc G L)) (crossMissing (graphArc G L))
  rw [DualCases.alphaThreeCases, hEtaLower, hEtaUpper, hQUpper,
    hCrossUpper, hSum] at hCases
  norm_num at hCases
  rcases hCases with (((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) |
      h8) | h9) | h10)
  · exact .e6q0 h1.1.1 h1.1.2 h1.2
  · exact .e5q1 h2.1.1 h2.1.2 h2.2
  · exact .e4q2 h3.1.1 h3.1.2 h3.2
  · exact .e3q3 h4.1.1 h4.1.2 h4.2
  · exact .e5q0c1 h5.1.1 h5.1.2 h5.2
  · exact .e4q1c1 h6.1.1 h6.1.2 h6.2
  · exact .e3q2c1 h7.1.1 h7.1.2 h7.2
  · exact .e4q0c2 h8.1.1 h8.1.2 h8.2
  · exact .e3q1c2 h9.1.1 h9.1.2 h9.2
  · exact .e3q0c3 h10.1.1 h10.1.2 h10.2

theorem eligibleHCount_three_of_alpha_one
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlpha : alpha 1 (graphArc G L) = 1) :
    (3 : BitVec 8).ule (eligibleHCount (graphArc G L)) = true := by
  have hCases := dual_cases_of_alpha_one G C L hG hHCard hA hDual
    hDelta hAlpha
  rcases hCases with (hCase | hCase) | hCase
  · exact eligibleHCount_lower_true (graphArc G L) hA 4 0 3
      hCase.1 hCase.2.1 rfl (by omega) (by omega) (by omega)
  · exact eligibleHCount_lower_true (graphArc G L) hA 3 1 3
      hCase.1 hCase.2.1 rfl (by omega) (by omega) (by omega)
  · have hFour := eligibleHCount_lower_true (graphArc G L) hA 3 0 4
      hCase.1 hCase.2.1 rfl (by omega) (by omega) (by omega)
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at hFour ⊢
    norm_num [BitVec.toNat_ofNat] at hFour ⊢
    have hThree : (3 : BitVec 8).toNat = 3 := by decide
    rw [hThree]
    omega

theorem eligibleHCount_two_of_alpha_two
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlpha : alpha 1 (graphArc G L) = 2) :
    (2 : BitVec 8).ule (eligibleHCount (graphArc G L)) = true := by
  have lowerTwo (etaValue qValue lower : Nat)
      (hEta : etaH (graphArc G L) = BitVec.ofNat 8 etaValue)
      (hQ : hQDefect 1 (graphArc G L) = BitVec.ofNat 8 qValue)
      (hSum : etaValue + qValue + lower = 7)
      (hLower : 2 ≤ lower) :
      (2 : BitVec 8).ule (eligibleHCount (graphArc G L)) = true := by
    have h := eligibleHCount_lower_true (graphArc G L) hA etaValue qValue
      lower hEta hQ hSum (by omega) (by omega) (by omega)
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at h ⊢
    change lower % 256 ≤ (eligibleHCount (graphArc G L)).toNat at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    change 2 ≤ (eligibleHCount (graphArc G L)).toNat
    omega
  have hCases := dual_cases_of_alpha_two G C L hG hHCard hA hDual
    hDelta hAlpha
  rcases hCases with (((((hCase | hCase) | hCase) | hCase) | hCase) | hCase)
  · exact lowerTwo 5 0 2 hCase.1 hCase.2.1 rfl (by omega)
  · exact lowerTwo 4 1 2 hCase.1 hCase.2.1 rfl (by omega)
  · exact lowerTwo 4 0 3 hCase.1 hCase.2.1 rfl (by omega)
  · exact lowerTwo 3 2 2 hCase.1 hCase.2.1 rfl (by omega)
  · exact lowerTwo 3 1 3 hCase.1 hCase.2.1 rfl (by omega)
  · exact lowerTwo 3 0 4 hCase.1 hCase.2.1 rfl (by omega)

theorem cross_edgeCount_eq_max_of_crossMissing_zero
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hCross : crossMissing (graphArc G L) = 0) :
    edgeCount G C.P C.H + edgeCount G C.H C.P = 42 := by
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hCrossBound := cross_edgeCount_add_reverse_le G C.P C.H hG
  rw [hPCard, hHCard] at hCrossBound
  have hFortyTwo : (42 : BitVec 8).toNat = 42 := by decide
  have hPLe : totalPToH (graphArc G L) ≤ (42 : BitVec 8) := by
    rw [BitVec.le_def, totalPToH_toNat G C L hG hHCard]
    rw [hFortyTwo]
    omega
  have hFirstNat : ((42 : BitVec 8) - totalPToH (graphArc G L)).toNat =
      42 - edgeCount G C.P C.H := by
    rw [BitVec.toNat_sub_of_le hPLe,
      totalPToH_toNat G C L hG hHCard]
    rw [hFortyTwo]
  have hHLe : totalHToP (graphArc G L) ≤
      (42 : BitVec 8) - totalPToH (graphArc G L) := by
    rw [BitVec.le_def, totalHToP_toNat G C L hHCard, hFirstNat]
    omega
  have hCrossNat : (crossMissing (graphArc G L)).toNat = 0 := by
    rw [hCross]
    decide
  rw [crossMissing, BitVec.toNat_sub_of_le hHLe, hFirstNat,
    totalHToP_toNat G C L hHCard] at hCrossNat
  omega

theorem rigidArc_graph_eq_of_defects
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hQ : hQDefect 1 (graphArc G L) = 0)
    (hCross : crossMissing (graphArc G L) = 0)
    (hMissing : aMissing (graphArc G L) = 0) :
    Rigid.rigidArc (graphArc G L) = graphArc G L := by
  apply RigidBridge.rigidArc_eq_of_agreement
  apply Rigid.rigidPremise_agrees
  have hFixed := fixedAOne_true G C L hG
  have hNoP := noPToAOne_true G C L hG
  have hQComplete := RigidBridge.hQComplete_true G L hQ
  have hCrossMax := cross_edgeCount_eq_max_of_crossMissing_zero G C L
    hG hHCard hCross
  have hHP := RigidBridge.hpDirectionsComplete_true G C L hG hHCard hCrossMax
  have hA := RigidBridge.aDirectionsComplete_true G C L hG hMissing
  simp [Rigid.rigidPremise, Rigid.alphaZeroPremise, hFixed, hNoP,
    hQComplete, hHP, hA]

/-- When `beta=0`, the six P vertices induce a tournament, so one Boolean
per unordered pair reconstructs the whole P block. -/
theorem pRigidArc_graph_eq (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented)
    (hMissing : internalMissing (graphArc G L) = 0) :
    pRigidArc (graphArc G L) = graphArc G L := by
  have hMissingNat : (internalMissing (graphArc G L)).toNat = 0 := by
    rw [hMissing]
    decide
  rw [internalMissing_toNat G C L hG] at hMissingNat
  have hPCard : C.P.card = 6 := by
    simpa using (Fintype.card_congr L.p).symm
  have hEdges : edgeCount G C.P C.P = C.P.card.choose 2 := by
    have hCap := internal_edgeCount_le_choose_two G C.P hG
    rw [hPCard]
    norm_num [Nat.choose]
    rw [hPCard] at hCap
    norm_num [Nat.choose] at hCap
    omega
  funext i j
  simp only [pRigidArc]
  split <;> rename_i hBlock
  · rcases hBlock with ⟨hi8, hi14, hj8, hj14⟩
    split <;> rename_i hij
    · subst j
      have hLoop := hG.1 (L.p ⟨i - 8, by omega⟩).1
      have hLoopArc : graphArc G L i i =
          decide (G.Adj (L.p ⟨i - 8, by omega⟩).1
            (L.p ⟨i - 8, by omega⟩).1) := by
        simpa [pArc, Nat.add_sub_of_le hi8] using
          (pArc_graph G L (i - 8) (i - 8) (by omega) (by omega))
      rw [hLoopArc]
      exact (decide_eq_false_iff_not.mpr hLoop).symm
    split <;> rename_i hlt
    · rfl
    · have hji : j < i := by omega
      let pi : Fin 6 := ⟨i - 8, by omega⟩
      let pj : Fin 6 := ⟨j - 8, by omega⟩
      have hNe : (L.p pi).1 ≠ (L.p pj).1 := by
        intro hEq
        have hFin : pi = pj := L.p.injective (Subtype.ext hEq)
        have : i - 8 = j - 8 := congrArg Fin.val hFin
        omega
      have hPair :=
        SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.complete_of_internal_edgeCount_max
          G C.P hG hEdges (L.p pi).2 (L.p pj).2 hNe
      have hForwardArc : graphArc G L i j =
          decide (G.Adj (L.p pi).1 (L.p pj).1) := by
        simpa [pArc, pi, pj, Nat.add_sub_of_le hi8,
          Nat.add_sub_of_le hj8] using
            (pArc_graph G L (i - 8) (j - 8) (by omega) (by omega))
      have hReverseArc : graphArc G L j i =
          decide (G.Adj (L.p pj).1 (L.p pi).1) := by
        simpa [pArc, pi, pj, Nat.add_sub_of_le hi8,
          Nat.add_sub_of_le hj8] using
            (pArc_graph G L (j - 8) (i - 8) (by omega) (by omega))
      rw [hForwardArc, hReverseArc]
      rcases hPair with hForward | hReverse
      · have hNot := hG.2 hForward
        simp [hForward, hNot]
      · have hNot := hG.2 hReverse
        simp [hReverse, hNot]
  · rfl

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDualBridge
