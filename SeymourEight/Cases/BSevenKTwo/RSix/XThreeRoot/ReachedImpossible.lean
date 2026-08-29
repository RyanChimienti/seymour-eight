import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.Assembly
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.SharpKing
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.ExactClassKing
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.Reached

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XThreeRoot

open RSix.XThreeNoRoot
open Shared Shared.FiniteCore
open Labels Encoding Core GraphFacts Assembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
theorem reached_impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hy : BSevenKTwo.y G C = 1) (hz : C.z = 2) : False := by
  have hPCard : C.P.card = 6 := hr
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  have hReachedCard : (reachedQ G C).card = 1 := hy
  obtain ⟨q, hqReached⟩ :=
    Finset.card_pos.mp (by omega : 0 < (reachedQ G C).card)
  have hqQ : q ∈ C.Q := (Finset.mem_inter.mp hqReached).1
  have hQ : C.Q = {q} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hQCard
    have hqw : q = w := by simpa [hw] using hqQ
    simpa [hqw] using hw
  have hAOneCard : C.A1.card = 2 := hk
  have hXCard : C.X.card = 3 := hx
  have hHCard : C.H.card = 5 := by
    rw [BSevenKTwo.H_card_eq_x_add_two G C hk, hx]
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 2 := by omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hZCard : (externalTargets G C).card = 3 := by
    rw [card_externalTargets G C, hz, hRoot]
  let L := canonicalLabels G C q hqQ hPCard hACard hAOneCard hXCard
    hRCard hHCard hZCard
  let bits : Core.Encoding := Encoding.coreBits G.Adj L
  have hOrA := orientedA_true G C q L hG
  have hOrP := orientedP_true G C q L hG
  have hOrPH := orientedPH_true G C q L hG
  have hFixed := fixedA_true G C q L hG
  have hXReached := everyXReached_true G C q L hk
  have hQReached := qReached_true G C q hqQ hQ L hk hy
  have hZReached := allZReached_true G C q L
  have hThreeNat := three_le_aOneToXCount G C q L hG hPivot hk hx
  have hThree : (3 : BitVec 8).ule (count 6 fun k ↦
      let a := k / 3
      let x := k % 3
      aArc bits (1 + a) (3 + x)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    simpa [bits] using hThreeNat
  have hAMin := aMinimumAndDegree_true G C q hqQ hQ L hG hPivot hMin hk hr
  have hPMin := pMinimumDegree_true G C q hqQ hQ L hG hHCard hMin
  have hANS := aNonSeymour_all_true G C q hqQ hQ L hG hNoSeymour
  have hPNS := pNonSeymour_all_true G C q hqQ hQ L hG hNoSeymour
  have hTight := tightPrivate_true G hBound C q hqQ hQ L hG hNoSeymour
    hk hr hx hy
  have hPOrder := orderedP_true G C q hqQ hQ L hG (by
    intro i
    exact canonicalLabels_p_order G C q hqQ hPCard hACard hAOneCard
      hXCard hRCard hHCard hZCard i)
  have hStructOrder := orderedStructuralClasses_true G C q hqQ hQ L
    (by
      intro i
      exact canonicalLabels_aOne_order G C q hqQ hPCard hACard hAOneCard
        hXCard hRCard hHCard hZCard i)
    (by
      intro i
      exact canonicalLabels_x_order G C q hqQ hPCard hACard hAOneCard
        hXCard hRCard hHCard hZCard i)
    (by
      intro i
      exact canonicalLabels_r_order G C q hqQ hPCard hACard hAOneCard
        hXCard hRCard hHCard hZCard i)
  have hAOneQCap : edgeCount G C.A1 {q} ≤ 2 := by
    have h := edgeCount_le_card_mul_card G C.A1 {q}
    simpa [hAOneCard] using h
  have hHPLowerGraph := H_to_P_lower G C q hqQ hQ hG hMin hk hx hRCard hy
  have hHPUpperGraph := H_to_P_add_missing_le G C q hQ hG hMin hr
    hHCard hZCard
  have hmBound : 24 - edgeCount G C.P ({q} ∪ externalTargets G C) ≤ 5 := by omega
  have hEffective := pEffectiveCondition_true G C q hqQ hQ L hG hMin
    hNoSeymour hHCard hy hmBound
  have hAnyExact := anyExact_true G C q hqQ hQ L hG hMin hk hr
    hx hRCard hy
  have hSharp := sharpKing_of_orientedP bits (by simpa [bits] using hOrP)
  have hExactKing := exactClassKing_of_effective bits
    (by simpa [bits] using hOrP) (by simpa [bits] using hEffective)
    (by simpa [bits] using hAnyExact)
  have hLower : (18 - aOneToQ bits).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub]
    rw [aOneToQ_toNat G C q hqQ L hk,
      totalHToP_toNat G C q L hHCard]
    norm_num [BitVec.toNat_ofNat]
    have hSmall : edgeCount G C.A1 {q} ≤ 18 := hAOneQCap.trans (by omega)
    change ((256 - edgeCount G C.A1 {q} + 18) % 256) ≤ _
    have heq : 256 - edgeCount G C.A1 {q} + 18 =
        256 + (18 - edgeCount G C.A1 {q}) := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
    have hlt : 18 - edgeCount G C.A1 {q} < 256 := by omega
    simpa only [Nat.mod_eq_of_lt hlt] using hHPLowerGraph
  have hUpper : (totalHToP bits + externalMissing bits).ule 21 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [totalHToP_toNat G C q L hHCard,
      externalMissing_toNat G C q L hG hHCard]
    norm_num [BitVec.toNat_ofNat]
    change (edgeCount G C.H C.P +
      (24 - edgeCount G C.P ({q} ∪ externalTargets G C))) % 256 ≤ 21
    have hSmall : edgeCount G C.H C.P +
        (24 - edgeCount G C.P ({q} ∪ externalTargets G C)) < 256 := by omega
    rw [Nat.mod_eq_of_lt hSmall]
    exact hHPUpperGraph
  have hCommon : commonCore bits = true := by
    simp only [commonCore, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨
      (by simpa [bits] using hOrA), (by simpa [bits] using hOrP)⟩,
      (by simpa [bits] using hOrPH)⟩, (by simpa [bits] using hFixed)⟩,
      (by simpa [bits] using hXReached)⟩, (by simpa [bits] using hQReached)⟩,
      (by simpa [bits] using hZReached)⟩, hThree⟩,
      (by simpa [bits] using hAMin)⟩, (by simpa [bits] using hANS)⟩,
      (by simpa [bits] using hPMin)⟩, (by simpa [bits] using hPNS)⟩,
      (by simpa [bits] using hTight)⟩, (by simpa [bits] using hPOrder)⟩,
      (by simpa [bits] using hStructOrder)⟩
  have hCore : core bits = true := by
    simp only [core, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨hCommon,
      (by simpa [bits] using hEffective)⟩, hSharp⟩,
      hExactKing⟩, hLower⟩, hUpper⟩
  have hImpossible := reachedCore_impossible bits
  rw [hCore] at hImpossible
  contradiction

end SeymourEight.BSevenKTwo.RSix.XThreeRoot
