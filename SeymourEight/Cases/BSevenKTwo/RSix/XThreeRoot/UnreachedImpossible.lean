import SeymourEight.Cases.BSevenKTwo.RSix.XThreeRoot.UnreachedAssembly
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.SharpKing
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.ExactClassKing
import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.Unreached

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XThreeRoot

open RSix.XThreeNoRoot
open Shared Shared.FiniteCore
open Labels UnreachedEncoding Core UnreachedCore UnreachedAssembly

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
theorem unreached_impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 6) (hx : C.x = 3) (hRoot : epsilonS G C = 1)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 3) : False := by
  have hPCard : C.P.card = 6 := hr
  have hQCard : C.Q.card = 1 := by
    have h := Digraph.LocalConfiguration.card_B_eq_r_add_card_Q (G := G) C
    omega
  obtain ⟨q, hqQ⟩ := Finset.card_pos.mp (by omega : 0 < C.Q.card)
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
  have hZCard : (externalTargets G C).card = 4 := by
    rw [card_externalTargets G C, hz, hRoot]
  let L := canonicalUnreachedLabels G C q hqQ hPCard hACard hAOneCard
    hXCard hRCard hHCard hZCard
  let bits : Core.Encoding := UnreachedEncoding.coreBits G.Adj L
  have hOrA := UnreachedAssembly.orientedA_true G C q L hG
  have hOrP := UnreachedAssembly.orientedP_true G C q L hG
  have hOrPH := UnreachedAssembly.orientedPH_true G C q L hG
  have hFixed := UnreachedAssembly.fixedA_true G C q L hG
  have hXReached := UnreachedAssembly.everyXReached_true G C q L hk
  have hZReached := UnreachedAssembly.allZReached_true G C q L
  have hQStructure := UnreachedAssembly.qStructure_true G C q hqQ L hy
  have hThreeNat := UnreachedAssembly.three_le_aOneToXCount
    G C q L hG hPivot hk hx
  have hThree : (3 : BitVec 8).ule (count 6 fun k ↦
      let a := k / 3
      let x := k % 3
      Core.aArc bits (1 + a) (3 + x)) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    simpa [bits] using hThreeNat
  have hAMin := UnreachedAssembly.aMinimumAndDegree_true
    G C q hqQ hQ L hG hPivot hMin hk hr
  have hPMin := UnreachedAssembly.pMinimumDegree_true
    G C q hqQ hQ L hG hHCard hMin hy
  have hANS := UnreachedAssembly.aNonSeymour_all_true
    G C q hqQ hQ L hG hNoSeymour hy
  have hPNS := UnreachedAssembly.pNonSeymour_all_true
    G C q hqQ hQ L hG hNoSeymour hy
  have hTightNative := UnreachedAssembly.tightPrivate_true G hBound C q hqQ hQ L
    hG hNoSeymour hk hr hx hy
  have hTight : Core.tightPrivate bits = true := by
    rw [← UnreachedCore.tightPrivate_eq_core_of_qStructure bits
      (by simpa [bits] using hQStructure)]
    simpa [bits] using hTightNative
  have hPOrder := UnreachedAssembly.orderedP_true G C q hqQ hQ L hG hy (by
    intro i
    exact canonicalUnreachedLabels_p_order G C q hqQ hPCard hACard
      hAOneCard hXCard hRCard hHCard hZCard i)
  have hStructOrder := UnreachedAssembly.orderedStructuralClasses_true
    G C q hqQ hQ L
    (by
      intro i
      exact canonicalUnreachedLabels_aOne_order G C q hqQ hPCard hACard
        hAOneCard hXCard hRCard hHCard hZCard i)
    (by
      intro i
      exact canonicalUnreachedLabels_x_order G C q hqQ hPCard hACard
        hAOneCard hXCard hRCard hHCard hZCard i)
    (by
      intro i
      exact canonicalUnreachedLabels_r_order G C q hqQ hPCard hACard
        hAOneCard hXCard hRCard hHCard hZCard i)
  have hHPLowerGraph := UnreachedAssembly.H_to_P_lower
    G C q hQ hG hMin hk hx hRCard hy
  have hHPUpperGraph := UnreachedAssembly.H_to_P_add_missing_le
    G C hG hMin hr hHCard hZCard hy
  have hmBound : 24 - edgeCount G C.P (externalTargets G C) ≤ 5 := by omega
  have hEffective := UnreachedAssembly.pEffectiveCondition_true
    G C q hqQ hQ L hG hMin hNoSeymour hHCard hy hmBound
  have hAnyExact := UnreachedAssembly.anyExact_true
    G C q hqQ hQ L hG hMin hk hr hx hRCard hy
  have hSharp := sharpKing_of_orientedP bits (by simpa [bits] using hOrP)
  have hExactKing := exactClassKing_of_effective bits
    (by simpa [bits] using hOrP) (by simpa [bits] using hEffective)
    (by simpa [bits] using hAnyExact)
  have hLower : (18 : BitVec 8).ule (Core.totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [UnreachedAssembly.totalHToP_toNat G C q L hHCard]
    exact hHPLowerGraph
  have hUpper : (Core.totalHToP bits + Core.externalMissing bits).ule 21 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [UnreachedAssembly.totalHToP_toNat G C q L hHCard,
      UnreachedAssembly.externalMissing_toNat G C q L hG hHCard]
    norm_num [BitVec.toNat_ofNat]
    have hSmall : edgeCount G C.H C.P +
        (24 - edgeCount G C.P (externalTargets G C)) < 256 := by omega
    rw [Nat.mod_eq_of_lt hSmall]
    exact hHPUpperGraph
  have hCommon : UnreachedCore.commonCore bits = true := by
    simp only [UnreachedCore.commonCore, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨
      (by simpa [bits] using hOrA), (by simpa [bits] using hOrP)⟩,
      (by simpa [bits] using hOrPH)⟩, (by simpa [bits] using hFixed)⟩,
      (by simpa [bits] using hXReached)⟩,
      (by simpa [bits] using hZReached)⟩,
      (by simpa [bits] using hQStructure)⟩, hThree⟩,
      (by simpa [bits] using hAMin)⟩, (by simpa [bits] using hANS)⟩,
      (by simpa [bits] using hPMin)⟩, (by simpa [bits] using hPNS)⟩,
      (by simpa [bits] using hTight)⟩, (by simpa [bits] using hPOrder)⟩,
      (by simpa [bits] using hStructOrder)⟩
  have hCore : UnreachedCore.core bits = true := by
    simp only [UnreachedCore.core, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨hCommon,
      (by simpa [bits] using hEffective)⟩, hSharp⟩,
      hExactKing⟩, hLower⟩, hUpper⟩
  have hImpossible := UnreachedCore.unreachedCore_impossible bits
  rw [hCore] at hImpossible
  contradiction

end SeymourEight.BSevenKTwo.RSix.XThreeRoot
