import SeymourEight.Cases.BSevenKTwo.RSeven.XThreeNoRoot.Assembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XThree.Three
import SeymourEight.Certificates.BSevenKTwo.RSeven.XThree.Four
import SeymourEight.Certificates.BSevenKTwo.RSeven.XThree.Five

set_option linter.style.header false

/-!
# The no-root `r = 7`, `x = 3` family

The graph hypotheses are transported to one common 225-bit encoding.  The
three possible sizes of `Z` are discharged by their corresponding
`bv_decide` certificates.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot

open Shared
open Labels Core
open RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem impossibleAt (zCount : Nat)
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = zCount)
    (hZCases : zCount = 3 ∨ zCount = 4 ∨ zCount = 5) : False := by
  have hPB : C.P = C.B := p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 2 := by
    change C.A1.card = 2 at hk
    exact hk
  have hXCard : C.X.card = 3 := by
    change C.X.card = 3 at hx
    exact hx
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 2 := by omega
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : C.Z.card = zCount := by
    change C.Z.card = zCount at hz
    exact hz
  have hzLe : zCount ≤ 5 := by
    rcases hZCases with rfl | rfl | rfl <;> omega
  let L := Labels.canonicalLabels G zCount C hPCard hACard hA1Card
    hXCard hRCard hHCard hZCard
  have hPOrder : ∀ q : Fin 6,
      Labels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pKey G C (L.p ⟨q.val, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_p_order G zCount C hPCard hACard hA1Card
      hXCard hRCard hHCard hZCard q
  have hZOrder : ∀ q : Fin (zCount - 1),
      Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
        Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_z_order G zCount C hPCard hACard hA1Card
      hXCard hRCard hHCard hZCard q
  have hAOneOrder : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨q.val + 2, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 1, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_aOne_order G zCount C hPCard hACard
      hA1Card hXCard hRCard hHCard hZCard q
  have hXOrder : ∀ q : Fin 2,
      Labels.structuralKey G C (L.a ⟨4 + q.val, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨3 + q.val, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_x_order G zCount C hPCard hACard
      hA1Card hXCard hRCard hHCard hZCard q
  have hROrder : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨q.val + 7, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 6, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_r_order G zCount C hPCard hACard
      hA1Card hXCard hRCard hHCard hZCard q
  have hCommon := Assembly.commonCore_true G C L hG hMin hNoSeymour hPivot
    hPB hk hXCard hNoRoot hHCard hzLe hPOrder hZOrder hAOneOrder hXOrder hROrder
  have hHP := Assembly.twentyOne_le_H_to_P G C hG hMin hRootDegree hk hx hy hPB
  have hCapacity := Assembly.H_to_P_add_externalMissing_le_capacity G C hG
    hMin hPB hNoRoot hPCard hZCard hHCard hzLe
  have hmBound : 7 * zCount - edgeCount G C.P C.Z ≤ 7 * zCount - 21 := by
    omega
  let bits := Encoding.coreBits G.Adj (fun i ↦ (L.p i).1)
    (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)
  rcases hZCases with rfl | rfl | rfl
  · have hEffective := Assembly.pEffectiveCondition_true G C L hG hPB hMin
      hNoSeymour hNoRoot hHCard (Or.inl rfl) hmBound
    have hCore := Assembly.smallCore_true_of_components G C L hG hHCard
      (by omega) hCommon hEffective hHP hCapacity
    have hUnsat := Core.three_impossible bits
    rw [show Core.smallCore 3 bits = true by simpa [bits] using hCore] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hEffective := Assembly.pEffectiveCondition_true G C L hG hPB hMin
      hNoSeymour hNoRoot hHCard (Or.inr (Or.inl rfl)) hmBound
    have hCore := Assembly.smallCore_true_of_components G C L hG hHCard
      (by omega) hCommon hEffective hHP hCapacity
    have hUnsat := Core.four_impossible bits
    rw [show Core.smallCore 4 bits = true by simpa [bits] using hCore] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hEffective := Assembly.pEffectiveConditionFive_true G C L hG hPB hMin
      hNoSeymour hNoRoot hHCard hmBound
    have hCore := Assembly.fiveCore_true_of_components G C L hG hHCard
      hCommon hEffective hHP (by simpa using hCapacity)
    have hUnsat := Core.five_impossible bits
    rw [show Core.fiveCore bits = true by simpa [bits] using hCore] at hUnsat
    exact Bool.noConfusion hUnsat

theorem impossible
    (_hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 3) (hNoRoot : epsilonS G C = 0)
    (hyz : BSevenKTwo.y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5)) : False := by
  rcases hyz with ⟨hy, hz | hz | hz⟩
  · exact impossibleAt G 3 C hG hMin hNoSeymour hRootDegree hPivot hBCard
      hk hr hx hNoRoot hy hz (Or.inl rfl)
  · exact impossibleAt G 4 C hG hMin hNoSeymour hRootDegree hPivot hBCard
      hk hr hx hNoRoot hy hz (Or.inr (Or.inl rfl))
  · exact impossibleAt G 5 C hG hMin hNoSeymour hRootDegree hPivot hBCard
      hk hr hx hNoRoot hy hz (Or.inr (Or.inr rfl))

end SeymourEight.BSevenKTwo.RSeven.XThreeNoRoot
