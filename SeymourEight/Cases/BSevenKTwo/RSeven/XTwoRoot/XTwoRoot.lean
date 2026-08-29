import SeymourEight.Cases.BSevenKTwo.RSeven.XTwoRoot.Assembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.Four
import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.Five
import SeymourEight.Certificates.BSevenKTwo.RSeven.XTwo.Six

set_option linter.style.header false

/-!
# The rooted `r = 7`, `x = 2` family

The reached root is combined with `Z` into a four-, five-, or six-element
external-target set. The resulting 225-bit cores, including the fixed
seven-vertex reduction, use the certificates shared by both root statuses.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XTwoRoot

open Shared
open Labels
open XTwoNoRoot.Core
open RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem impossibleAt (zCount : Nat)
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hz : C.z = zCount - 1)
    (hZCases : zCount = 4 ∨ zCount = 5 ∨ zCount = 6) : False := by
  have hPB : C.P = C.B := p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 2 := by
    change C.A1.card = 2 at hk
    exact hk
  have hXCard : C.X.card = 2 := by
    change C.X.card = 2 at hx
    exact hx
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 3 := by omega
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : (externalTargets G C).card = zCount := by
    rw [card_externalTargets G C, hz, hRoot]
    have hzPos : 1 ≤ zCount := by
      rcases hZCases with rfl | rfl | rfl <;> omega
    omega
  have hzLe : zCount ≤ 6 := by
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
  have hXOrder : ∀ q : Fin 1,
      Labels.structuralKey G C (L.a ⟨4 + q.val, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨3 + q.val, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_x_order G zCount C hPCard hACard
      hA1Card hXCard hRCard hHCard hZCard q
  have hROrder : ∀ q : Fin 2,
      Labels.structuralKey G C (L.a ⟨q.val + 6, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 5, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_r_order G zCount C hPCard hACard
      hA1Card hXCard hRCard hHCard hZCard q
  have hCommon := Assembly.commonCore_true G C L hG hMin hNoSeymour hPivot
    hPB hk hXCard hBound hHCard hzLe hPOrder hZOrder hAOneOrder
      hXOrder hROrder
  have hHP := Assembly.nineteen_le_H_to_P G C hG hMin hRootDegree hPivot
    hr hk hx hPB
  have hCapacity := Assembly.H_to_P_add_externalMissing_le_capacity G C hG
    hMin hPB hPCard hZCard hHCard hzLe
  have hmBound : 7 * zCount - edgeCount G C.P (externalTargets G C) ≤ 7 * zCount - 26 := by
    omega
  let bits := XTwoNoRoot.Encoding.coreBits G.Adj (fun i ↦ (L.p i).1)
    (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)
  rcases hZCases with rfl | rfl | rfl
  · have hEffective := Assembly.pEffectiveCondition_true G C L hG hPB hMin
      hNoSeymour hRootDegree hHCard (Or.inl rfl) hmBound
    have hCore := Assembly.smallCore_true_of_components G C L hG hHCard
      (by omega) hCommon hEffective hHP hCapacity
    have hUnsat := XTwoNoRoot.Core.four_impossible bits
    rw [show XTwoNoRoot.Core.smallCore 4 bits = true by simpa [bits] using hCore] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hEffective := Assembly.pEffectiveCondition_true G C L hG hPB hMin
      hNoSeymour hRootDegree hHCard (Or.inr (Or.inl rfl)) hmBound
    have hCore := Assembly.smallCore_true_of_components G C L hG hHCard
      (by omega) hCommon hEffective hHP hCapacity
    have hUnsat := XTwoNoRoot.Core.five_impossible bits
    rw [show XTwoNoRoot.Core.smallCore 5 bits = true by simpa [bits] using hCore] at hUnsat
    exact Bool.noConfusion hUnsat
  · have hEffective := Assembly.pEffectiveCondition_true G C L hG hPB hMin
      hNoSeymour hRootDegree hHCard (Or.inr (Or.inr rfl)) hmBound
    have hCore := Assembly.smallCore_true_of_components G C L hG hHCard
      (by omega) hCommon hEffective hHP hCapacity
    have hUnsat := XTwoNoRoot.Core.six_impossible bits
    rw [show XTwoNoRoot.Core.smallCore 6 bits = true by simpa [bits] using hCore] at hUnsat
    exact Bool.noConfusion hUnsat

theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 2) (hRoot : epsilonS G C = 1)
    (hyz : BSevenKTwo.y G C = 0 ∧ (C.z = 3 ∨ C.z = 4 ∨ C.z = 5)) : False := by
  rcases hyz with ⟨_, hz | hz | hz⟩
  · exact impossibleAt G 4 hBound C hG hMin hNoSeymour hRootDegree hPivot
      hBCard hk hr hx hRoot (by omega) (Or.inl rfl)
  · exact impossibleAt G 5 hBound C hG hMin hNoSeymour hRootDegree hPivot
      hBCard hk hr hx hRoot (by omega) (Or.inr (Or.inl rfl))
  · exact impossibleAt G 6 hBound C hG hMin hNoSeymour hRootDegree hPivot
      hBCard hk hr hx hRoot (by omega) (Or.inr (Or.inr rfl))

end SeymourEight.BSevenKTwo.RSeven.XTwoRoot
