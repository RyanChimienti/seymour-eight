import SeymourEight.Cases.BSevenKTwo.RSeven.XFiveNoRoot.Assembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.AllSlices
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.SuffixBridge

set_option linter.style.header false

/-!
# The no-root `r = 7`, `x = 5` row

The graph hypotheses are transported to a 225-bit finite core.  Six isolated
certificate modules cover the possible exact external defects `m = 0,...,5`.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot

open Shared Labels Core
open RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem impossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2)
    (hr : C.r = 7) (hx : C.x = 5) (hNoRoot : epsilonS G C = 0)
    (hyz : BSevenKTwo.y G C = 0 ∧ C.z = 3) : False := by
  rcases hyz with ⟨hy, hz⟩
  have hPB : C.P = C.B := p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 2 := by
    change C.A1.card = 2 at hk
    exact hk
  have hXCard : C.X.card = 5 := by
    change C.X.card = 5 at hx
    exact hx
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 0 := by omega
  have hRZero : C.R = ∅ := Finset.card_eq_zero.mp hRCard
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : C.Z.card = 3 := by
    change C.Z.card = 3 at hz
    exact hz
  let L := Labels.canonicalLabels G C hPCard hACard hA1Card hXCard
    hHCard hRZero hZCard
  have hPOrder : ∀ q : Fin 6,
      Labels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pKey G C (L.p ⟨q.val, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_p_order G C hPCard hACard hA1Card hXCard
      hHCard hRZero hZCard q
  have hZOrder : ∀ q : Fin 2,
      Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val + 1, by omega⟩).1 ≤
        Labels.zKey G (fun i ↦ (L.p i).1) (L.z ⟨q.val, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_z_order G C hPCard hACard hA1Card hXCard
      hHCard hRZero hZCard q
  have hAOneOrder : Labels.structuralKey G C (L.a 2).1 ≤
      Labels.structuralKey G C (L.a 1).1 :=
    Labels.canonicalLabels_aOne_order G C hPCard hACard hA1Card hXCard
      hHCard hRZero hZCard
  have hXOrder : ∀ q : Fin 4,
      Labels.structuralKey G C (L.a ⟨q.val + 4, by omega⟩).1 ≤
        Labels.structuralKey G C (L.a ⟨q.val + 3, by omega⟩).1 := by
    intro q
    exact Labels.canonicalLabels_x_order G C hPCard hACard hA1Card hXCard
      hHCard hRZero hZCard q
  let bits : Encoding := Encoding.coreBits G.Adj (fun i ↦ (L.p i).1)
    (fun i ↦ (L.a i).1) (fun i ↦ (L.z i).1)
  have hBase : baseCore bits = true := by
    simpa [bits] using Assembly.baseCore_true G hBound C L hG hPB hMin
      hNoSeymour hPivot hk hx hy hNoRoot hPCard hXCard hHCard hRZero hZCard
      hPOrder hZOrder hAOneOrder hXOrder
  have hSuffix := degreeEightSuffix_of_baseCore bits hBase
  have hCore : suffixCore bits = true := by simp [suffixCore, hBase, hSuffix]
  rw [allSlices_impossible bits] at hCore
  exact Bool.noConfusion hCore

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot
