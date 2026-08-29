import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.HardAuxBridge
import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.HardEffectiveBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.HardBroad
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.HardDerived

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardBridge

open Labels Encoding EasyBridge HardAuxBridge HardEffectiveBridge
open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem contradiction (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (hk : C.k = 3) (hr : C.r = 6) (hx : C.x = 2)
    (hy : BSevenKThree.y G C = 1) : False := by
  let arc := graphArc G L
  let pToZ := graphPToZ G L
  let auxArc := graphAuxArc G C L hMin
  have hEasy : easyCore 5 true arc pToZ = true :=
    core_true G C L hG hMin hNoSeymour hPivot hk hr (by omega) (by omega) true
      (by simpa using hy)
  have hDerived := arithmetic_consequences arc pToZ hEasy
  have hHCard : C.H.card = 5 := by
    rw [Digraph.LocalConfiguration.H,
      Finset.card_union_of_disjoint
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)]
    change C.k + C.x = 5
    omega
  have hmBound : (externalMissing arc pToZ).toNat ≤ 11 := by
    simpa [BitVec.ule_eq_decide] using hDerived.2.2.2.2
  have hEffective : (all 6 fun p ↦ pEffective arc pToZ p) = true :=
    pEffective_true G C L hG hMin hNoSeymour hHCard hy hmBound
  have hExact : auxiliaryExact auxArc = true :=
    auxiliaryExact_true G C L hG hMin
  have hOriented : auxiliaryOriented arc pToZ auxArc = true :=
    auxiliaryOriented_true G C L hG hMin
  have hFull : fullNonSeymour arc pToZ auxArc = true :=
    fullNonSeymour_true G C L hG hMin hNoSeymour
  have hHall : fullHallConditions arc pToZ auxArc = true :=
    fullHallConditions_true G C L hG hMin hNoSeymour
  have hCommon : commonCore arc pToZ auxArc = true := by
    simp only [commonCore, hEasy, hDerived.1, hDerived.2.1,
      hDerived.2.2.1, hDerived.2.2.2.1, hEffective, hExact, hOriented, hFull, hHall,
      Bool.and_true]
  rw [hard_broad_false arc pToZ auxArc] at hCommon
  contradiction

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.HardBridge
