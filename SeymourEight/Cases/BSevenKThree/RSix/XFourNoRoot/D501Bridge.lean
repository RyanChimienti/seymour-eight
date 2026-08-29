import SeymourEight.Cases.BSevenKThree.RSix.XFourNoRoot.StrongDualBridge
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.D501PositiveDefs

set_option linter.style.header false
set_option maxRecDepth 20000

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Bridge

open Labels Encoding Core HDeletion Rigid StrongDual APRigid
open RigidBridge StrongDualBridge
open D501Positive

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 6000000 in
theorem d501Positive_contradiction
    (hCert : ∀ raw pToZ : Nat → Nat → Bool,
      d501PositiveLeaf raw pToZ = false)
    (C : G.LocalConfiguration) (L : Labels G 3 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hCommon : commonCore 1 3 (graphArc G L) (graphPToZ G L) = true)
    (hDelete : hQDeletionConditions (graphArc G L) (graphPToZ G L) = true)
    (hA : aConditions (graphArc G L) = true)
    (hDual : degreeAndDualConditions 1 (graphArc G L) = true)
    (hm : externalMissing 1 3 (graphArc G L) (graphPToZ G L) = 5)
    (hDelta : aMissing (graphArc G L) = 0)
    (hAlpha : alpha 1 (graphArc G L) = 1)
    (hBeta : internalMissing (graphArc G L) = 0) : False := by
  have hARigid := aRigidArc_graph_eq G C L hG hDelta
  have hPRigid := pRigidArc_graph_eq G C L hG hBeta
  have hAPRigid : aRigidArc (pRigidArc (graphArc G L)) = graphArc G L := by
    rw [hPRigid, hARigid]
  have hBase : hDeletionLeaf 5 0 1 0 (graphArc G L)
      (graphPToZ G L) = true := by
    simp [hDeletionLeaf, hCommon, hDelete, hm, hDelta, hAlpha, hBeta]
  have hEligible := eligibleHCount_three_of_alpha_one G C L hG hHCard hA
    hDual hDelta hAlpha
  have hLeaf : d501PositiveLeaf (graphArc G L) (graphPToZ G L) = true := by
    rw [d501PositiveLeaf, hAPRigid, Bool.and_eq_true]
    exact ⟨hBase, by simpa using hEligible⟩
  rw [hCert _ _] at hLeaf
  contradiction

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.D501Bridge
