import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourLowCoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore

open BroadFourCore

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
/-- Full column tie breaking removes the duplicate disjoint matching, leaving
exactly five canonical low-defect `P → Z` patterns. -/
theorem selectedLowPattern_cover (bits : Encoding)
    (hP : orderedP bits = true) (hZ : orderedZ bits = true)
    (hZFull : orderedZFull bits = true)
    (hm : (externalMissing bits).ule 2 = true) :
    any 5 (fun mode => selectedLowPattern (BitVec.ofNat 3 mode) bits) = true := by
  simp only [selectedLowPattern, fullPToZ, pZMissingOne, pZMissingExactly,
    orderedP, pRowKey, orderedZ, orderedZFull, zFullKey, pZIncidenceCode,
    zColumnCode, externalMissing, totalPToZ, pZOut, pToZ, all, any, sumCount,
    pHOut, pOut, directCount, coreArc, pToA, aToP, rToP, hToP, pToH,
    pArc, directedIndex, aArc, count, bitCount] at hP hZ hZFull hm ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowCore
