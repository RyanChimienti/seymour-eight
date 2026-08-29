import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A0B0
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A0B1
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A0B2
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A0B3
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A1B0
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A1B1
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.A1B2

namespace SeymourEight.ThreeZFullCore

theorem core_unsat (alpha beta : Nat) (hDefects : alpha + beta ≤ 3)
    (hAlpha : alpha ≤ 1)
    (hCertified : alpha + beta ≤ 2 ∨ 2 ≤ beta)
    (bits : BitVec 119) :
    core bits (BitVec.ofNat 8 alpha) (BitVec.ofNat 8 (21 - beta))
      (BitVec.ofNat 8 (59 - alpha - beta)) = false := by
  have ha : alpha = 0 ∨ alpha = 1 := by omega
  rcases ha with rfl | rfl
  · have hb : beta = 0 ∨ beta = 1 ∨ beta = 2 ∨ beta = 3 := by omega
    rcases hb with rfl | rfl | rfl | rfl
    · exact a0_b0_unsat bits
    · exact a0_b1_unsat bits
    · exact a0_b2_unsat bits
    · exact a0_b3_unsat bits
  · have hb : beta = 0 ∨ beta = 1 ∨ beta = 2 := by omega
    rcases hb with rfl | rfl | rfl
    · exact a1_b0_unsat bits
    · exact a1_b1_unsat bits
    · exact a1_b2_unsat bits

end SeymourEight.ThreeZFullCore
