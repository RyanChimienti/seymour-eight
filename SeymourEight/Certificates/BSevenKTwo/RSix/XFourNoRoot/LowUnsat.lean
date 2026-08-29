import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.CZeroMZero
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.COneMZero
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.COneMOne
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.CTwoMZero
import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.CTwoMOne
namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core

set_option maxHeartbeats 2000000 in
theorem low_case_unsat (c m alpha beta : Nat)
    (hc : c ≤ 2) (hm : m ≤ 1) (hdefect : m + alpha + beta ≤ c)
    (bits : Encoding) : coreCase c m alpha beta bits = false := by
  have hcCases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcCases with rfl | rfl | rfl
  · have h : m = 0 ∧ alpha = 0 ∧ beta = 0 := by omega
    rcases h with ⟨rfl, rfl, rfl⟩
    exact cZero_mZero_aZero_bZero_unsat bits
  · have h :
        (m = 0 ∧ alpha = 0 ∧ beta = 0) ∨
        (m = 0 ∧ alpha = 1 ∧ beta = 0) ∨
        (m = 0 ∧ alpha = 0 ∧ beta = 1) ∨
        (m = 1 ∧ alpha = 0 ∧ beta = 0) := by omega
    rcases h with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    · exact cOne_mZero_aZero_bZero_unsat bits
    · exact cOne_mZero_aOne_bZero_unsat bits
    · exact cOne_mZero_aZero_bOne_unsat bits
    · exact cOne_mOne_aZero_bZero_unsat bits
  · have h :
        (m = 0 ∧ alpha = 0 ∧ beta = 0) ∨
        (m = 0 ∧ alpha = 1 ∧ beta = 0) ∨
        (m = 0 ∧ alpha = 0 ∧ beta = 1) ∨
        (m = 0 ∧ alpha = 2 ∧ beta = 0) ∨
        (m = 0 ∧ alpha = 1 ∧ beta = 1) ∨
        (m = 0 ∧ alpha = 0 ∧ beta = 2) ∨
        (m = 1 ∧ alpha = 0 ∧ beta = 0) ∨
        (m = 1 ∧ alpha = 1 ∧ beta = 0) ∨
        (m = 1 ∧ alpha = 0 ∧ beta = 1) := by omega
    rcases h with h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    · exact cTwo_mZero_aZero_bZero_unsat bits
    · exact cTwo_mZero_aOne_bZero_unsat bits
    · exact cTwo_mZero_aZero_bOne_unsat bits
    · exact cTwo_mZero_aTwo_bZero_unsat bits
    · exact cTwo_mZero_aOne_bOne_unsat bits
    · exact cTwo_mZero_aZero_bTwo_unsat bits
    · exact cTwo_mOne_aZero_bZero_unsat bits
    · exact cTwo_mOne_aOne_bZero_unsat bits
    · exact cTwo_mOne_aZero_bOne_unsat bits

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core
