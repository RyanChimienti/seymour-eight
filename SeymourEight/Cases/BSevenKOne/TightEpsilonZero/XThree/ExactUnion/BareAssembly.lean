import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.BareAssemblyCore
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.OverlapLabels
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Dispatch

set_option linter.style.header false

namespace SeymourEight.FourZExactSevenAssembly

open FourZExactSeven FourZExactSevenGraphBridge FourZExactSevenPZLabels
  FourZExactSevenOverlapLabels Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The bare graph theorem for the exact-seven part of the tight `x=3,z=4`
low-defect branch. -/
theorem impossible_exactFourZ_externalUnion_eq_seven
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1) (hx : C.x = 3)
    (hz : C.z = 4) (hEpsilon : epsilonS G C = 0)
    (hPZ : 27 ≤ edgeCount G C.P C.Z)
    (hWCard : (FourZExactSevenGraphBridge.zExternalUnion G C).card = 7) :
    False := by
  classical
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 4 := hz
  have hHCard : C.H.card = 4 := by
    change C.h = 4
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hA1Card : C.A1.card = 1 := hk
  have hXCard : C.X.card = 3 := hx
  have hPZUpper : edgeCount G C.P C.Z ≤ 28 := by
    have hc := edgeCount_le_card_mul_card G C.P C.Z
    simpa [hPCard, hZCard] using hc
  rcases (show edgeCount G C.P C.Z = 28 ∨
      edgeCount G C.P C.Z = 27 by omega) with hFull | hOne
  · obtain ⟨pz⟩ := FourZExactSevenPZLabels.exists_data_zero G C hPCard
      hZCard hHCard hFull
    obtain ⟨ov⟩ := FourZExactSevenOverlapLabels.exists_data G C pz.p hA1Card
      hXCard hHCard hWCard
    apply impossible_of_overlapLabels G C hG hPivot hMin hNoSeymour
      hRootDegree hk hx hPB hEpsilon 0 (by omega) (by omega) pz ov.overlap
      ov.h ov.w ov.h0A1 ov.h1X ov.h2X ov.h3X ov.hWH ov.hHInW
      (fun a ↦ ov.orderH (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1))
    intro degreeSum bits hLower hUpper
    exact core_unsat 0 degreeSum ov.overlap (by omega) hLower hUpper bits
  · obtain ⟨pz⟩ := FourZExactSevenPZLabels.exists_data_one G C hPCard
      hZCard hHCard hOne
    obtain ⟨ov⟩ := FourZExactSevenOverlapLabels.exists_data G C pz.p hA1Card
      hXCard hHCard hWCard
    apply impossible_of_overlapLabels G C hG hPivot hMin hNoSeymour
      hRootDegree hk hx hPB hEpsilon 1 (by omega) (by omega) pz ov.overlap
      ov.h ov.w ov.h0A1 ov.h1X ov.h2X ov.h3X ov.hWH ov.hHInW
      (fun a ↦ ov.orderH (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1))
    intro degreeSum bits hLower hUpper
    exact core_unsat 1 degreeSum ov.overlap (by omega) hLower hUpper bits

end SeymourEight.FourZExactSevenAssembly
