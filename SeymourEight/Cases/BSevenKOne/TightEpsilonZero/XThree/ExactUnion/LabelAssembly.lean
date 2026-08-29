import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.AssemblyCore
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.PZLabels

set_option linter.style.header false

/-! Assemble graph-sound fields once the canonical finite labels are fixed. -/

namespace SeymourEight.FourZExactSevenAssembly

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FourZExactSevenPZLabels FourZExactSevenAccounting FourZExactSevenFixedA
  FourZExactSevenPBridge FourZExactSevenZBridge FourZExactSevenHBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactGlobalBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
noncomputable def rowData_of_compatibleLabels (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 3)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing : Nat) (hMissing : missing ≤ 1)
    (hPZCount : edgeCount G C.P C.Z + missing = 28)
    (overlap : OverlapType) (pz : FourZExactSevenPZLabels.Data G C missing)
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hH3X : (h 3).1 ∈ C.X)
    (hAR : ∀ q : Nat, (hq : q < 3) → (a ⟨q + 5, by omega⟩).1 ∈ C.R)
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (hOrderH : orderedH overlap (coreBits G.Adj (fun j ↦ (pz.p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1)
      (fun j ↦ (w j).1)) = true) : CompatibleRowData G C := by
  let degreeSum := ∑ u ∈ C.P, G.outdegree u
  let bits := coreBits G.Adj (fun j ↦ (pz.p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1) (fun j ↦ (w j).1)
  have hZP := FourZExactSevenPZLabels.zToP_iff_exceptional G C hG missing
    pz.p (fun j ↦ (h j).1) (fun j ↦ (a j).1) pz.z
    (fun j ↦ (w j).1) pz.pToZ
  have hDefect := FourZExactSevenAccounting.defectIdentity G C hG hMin
    hRootDegree hk hx hPB hEpsilon missing degreeSum pz.p h
    (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1) (fun j ↦ (w j).1)
    hPZCount rfl
  have hBytes := FourZExactSevenAccounting.degreeBytes G C hG hPB hEpsilon
    missing degreeSum pz.p h (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1)
    (fun j ↦ (w j).1) pz.rows rfl
  have hFixed := FourZExactSevenFixedA.fixedAStructure_coreBits_true G C hG
    hPivot hk hMin hPB pz.p h a (fun j ↦ (pz.z j).1)
    (fun j ↦ (w j).1) hA0 hAH hH0A1 hH1X hH2X hH3X hAR
  have hZRows := FourZExactSevenZBridge.zRows_coreBits_true G C missing
    overlap pz.p h (fun j ↦ (a j).1) pz.z w pz.pToZ hZP hWH hHInW
    hMin hNoSeymour
  have hHRows := FourZExactSevenHBridge.hRows_coreBits_true G C hG hPB
    missing pz.p h a pz.z (fun j ↦ (w j).1) hA0 hAH pz.pToZ hMin
    hNoSeymour
  have hPRows := FourZExactSevenPBridge.pRows_coreBits_true G C hG hPB
    hEpsilon missing overlap pz.p h (fun j ↦ (a j).1) pz.z w pz.rows
    pz.pToZ hWH hHInW hMin hNoSeymour
  have hOrderP := FourZExactSevenGraphBridge.orderedP_coreBits_true G C hG
    hPB hEpsilon missing pz.p h (fun j ↦ (a j).1) (fun j ↦ (pz.z j).1)
    (fun j ↦ (w j).1) pz.rows pz.sorted
  exact {
    missing := missing
    degreeSum := degreeSum
    overlap := overlap
    p := pz.p
    h := h
    a := a
    z := pz.z
    w := w
    missing_le := hMissing
    pz_count := hPZCount
    pz_rows := pz.rows
    degreeSum_eq := rfl
    defectIdentity := hDefect
    degreeBytes := hBytes
    fixedA := hFixed
    zRows := hZRows
    hRows := hHRows
    pRows := hPRows
    orderH := hOrderH
    orderP := hOrderP }

end SeymourEight.FourZExactSevenAssembly
