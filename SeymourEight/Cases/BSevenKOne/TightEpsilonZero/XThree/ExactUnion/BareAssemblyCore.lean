import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.LabelAssembly

set_option linter.style.header false

namespace SeymourEight.FourZExactSevenAssembly

open FourZExactSeven FourZExactSevenGraphBridge FourZExactSevenPZLabels
  FourZExactSevenLabels FiveZExactPBridge FiveZExactRisk
  Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 2000000 in
/-- Contradiction from the canonical `H/W` overlap package.  All `A` labels,
row predicates, accounting fields, and degree bounds are constructed here. -/
theorem impossible_of_overlapLabels (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 3)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing : Nat) (hMissing : missing ≤ 1)
    (hPZCount : edgeCount G C.P C.Z + missing = 28)
    (pz : FourZExactSevenPZLabels.Data G C missing)
    (overlap : OverlapType) (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hH3X : (h 3).1 ∈ C.X)
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (hOrderH : ∀ (a : Fin 8 ≃ {v : V // v ∈ C.A}),
      orderedH overlap (FourZExactSevenBridge.coreBits G.Adj
        (fun j ↦ (pz.p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (pz.z j).1) (fun j ↦ (w j).1)) = true)
    (hDispatch : ∀ (degreeSum : Nat) (bits : BitVec 214),
      56 ≤ degreeSum → degreeSum ≤ 63 - missing →
      core missing degreeSum overlap bits = false) : False := by
  classical
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hRCard : C.R.card = 3 := by
    have hXR := Digraph.LocalConfiguration.x_add_card_R_eq_six_of_k_eq_one
      (G := G) C hG.1 hRootDegree hk
    change C.X.card = 3 at hx
    change C.X.card + C.R.card = 6 at hXR
    omega
  let eR : Fin 3 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a : Fin 8 ≃ {v : V // v ∈ C.A} :=
    FourZExactSevenLabels.aLabelEquiv G C hACard h eR
  have hA0 : (a 0).1 = C.a1 :=
    FourZExactSevenLabels.aLabelEquiv_zero G C hACard h eR
  have hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1 := by
    intro j
    exact FourZExactSevenLabels.aLabelEquiv_h G C hACard h eR j
  have hAR : ∀ q : Nat, (hq : q < 3) → (a ⟨q + 5, by omega⟩).1 ∈ C.R := by
    intro q hq
    rw [FourZExactSevenLabels.aLabelEquiv_r G C hACard h eR ⟨q, hq⟩]
    exact (eR ⟨q, hq⟩).2
  let d := rowData_of_compatibleLabels G C hG hPivot hMin hNoSeymour
    hRootDegree hk hx hPB hEpsilon missing hMissing hPZCount overlap pz h a w
    hA0 hAH hH0A1 hH1X hH2X hH3X hAR hWH hHInW (hOrderH a)
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr pz.p).symm
  have hHCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hLower : 56 ≤ d.degreeSum := by
    change 56 ≤ ∑ u ∈ C.P, G.outdegree u
    calc
      56 = ∑ _u ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ u ∈ C.P, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hPHUpper : edgeCount G C.P C.H ≤ 14 := by
    have hReverse := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB
      hRootDegree hk
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hCross
    simp [hx, Nat.choose] at hReverse
    omega
  have hPPUpper : edgeCount G C.P C.P ≤ 21 :=
    internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ u ∈ C.P, epsilonAt G u C.s = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [epsilonAt, no_P_to_s_of_epsilonS_zero G C hEpsilon u hu]
  rw [hNoRoot] at hAccounting
  have hUpper : d.degreeSum ≤ 63 - missing := by
    change (∑ u ∈ C.P, G.outdegree u) ≤ 63 - missing
    omega
  apply impossible_of_compatibleRowData G C hG hMin hRootDegree hk hx hPB
    hEpsilon d
  intro bits
  exact hDispatch d.degreeSum bits hLower hUpper

end SeymourEight.FourZExactSevenAssembly
