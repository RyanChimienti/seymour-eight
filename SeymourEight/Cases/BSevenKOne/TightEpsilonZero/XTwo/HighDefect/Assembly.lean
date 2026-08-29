import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.HighDefect.Structure

set_option linter.style.header false

namespace SeymourEight.FiveZHighDefectAssembly

open FiveZHighDefect FiveZHighDefectBridge FiveZHighDefectGraphBridge
  FiveZExactLabels FiveZExactRisk FiveZExactGlobalBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem impossible_of_compatibleLabels
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPB : C.P = C.B)
    (hk : C.k = 1) (hx : C.x = 2) (hEpsilon : epsilonS G C = 0)
    (hHighDefect : 4 ≤ 35 - edgeCount G C.P C.Z)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (r : Fin 4 ≃ {v : V // v ∈ C.R})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hAR : ∀ i : Fin 4, (a ⟨i + 4, by omega⟩).1 = (r i).1) : False := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
    (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  have hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1 := by
    intro i
    rw [hA0]
    exact (Finset.mem_filter.mp (p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1 := by
    intro i
    exact hG.2 (hA0P i)
  have hPR : ∀ i : Fin 7, ∀ j : Fin 4, ¬G.Adj (p i).1 (r j).1 := by
    intro i j
    exact P_not_adj_R G C (p i).1 (r j).1 (p i).2 (r j).2
  have hAZ : ∀ i : Fin 8, ∀ j : Fin 5, ¬G.Adj (a i).1 (z j).1 := by
    intro i j
    exact A_not_adj_Z G C hG (a i).1 (z j).1 (a i).2 (z j).2
  have hA01 : G.Adj (a 0).1 (a 1).1 := by
    have h1 : (a 1).1 = (h 0).1 := by simpa using hAH 0
    rw [hA0, h1]
    exact (Finset.mem_filter.mp hH0A1).2
  have hDegreeA0 : G.outdegree (a 0).1 = 8 := by
    rw [hA0]
    exact BSevenKOne.outdegree_a1_eq_eight G C hG hMin
      (by rw [← hPB]; simpa using (Fintype.card_congr p).symm) hk
  have hFixed := fixedStructure_coreBits_true G C hG hPivot hMin hRootDegree
    hPB hk hx hEpsilon p h r z a hA0 hAH hH0A1 hH1X hH2X hAR
  have hDeletion := aOneDeletionExpands_coreBits_true G hBound C hG hPB
    hEpsilon hNoSeymour p (fun i ↦ (h i).1) (fun i ↦ (r i).1) z a
    hDegreeA0 hA01 hA0P hP0 hAH hAR hPR hAZ
  have hMissingNat := totalMissingPZ_coreBits_toNat_add_edges G C p z
    (fun i ↦ (h i).1) (fun i ↦ (r i).1) (fun i ↦ (a i).1)
  change (FiveZHighDefect.totalMissingPZ bits).toNat +
    edgeCount G C.P C.Z = 35 at hMissingNat
  have hMissing : (4 : BitVec 8).ule
      (FiveZHighDefect.totalMissingPZ bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    change 4 ≤ (FiveZHighDefect.totalMissingPZ bits).toNat
    omega
  have hRows : all 7 (fun q => aNonSeymour bits (q + 1)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    exact aNonSeymour_coreBits_true G C hG hPB hEpsilon hNoSeymour p
      (fun i ↦ (h i).1) (fun i ↦ (r i).1) z a
      hA0P hP0 hAH hAR hPR hAZ (q + 1) (by omega)
  have hCore : highDefectCore bits = true := by
    rw [highDefectCore]
    simpa only [Bool.and_eq_true] using ⟨⟨⟨hFixed, hDeletion⟩, hMissing⟩, hRows⟩
  exact impossible_of_encodedCore G.Adj (fun i ↦ (p i).1)
    (fun i ↦ (h i).1) (fun i ↦ (r i).1) (fun i ↦ (z i).1)
    (fun i ↦ (a i).1) hCore

theorem tightEpsilonZeroXTwoHighDefectImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 2) (hz : C.z = 5)
    (hHighDefect : 4 ≤ 35 - edgeCount G C.P C.Z) : False := by
  classical
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 5 := by exact hz
  have hHCard : C.H.card = 3 := by
    change C.h = 3
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 1 := hk
  have hXCard : C.X.card = 2 := hx
  have hRCard : C.R.card = 4 := by
    have hXR := Digraph.LocalConfiguration.x_add_card_R_eq_six_of_k_eq_one
      (G := G) C hG.1 hRootDegree hk
    change C.X.card = 2 at hx
    change C.X.card + C.R.card = 6 at hXR
    omega
  let p : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let z : Fin 5 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let eA1 : Fin 1 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eX : Fin 2 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let h : Fin 3 ≃ {v : V // v ∈ C.H} := hLabelEquiv G C hHCard eA1 eX
  let eR : Fin 4 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a : Fin 8 ≃ {v : V // v ∈ C.A} := aLabelEquiv G C hACard h eR
  have hH0A1 : (h 0).1 ∈ C.A1 := by
    rw [show (h 0).1 = (eA1 0).1 by exact hLabelEquiv_zero G C hHCard eA1 eX]
    exact (eA1 0).2
  have hH1X : (h 1).1 ∈ C.X := by
    rw [show (h 1).1 = (eX 0).1 by exact hLabelEquiv_one G C hHCard eA1 eX]
    exact (eX 0).2
  have hH2X : (h 2).1 ∈ C.X := by
    rw [show (h 2).1 = (eX 1).1 by exact hLabelEquiv_two G C hHCard eA1 eX]
    exact (eX 1).2
  have hA0 : (a 0).1 = C.a1 := aLabelEquiv_zero G C hACard h eR
  have hAH : ∀ i : Fin 3, (a ⟨i + 1, by omega⟩).1 = (h i).1 := by
    intro i
    exact aLabelEquiv_h G C hACard h eR i
  have hAR : ∀ i : Fin 4, (a ⟨i + 4, by omega⟩).1 = (eR i).1 := by
    intro i
    exact aLabelEquiv_r G C hACard h eR i
  exact impossible_of_compatibleLabels G hBound C hG hPivot hMin hNoSeymour
    hRootDegree hPB hk hx hEpsilon hHighDefect p h eR z a hA0 hAH
    hH0A1 hH1X hH2X hAR

end SeymourEight.FiveZHighDefectAssembly
