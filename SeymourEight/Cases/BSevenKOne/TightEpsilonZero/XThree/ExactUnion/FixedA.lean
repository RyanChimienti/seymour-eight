import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.CoreSoundness

set_option linter.style.header false

/-! Graph soundness of the exact core's fixed `A` structure. -/

namespace SeymourEight.FourZExactSevenFixedA

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactGlobalBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Produces exactly the `CompatibleRowData.fixedA` field.  It only assumes
the already-canonical `A/H/R` incidence labels, independently of `W`. -/
theorem fixedAStructure_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C) (hk : C.k = 1)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 → V) (w : Fin 7 → V)
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hH3X : (h 3).1 ∈ C.X)
    (hAR : ∀ q : Nat, (hq : q < 3) → (a ⟨q + 5, by omega⟩).1 ∈ C.R) :
    fixedAStructure (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) z w) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (a j).1) z w
  have hSquares := orientedSquare_coreBits_true G hG
    (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1) z w
  have hAOriented : orientedSquare 8 (aArc bits) = true := hSquares.2.1
  have hA0' : (a ⟨0, by omega⟩).1 = C.a1 := by simpa using hA0
  have hA1' : (a ⟨1, by omega⟩).1 = (h 0).1 := by simpa using hAH 0
  have hA01 : aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (a j).1) z w 0 1 (by omega) (by omega)]
    have hAdj : G.Adj C.a1 (h 0).1 := (Finset.mem_filter.mp hH0A1).2
    simp only [decide_eq_true_eq]
    rw [hA0', hA1']
    exact hAdj
  have hA0Tail : all 6 (fun q => !aArc bits 0 (q + 2)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (a j).1) z w 0 (q + 2) (by omega) (by omega)]
    have hNot : ¬G.Adj (a 0).1 (a ⟨q + 2, by omega⟩).1 := by
      rw [hA0]
      intro hadj
      have hm : (a ⟨q + 2, by omega⟩).1 ∈ C.A1 :=
        Finset.mem_filter.mpr ⟨(a ⟨q + 2, by omega⟩).2, hadj⟩
      have hEq : (a ⟨q + 2, by omega⟩).1 = (h 0).1 := by
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hk
        have ht : (a ⟨q + 2, by omega⟩).1 = u := by simpa [hu] using hm
        have hh : (h 0).1 = u := by simpa [hu] using hH0A1
        exact ht.trans hh.symm
      have hIndex : (⟨q + 2, by omega⟩ : Fin 8) = 1 := by
        apply a.injective
        apply Subtype.ext
        exact hEq.trans hA1'.symm
      have hVal := congrArg Fin.val hIndex
      simp only [Fin.val_one] at hVal
      omega
    simpa using hNot
  have hA1R : all 3 (fun q => !aArc bits 1 (q + 5)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (a j).1) z w 1 (q + 5) (by omega) (by omega)]
    have hSource : (a 1).1 = (h 0).1 := by simpa using hAH 0
    have hNotAdj : ¬G.Adj (h 0).1 (a ⟨q + 5, by omega⟩).1 := by
      intro hadj
      have hr := hAR q hq
      have hrX : (a ⟨q + 5, by omega⟩).1 ∈ C.X := by
        apply Finset.mem_inter.mpr
        constructor
        · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
          exact ⟨(h 0).1, Finset.mem_union_left C.P hH0A1, hadj⟩
        · apply Finset.mem_sdiff.mpr
          refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
          intro hParts
          apply (Finset.mem_sdiff.mp hr).2
          rcases Finset.mem_union.mp hParts with hA1 | ha1
          · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1)
          · exact Finset.mem_union_right (C.A1 ∪ C.X) ha1
      exact (Finset.mem_sdiff.mp hr).2
        (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))
    simp [hSource, hNotAdj]
  have hXReach (target : Nat) (ht : target = 2 ∨ target = 3 ∨ target = 4)
      (hTargetX : (a ⟨target, by omega⟩).1 ∈ C.X) :
      (aArc bits 1 target || any 7 (fun i =>
        pToH bits i (target - 1))) = true := by
    rcases Finset.mem_inter.mp hTargetX with ⟨hReached, _⟩
    obtain ⟨u, huParts, huTarget⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReached
    rcases Finset.mem_union.mp huParts with huA1 | huP
    · have huEq : u = (h 0).1 := by
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hk
        have huV : u = v := by simpa [hv] using huA1
        have hhV : (h 0).1 = v := by simpa [hv] using hH0A1
        exact huV.trans hhV.symm
      rw [Bool.or_eq_true]
      left
      rw [aArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (a j).1) z w 1 target (by omega) (by omega)]
      have hs : (a 1).1 = (h 0).1 := by simpa using hAH 0
      simpa [hs, huEq] using huTarget
    · obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
      rw [Bool.or_eq_true]
      right
      rw [any_eq_true_iff]
      refine ⟨i, i.isLt, ?_⟩
      rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (a j).1) z w i (target - 1) i.isLt (by omega)]
      have htH : (a ⟨target, by omega⟩).1 =
          (h ⟨target - 1, by omega⟩).1 := by
        simpa [show target - 1 + 1 = target by omega] using
          hAH ⟨target - 1, by omega⟩
      simpa [congrArg Subtype.val hi, htH] using huTarget
  have hX1 : (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) = true := by
    apply hXReach 2 (Or.inl rfl)
    simpa [show (a 2).1 = (h 1).1 by simpa using hAH 1] using hH1X
  have hX2 : (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) = true := by
    apply hXReach 3 (Or.inr (Or.inl rfl))
    simpa [show (a 3).1 = (h 2).1 by simpa using hAH 2] using hH2X
  have hX3 : (aArc bits 1 4 || any 7 (fun i => pToH bits i 3)) = true := by
    apply hXReach 4 (Or.inr (Or.inr rfl))
    simpa [show (a 4).1 = (h 3).1 by simpa using hAH 3] using hH3X
  have hX : all 3 (fun q =>
      aArc bits 1 (q + 2) || any 7 (fun i => pToH bits i (q + 1))) = true := by
    rw [all_eq_true_iff]
    intro q hq
    have hCases : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact hX1
    · exact hX2
    · exact hX3
  have hHDegrees : all 4 (fun hi =>
      (8 : BitVec 8).ule (hDegree bits hi)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree_toNat G C hG hPB p h a z w hAH i hi]
    exact hMin _
  have hRDegrees : all 3 (fun q =>
      (1 : BitVec 8).ule (aOut bits (q + 5))) = true := by
    rw [all_eq_true_iff]
    intro q hq
    have hOut := aOut_toNat G C (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      a z w (q + 5) (by omega)
    have hMinA := (hPivot (a ⟨q + 5, by omega⟩).1
      (a ⟨q + 5, by omega⟩).2).1
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hOut]
    change 1 ≤ directCount G C.A (a ⟨q + 5, by omega⟩).1
    rw [hk] at hMinA
    exact hMinA
  rw [FourZExactSeven.fixedAStructure]
  simpa only [Bool.and_eq_true] using
    ⟨⟨⟨⟨⟨⟨hAOriented, hA01⟩, hA0Tail⟩, hA1R⟩, hX⟩,
      hHDegrees⟩, hRDegrees⟩

end SeymourEight.FourZExactSevenFixedA
