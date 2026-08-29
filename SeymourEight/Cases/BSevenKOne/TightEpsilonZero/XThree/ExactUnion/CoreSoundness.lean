import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.GraphBridge

set_option linter.style.header false

/-! Composition of graph-facing bridge facts into one exact-union core row. -/

namespace SeymourEight.FourZExactSevenGraphBridge

open FourZExactSeven FourZExactSevenBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZExactGlobalBridge Shared BSevenKOneCounting
  FiveZExactHBridge FiveZExactPBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem orientedSquare_coreBits_true
    (hG : G.IsOriented) (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V) :
    orientedSquare 7 (pArc (coreBits G.Adj p h a z w)) = true ∧
      orientedSquare 8 (aArc (coreBits G.Adj p h a z w)) = true ∧
      orientedSquare 4 (zArc (coreBits G.Adj p h a z w)) = true := by
  classical
  have square (n : Nat) (e : Fin n → V)
      (arc : BitVec 214 → Nat → Nat → Bool)
      (decode : ∀ i j : Nat, (hi : i < n) → (hj : j < n) →
        arc (coreBits G.Adj p h a z w) i j =
          decide (G.Adj (e ⟨i, hi⟩) (e ⟨j, hj⟩))) :
      orientedSquare n (arc (coreBits G.Adj p h a z w)) = true := by
    rw [orientedSquare, all_eq_true_iff]
    intro i hi
    rw [Bool.and_eq_true]
    constructor
    · rw [decode i i hi hi]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      exact hG.1 _
    · rw [all_eq_true_iff]
      intro j hj
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij]
        rw [decode i j hi hj, decode j i hj hi]
        by_cases huv : G.Adj (e ⟨i, hi⟩) (e ⟨j, hj⟩)
        · have hvu := hG.2 huv
          simp [huv, hvu]
        · simp [huv]
  exact ⟨square 7 p pArc (pArc_coreBits G.Adj p h a z w),
    square 8 a aArc (aArc_coreBits G.Adj p h a z w),
    square 4 z zArc (zArc_coreBits G.Adj p h a z w)⟩

omit [Fintype V] [DecidableEq V] in
theorem orientedPH_coreBits_true (hG : G.IsOriented)
    (p : Fin 7 → V) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) :
    FourZExactSeven.orientedPH (coreBits G.Adj p h a z w) = true := by
  classical
  rw [FourZExactSeven.orientedPH, all_eq_true_iff]
  intro i hi
  rw [all_eq_true_iff]
  intro j hj
  simp only [Bool.not_eq_true']
  rw [pToH_coreBits G.Adj p h a z w i j hi hj,
    hToP_coreBits G.Adj p h a z w j i hj hi]
  by_cases hij : G.Adj (p ⟨i, hi⟩) (h ⟨j, hj⟩)
  · have hji := hG.2 hij
    simp [hij, hji]
  · simp [hij]

theorem exactWCoverage_coreBits_true (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ zExternalUnion G C}) :
    all 7 (fun wi => any 4 fun zi =>
      zToW (coreBits G.Adj p h a (fun j ↦ (z j).1) (fun j ↦ (w j).1)) zi wi) = true := by
  rw [all_eq_true_iff]
  intro wi hwi
  have hw := (w ⟨wi, hwi⟩).2
  rcases (Digraph.mem_outNeighborFinsetOf (G := G)).mp
      (Finset.mem_sdiff.mp hw).1 with ⟨u, huZ, huw⟩
  obtain ⟨zi, hzi⟩ := z.surjective ⟨u, huZ⟩
  rw [any_eq_true_iff]
  refine ⟨zi, zi.isLt, ?_⟩
  rw [zToW_coreBits G.Adj p h a (fun j ↦ (z j).1) (fun j ↦ (w j).1)
    zi wi zi.isLt hwi]
  simpa [congrArg Subtype.val hzi] using huw

/-- This theorem deliberately isolates the three substantial
second-neighborhood soundness families as named premises.  The decoder,
orientation, global counts, exact degree sum, and exact-union coverage are
proved here. -/
theorem coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 3)
    (hPB : C.P = C.B) (_hEpsilon : epsilonS G C = 0)
    (missing degreeSum : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ zExternalUnion G C})
    (_hPZ : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hDefectIdentity : totalMissingPPairs (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) +
      (14 - totalPToH (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1))) =
      BitVec.ofNat 8 (63 - missing - degreeSum))
    (hDegreeBytes : sumCount 7 (pDegree missing (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1))) = BitVec.ofNat 8 degreeSum)
    (hFixedA : fixedAStructure (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1)) = true)
    (hZRows : all 4 (fun zi =>
      (8 : BitVec 8).ule (zDegree missing (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) zi) &&
      zNonSeymour missing overlap (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) zi) = true)
    (hHRows : all 4 (hNonSeymour missing (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1))) = true)
    (hPRows : all 7 (fun pi =>
      (8 : BitVec 8).ule (pDegree missing (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) pi) &&
      (pDegree missing (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) pi).ule 14 &&
      pNonSeymour missing overlap (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) pi) = true)
    (hOrderH : orderedH overlap (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1)) = true)
    (hOrderP : orderedP missing (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1)) = true) :
    core missing degreeSum overlap (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1)) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (a j).1) (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  have hSquares := orientedSquare_coreBits_true G hG
    (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  have hCross := orientedPH_coreBits_true G hG
    (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hPTotalNat := totalPToH_toNat G C p h
    (fun j ↦ (a j).1) (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  have hHTotalNat := totalHToP_toNat G C p h
    (fun j ↦ (a j).1) (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  have hHTotalLower : 14 ≤ edgeCount G C.H C.P := by
    have hc := eight_add_choose_x_succ_le_H_to_P G C hG hMin hPB hRootDegree hk
    simpa [hx, Nat.choose] using hc
  have hPTotalUpper : edgeCount G C.P C.H ≤ 14 := by
    have hc := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hc
    omega
  have hPTotal : (totalPToH bits).ule 14 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hPTotalNat]
    exact hPTotalUpper
  have hHTotal : (14 : BitVec 8).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHTotalNat]
    exact hHTotalLower
  have hHPositive : all 4 (fun hi => (1 : BitVec 8).ule (hPOut bits hi)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hPOut_toNat G C p h (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) i hi]
    change 1 ≤ directCount G C.P (h ⟨i, hi⟩).1
    have hDegree := H_outdegree_eq_A_add_P G C hG hPB
      (h ⟨i, hi⟩).1 (h ⟨i, hi⟩).2
    have hAUpper : directCount G C.A (h ⟨i, hi⟩).1 ≤ 7 := by
      have huA := Digraph.LocalConfiguration.H_subset_A (G := G) C (h ⟨i, hi⟩).2
      have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr a).symm
      calc
        directCount G C.A (h ⟨i, hi⟩).1 ≤
            (C.A.erase (h ⟨i, hi⟩).1).card := by
          unfold directCount CertificateBridge.internalFirstNeighbors
          apply Finset.card_le_card
          intro v hv
          apply Finset.mem_erase.mpr
          refine ⟨?_, (Finset.mem_filter.mp hv).1⟩
          intro hvu
          subst v
          exact hG.1 _ (Finset.mem_filter.mp hv).2
        _ = 7 := by rw [Finset.card_erase_of_mem huA, hACard]
    have hMinH := hMin (h ⟨i, hi⟩).1
    omega
  have hCoverage := exactWCoverage_coreBits_true G C
    (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1) z w
  rw [core]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSquares.1, hCross⟩, hSquares.2.2⟩,
    hPTotal⟩, hHTotal⟩, hDefectIdentity⟩, hHPositive⟩, hFixedA⟩,
    hCoverage⟩, hZRows⟩, hHRows⟩, hPRows⟩, hDegreeBytes⟩, hOrderH⟩,
    hOrderP⟩

end SeymourEight.FourZExactSevenGraphBridge
