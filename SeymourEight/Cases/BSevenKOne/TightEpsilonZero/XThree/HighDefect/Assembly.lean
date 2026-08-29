import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.HighDefect.Structure
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Labels
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false

namespace SeymourEight.FourZHighDefectAssembly

open FourZHighDefect FourZHighDefectBridge FourZHighDefectGraphBridge
  FiveZExactRisk FiveZExactGlobalBridge Shared
  BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def zColumnCode (p : Fin 7 → V) (v : V) : BitVec 16 :=
  count16 7 fun i =>
    bitCount16 (decide (G.Adj (p ⟨i % 7, Nat.mod_lt _ (by omega)⟩) v)) <<< i

def zSortPermutation (p : Fin 7 → V) (z : Fin 4 → V) : Equiv.Perm (Fin 4) :=
  Tuple.sort fun i => OrderDual.toDual (zColumnCode G p (z i)).toNat

noncomputable def sortedZFinsetEquiv (p : Fin 7 → V) (Z : Finset V)
    (eZ : Fin 4 ≃ {v : V // v ∈ Z}) : Fin 4 ≃ {v : V // v ∈ Z} :=
  (zSortPermutation G p (fun i => (eZ i).1)).trans eZ

omit [Fintype V] [DecidableEq V] in
theorem sortedZ_code_anti (p : Fin 7 → V) (Z : Finset V)
    (eZ : Fin 4 ≃ {v : V // v ∈ Z}) {i j : Fin 4} (hij : i ≤ j) :
    (zColumnCode G p (sortedZFinsetEquiv G p Z eZ i).1).toNat ≥
      (zColumnCode G p (sortedZFinsetEquiv G p Z eZ j).1).toNat := by
  classical
  exact Tuple.monotone_sort
    (fun q => OrderDual.toDual (zColumnCode G p (eZ q).1).toNat) hij

theorem pHCount_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V) (i : Nat) (hi : i < 7) :
    (count 4 (pToH (coreBits G.Adj (fun q => (p q).1)
      (fun q => (h q).1) r z a) i)).toNat =
      directCount G C.H (p ⟨i, hi⟩).1 := by
  rw [FiveZExactGraphBridge.toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H h
  intro j
  rw [pToH_coreBits G.Adj (fun q => (p q).1) (fun q => (h q).1)
    r z a i j hi j.isLt]
  simp

theorem orderedP_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (r : Fin 3 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (a : Fin 8 → V)
    (hSorted : ∀ q : Nat, (hq : q < 6) →
      G.outdegree (p ⟨q + 1, by omega⟩).1 ≤ G.outdegree (p ⟨q, by omega⟩).1 ∧
        (G.outdegree (p ⟨q, by omega⟩).1 = G.outdegree (p ⟨q + 1, by omega⟩).1 →
          directCount G C.H (p ⟨q + 1, by omega⟩).1 ≤
            directCount G C.H (p ⟨q, by omega⟩).1)) :
    FourZHighDefect.orderedP (coreBits G.Adj (fun q => (p q).1) (fun q => (h q).1)
      r (fun q => (z q).1) a) = true := by
  let bits := coreBits G.Adj (fun q => (p q).1) (fun q => (h q).1)
    r (fun q => (z q).1) a
  rw [FourZHighDefect.orderedP, all_eq_true_iff]
  intro q hq
  have hd0 := pDegree_coreBits_toNat G C hG hPB hEpsilon p h r z a q
    (by omega)
  have hd1 := pDegree_coreBits_toNat G C hG hPB hEpsilon p h r z a
    (q + 1) (by omega)
  have hh0 := pHCount_coreBits_toNat G C p h r (fun i => (z i).1) a q
    (by omega)
  have hh1 := pHCount_coreBits_toNat G C p h r (fun i => (z i).1) a
    (q + 1) (by omega)
  have hs := hSorted q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    BitVec.ule_eq_decide, decide_eq_true_eq]
  constructor
  · simpa [hd0, hd1] using hs.1
  · by_cases heq : pDegree bits q = pDegree bits (q + 1)
    · right
      have hdeg : G.outdegree (p ⟨q, by omega⟩).1 =
          G.outdegree (p ⟨q + 1, by omega⟩).1 := by
        rw [← hd0, ← hd1, heq]
      simpa [hh0, hh1] using hs.2 hdeg
    · left
      apply Bool.eq_false_iff.mpr
      intro hb
      exact heq (beq_iff_eq.mp hb)

omit [Fintype V] [DecidableEq V] in
theorem zCode_coreBits (p : Fin 7 → V) (h : Fin 4 → V) (r : Fin 3 → V)
    (z : Fin 4 → V) (a : Fin 8 → V) (j : Nat) (hj : j < 4) :
    zCode (coreBits G.Adj p h r z a) j = zColumnCode G p (z ⟨j, hj⟩) := by
  classical
  unfold zCode zColumnCode
  simp only [count16]
  rw [pToZ_coreBits G.Adj p h r z a 0 j (by omega) hj,
    pToZ_coreBits G.Adj p h r z a 1 j (by omega) hj,
    pToZ_coreBits G.Adj p h r z a 2 j (by omega) hj,
    pToZ_coreBits G.Adj p h r z a 3 j (by omega) hj,
    pToZ_coreBits G.Adj p h r z a 4 j (by omega) hj,
    pToZ_coreBits G.Adj p h r z a 5 j (by omega) hj,
    pToZ_coreBits G.Adj p h r z a 6 j (by omega) hj]

theorem orderedZ_coreBits_true (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 4 → V)
    (r : Fin 3 → V) (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (a : Fin 8 → V)
    (hSorted : ∀ q : Nat, (hq : q < 3) →
      (zColumnCode G p (z ⟨q + 1, by omega⟩).1).toNat ≤
        (zColumnCode G p (z ⟨q, by omega⟩).1).toNat) :
    FourZHighDefect.orderedZ
      (coreBits G.Adj p h r (fun q => (z q).1) a) = true := by
  rw [FourZHighDefect.orderedZ, all_eq_true_iff]
  intro q hq
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zCode_coreBits G p h r (fun i => (z i).1) a q (by omega),
    zCode_coreBits G p h r (fun i => (z i).1) a (q + 1) (by omega)]
  exact hSorted q hq

theorem impossible_of_compatibleLabels
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPB : C.P = C.B)
    (hk : C.k = 1) (hx : C.x = 3) (hEpsilon : epsilonS G C = 0)
    (hHighDefect : 2 ≤ 28 - edgeCount G C.P C.Z)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (r : Fin 3 ≃ {v : V // v ∈ C.R})
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hH3X : (h 3).1 ∈ C.X)
    (hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = (r i).1)
    (hOrderP : FourZHighDefect.orderedP (coreBits G.Adj (fun i => (p i).1)
      (fun i => (h i).1) (fun i => (r i).1) (fun i => (z i).1)
      (fun i => (a i).1)) = true)
    (hOrderZ : FourZHighDefect.orderedZ (coreBits G.Adj (fun i => (p i).1)
      (fun i => (h i).1) (fun i => (r i).1) (fun i => (z i).1)
      (fun i => (a i).1)) = true) : False := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
    (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  let missing := (FourZHighDefect.totalMissingPZ bits).toNat
  let degreeSum := ∑ u ∈ C.P, G.outdegree u
  have hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1 := by
    intro i
    rw [hA0]
    exact (Finset.mem_filter.mp (p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1 := by
    intro i
    exact hG.2 (hA0P i)
  have hPR : ∀ i : Fin 7, ∀ j : Fin 3, ¬G.Adj (p i).1 (r j).1 := by
    intro i j
    exact P_not_adj_R G C (p i).1 (r j).1 (p i).2 (r j).2
  have hAZ : ∀ i : Fin 8, ∀ j : Fin 4, ¬G.Adj (a i).1 (z j).1 := by
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
    hPB hk hx hEpsilon p h r z a hA0 hAH hH0A1 hH1X hH2X hH3X hAR
  have hDeletion := aOneDeletionExpands_coreBits_true G hBound C hG hPB
    hEpsilon hNoSeymour p (fun i ↦ (h i).1) (fun i ↦ (r i).1) z a
    hDegreeA0 hA01 hA0P hP0 hAH hAR hPR hAZ
  have hMissingNat := totalMissingPZ_coreBits_toNat_add_edges G C p z
    (fun i ↦ (h i).1) (fun i ↦ (r i).1) (fun i ↦ (a i).1)
  change (FourZHighDefect.totalMissingPZ bits).toNat +
    edgeCount G C.P C.Z = 28 at hMissingNat
  have hMissingLower : 2 ≤ missing := by
    change 2 ≤ (FourZHighDefect.totalMissingPZ bits).toNat
    omega
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr p).symm
  have hHCard : C.H.card = 4 := by
    simpa using (Fintype.card_congr h).symm
  have hDegreeLower : 56 ≤ degreeSum := by
    change 56 ≤ ∑ u ∈ C.P, G.outdegree u
    calc
      56 = ∑ _u ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ u ∈ C.P, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hPHUpper : edgeCount G C.P C.H ≤ 14 := by
    have hReverse := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
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
    simp [epsilonAt, FiveZExactPBridge.no_P_to_s_of_epsilonS_zero
      G C hEpsilon u hu]
  rw [hNoRoot] at hAccounting
  have hPZLower : 21 ≤ edgeCount G C.P C.Z := by omega
  have hMissingUpper : missing ≤ 7 := by
    change (FourZHighDefect.totalMissingPZ bits).toNat ≤ 7
    omega
  have hDegreeUpper : degreeSum ≤ 63 - missing := by
    change (∑ u ∈ C.P, G.outdegree u) ≤
      63 - (FourZHighDefect.totalMissingPZ bits).toNat
    omega
  have hMissing : (2 : BitVec 8).ule
      (FourZHighDefect.totalMissingPZ bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    change 2 ≤ (FourZHighDefect.totalMissingPZ bits).toNat
    omega
  have hRows : all 7 (fun q => aNonSeymour bits (q + 1)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    exact aNonSeymour_coreBits_true G C hG hPB hEpsilon hNoSeymour p
      (fun i ↦ (h i).1) (fun i ↦ (r i).1) z a
      hA0P hP0 hAH hAR hPR hAZ (q + 1) (by omega)
  have hPRows : all 7 (fun q => aNonSeymour bits (q + 8)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    exact aNonSeymour_coreBits_true G C hG hPB hEpsilon hNoSeymour p
      (fun i ↦ (h i).1) (fun i ↦ (r i).1) z a
      hA0P hP0 hAH hAR hPR hAZ (q + 8) (by omega)
  have hCore : highDefectCore bits = true := by
    rw [highDefectCore]
    simpa only [Bool.and_eq_true] using
      ⟨⟨⟨⟨⟨⟨hFixed, hDeletion⟩, hMissing⟩, hRows⟩, hPRows⟩,
        hOrderP⟩, hOrderZ⟩
  have hMissingBits : FourZHighDefect.totalMissingPZ bits =
      BitVec.ofNat 8 missing := by
    apply BitVec.eq_of_toNat_eq
    simp only [missing, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : missing < 2 ^ 8)]
  have hCoreAt : highDefectCoreAtMissing missing bits = true := by
    rw [highDefectCoreAtMissing]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hCore, hMissingBits⟩
  have hDegreeNat := pDegreeSum_coreBits_toNat G C hG hPB hEpsilon p h
    (fun i ↦ (r i).1) z (fun i ↦ (a i).1)
  change (FourZHighDefect.pDegreeSum bits).toNat = degreeSum at hDegreeNat
  have hDegreeBits : FourZHighDefect.pDegreeSum bits =
      BitVec.ofNat 8 degreeSum := by
    apply BitVec.eq_of_toNat_eq
    rw [hDegreeNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hCoreAtDegree : highDefectCoreAtMissingDegree missing degreeSum bits = true := by
    rw [highDefectCoreAtMissingDegree]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hCoreAt, hDegreeBits⟩
  exact impossible_of_encodedCore G.Adj (fun i ↦ (p i).1)
    (fun i ↦ (h i).1) (fun i ↦ (r i).1) (fun i ↦ (z i).1)
    (fun i ↦ (a i).1) missing degreeSum hMissingLower hMissingUpper
    hDegreeLower hDegreeUpper hCoreAtDegree

theorem tightEpsilonZeroXThreeHighDefectImpossible
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hEpsilon : epsilonS G C = 0)
    (hx : C.x = 3) (hz : C.z = 4)
    (hHighDefect : 2 ≤ 28 - edgeCount G C.P C.Z) : False := by
  classical
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 4 := by exact hz
  have hHCard : C.H.card = 4 := by
    change C.h = 4
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 1 := hk
  have hXCard : C.X.card = 3 := hx
  have hRCard : C.R.card = 3 := by
    have hXR := Digraph.LocalConfiguration.x_add_card_R_eq_six_of_k_eq_one
      (G := G) C hG.1 hRootDegree hk
    change C.X.card = 3 at hx
    change C.X.card + C.R.card = 6 at hXR
    omega
  let eP : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let p := FourZExactSevenLabels.sortedAllFinsetEquiv
    G.outdegree (directCount G C.H) C.P eP
  let eZ : Fin 4 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let z := sortedZFinsetEquiv G (fun i => (p i).1) C.Z eZ
  let eA1 : Fin 1 ≃ {v : V // v ∈ C.A1} := finsetEquivFin C.A1 hA1Card
  let eX : Fin 3 ≃ {v : V // v ∈ C.X} := finsetEquivFin C.X hXCard
  let h : Fin 4 ≃ {v : V // v ∈ C.H} :=
    FourZHighDefectGraphBridge.hLabelEquiv G C hHCard eA1 eX
  let eR : Fin 3 ≃ {v : V // v ∈ C.R} := finsetEquivFin C.R hRCard
  let a : Fin 8 ≃ {v : V // v ∈ C.A} :=
    FourZHighDefectGraphBridge.aLabelEquiv G C hACard h eR
  have hH0A1 : (h 0).1 ∈ C.A1 := by
    rw [show (h 0).1 = (eA1 0).1 by
      exact FourZHighDefectGraphBridge.hLabelEquiv_zero G C hHCard eA1 eX]
    exact (eA1 0).2
  have hH1X : (h 1).1 ∈ C.X := by
    rw [show (h 1).1 = (eX 0).1 by
      exact FourZHighDefectGraphBridge.hLabelEquiv_one G C hHCard eA1 eX]
    exact (eX 0).2
  have hH2X : (h 2).1 ∈ C.X := by
    rw [show (h 2).1 = (eX 1).1 by
      exact FourZHighDefectGraphBridge.hLabelEquiv_two G C hHCard eA1 eX]
    exact (eX 1).2
  have hH3X : (h 3).1 ∈ C.X := by
    rw [show (h 3).1 = (eX 2).1 by
      exact FourZHighDefectGraphBridge.hLabelEquiv_three G C hHCard eA1 eX]
    exact (eX 2).2
  have hA0 : (a 0).1 = C.a1 :=
    FourZHighDefectGraphBridge.aLabelEquiv_zero G C hACard h eR
  have hAH : ∀ i : Fin 4, (a ⟨i + 1, by omega⟩).1 = (h i).1 := by
    intro i
    exact FourZHighDefectGraphBridge.aLabelEquiv_h G C hACard h eR i
  have hAR : ∀ i : Fin 3, (a ⟨i + 5, by omega⟩).1 = (eR i).1 := by
    intro i
    exact FourZHighDefectGraphBridge.aLabelEquiv_r G C hACard h eR i
  have hCountLt : ∀ v, directCount G C.H v < 256 := by
    intro v
    have hv : directCount G C.H v ≤ 4 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    omega
  have hSortedP : ∀ q : Nat, (hq : q < 6) →
      G.outdegree (p ⟨q + 1, by omega⟩).1 ≤ G.outdegree (p ⟨q, by omega⟩).1 ∧
        (G.outdegree (p ⟨q, by omega⟩).1 = G.outdegree (p ⟨q + 1, by omega⟩).1 →
          directCount G C.H (p ⟨q + 1, by omega⟩).1 ≤
            directCount G C.H (p ⟨q, by omega⟩).1) := by
    exact FourZExactSevenLabels.sortedAllFinsetEquiv_order
      G.outdegree (directCount G C.H)
      C.P eP hCountLt
  have hOrderP := orderedP_coreBits_true G C hG hPB hEpsilon p h
    (fun i => (eR i).1) z (fun i => (a i).1) hSortedP
  have hSortedZ : ∀ q : Nat, (hq : q < 3) →
      (zColumnCode G (fun i => (p i).1) (z ⟨q + 1, by omega⟩).1).toNat ≤
        (zColumnCode G (fun i => (p i).1) (z ⟨q, by omega⟩).1).toNat := by
    intro q hq
    exact sortedZ_code_anti G (fun i => (p i).1) C.Z eZ
      (Fin.mk_le_mk.mpr (by omega) :
        (⟨q, by omega⟩ : Fin 4) ≤ ⟨q + 1, by omega⟩)
  have hOrderZ := orderedZ_coreBits_true G C (fun i => (p i).1)
    (fun i => (h i).1) (fun i => (eR i).1) z (fun i => (a i).1) hSortedZ
  exact impossible_of_compatibleLabels G hBound C hG hPivot hMin hNoSeymour
    hRootDegree hPB hk hx hEpsilon hHighDefect p h eR z a hA0 hAH
    hH0A1 hH1X hH2X hH3X hAR hOrderP hOrderZ

end SeymourEight.FourZHighDefectAssembly
