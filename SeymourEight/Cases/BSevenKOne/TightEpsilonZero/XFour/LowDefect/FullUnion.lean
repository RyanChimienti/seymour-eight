import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.LowDefect.ExactSeven
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Labels
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.FullRows.Dispatch
import SeymourEight.Shared.SameStatusKing

set_option linter.style.header false

/-!
# Compact certificate bridge for the full three-`Z` branch

If the complete external `Z`-union has at least eight vertices, its members
which are not direct neighbors of `p` give the inequality
`q_p + 6 ≤ d⁺_P(p) + 2 d⁺_H(p)`.  This file transports that inequality and
the ordinary local counts into the 119-bit checked core.
-/

namespace SeymourEight.ThreeZFullUnion

open CertificateBridge FiveZExactGraphBridge FiveZExactPBridge
  FourZExactSevenLabels Shared TerminalAlphaBeta TerminalCore
  TerminalCoreBridge TerminalCoreGraphBridge ThreeZFullCore
  BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The full external union supplies the subtraction-free per-`P` inequality
used by the compact core. -/
theorem equation_of_full_union (C : G.LocalConfiguration)
    (hFullPZ : ∀ p ∈ C.P, ∀ z ∈ C.Z, G.Adj p z)
    (hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P)
    (hEpsilon : epsilonS G C = 0)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hDegree : ∀ p ∈ C.P, G.outdegree p =
      3 + directCount G C.H p + directCount G C.P p)
    (hWCard : 8 ≤ (zExternalUnion G C).card) :
    ∀ p ∈ C.P, qCount G C.P C.H p + 6 ≤
      directCount G C.P p + 2 * directCount G C.H p := by
  intro p hp
  let W := zExternalUnion G C
  let Wnew := W.filter fun v ↦ ¬G.Adj p v
  have hWP : Disjoint W C.P := (disjoint_P_zExternalUnion G C).symm
  have hWZ : Disjoint W C.Z := (disjoint_Z_zExternalUnion G C).symm
  have hWnewSecond : Wnew ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvW, hNotAdj⟩
    have hvReach := (Finset.mem_sdiff.mp hvW).1
    obtain ⟨z, hzZ, hzv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hvp : v ≠ p := by
      intro hEq
      subst v
      exact (Finset.disjoint_left.mp hWP) hvW hp
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨z, hFullPZ p hp z hzZ, hzv⟩, hNotAdj, hvp⟩
  have hQSecond : secondNeighborsThrough G C.P (C.P ∪ C.H) p ⊆
      G.secondOutNeighborFinset p :=
    secondNeighborsThrough_subset_secondOutNeighborFinset
      G C.P (C.P ∪ C.H) p
  have hDisjoint : Disjoint Wnew
      (secondNeighborsThrough G C.P (C.P ∪ C.H) p) := by
    rw [Finset.disjoint_left]
    intro v hvWnew hvQ
    have hvW : v ∈ W := (Finset.mem_filter.mp hvWnew).1
    have hvP : v ∈ C.P := (Finset.mem_filter.mp hvQ).1
    exact (Finset.disjoint_left.mp hWP) hvW hvP
  have hSecondCard : Wnew.card + qCount G C.P C.H p ≤
      G.secondOutdegree p := by
    have hSubset : Wnew ∪ secondNeighborsThrough G C.P (C.P ∪ C.H) p ⊆
        G.secondOutNeighborFinset p :=
      Finset.union_subset hWnewSecond hQSecond
    have hCard := Finset.card_le_card hSubset
    rw [Finset.card_union_of_disjoint hDisjoint] at hCard
    exact hCard
  have hWSplit : (W.filter (G.Adj p)).card + Wnew.card = W.card :=
    Finset.card_filter_add_card_filter_not (G.Adj p)
  have hDirectW := direct_W_bound_of_captured G C hCaptured W hWZ hWP p hp
  have hNoRoot : epsilonAt G p C.s = 0 := by
    simp [epsilonAt, no_P_to_s_of_epsilonS_zero G C hEpsilon p hp]
  have hSecondLt : G.secondOutdegree p < G.outdegree p := by
    have hNot : ¬G.IsSeymourVertex p := fun hpS ↦ hNoSeymour ⟨p, hpS⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  have hDeg := hDegree p hp
  dsimp [W, Wnew] at hWSplit hSecondCard hDirectW ⊢
  rw [hNoRoot] at hDirectW
  omega

omit [DecidableEq V] in
theorem fullRetainedDegree_coreBits_toNat (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H}) (i : Nat) (hi : i < 7)
    (hDegree : G.outdegree (eP ⟨i, hi⟩).1 =
      3 + directCount G H (eP ⟨i, hi⟩).1 +
        directCount G P (eP ⟨i, hi⟩).1)
    (hDegreeLt : G.outdegree (eP ⟨i, hi⟩).1 < 256) :
    (ThreeZFullCore.retainedDegree
      (coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)) i).toNat =
        G.outdegree (eP ⟨i, hi⟩).1 := by
  classical
  have hH := labelledPToHCount_toNat G (fun j ↦ (eP j).1) H eH i
  rw [pAt_of_lt (fun j ↦ (eP j).1) i hi] at hH
  have hP := labelledPOutCount_toNat G P eP i
  rw [pAt_of_lt (fun j ↦ (eP j).1) i hi] at hP
  let hCount := labelledPToHCount G.Adj (fun j ↦ (eP j).1)
    (fun j ↦ (eH j).1) i
  let pCount := labelledPOutCount G.Adj (fun j ↦ (eP j).1) i
  have hH' : hCount.toNat = directCount G H (eP ⟨i, hi⟩).1 := hH
  have hP' : pCount.toNat = directCount G P (eP ⟨i, hi⟩).1 := hP
  rw [ThreeZFullCore.retainedDegree, pToHCount_coreBits G.Adj _ _ i hi,
    pOutCount_coreBits G.Adj _ _ i hi]
  change ((3 : BitVec 8) + hCount + pCount).toNat = _
  have hThree : (3 : BitVec 8).toNat = 3 := by decide
  simp only [BitVec.toNat_add, Nat.reducePow, hThree]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

omit [Fintype V] in
theorem fullEquation_coreBits_true (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H}) (i : Nat) (hi : i < 7)
    (hEquation : qCount G P H (eP ⟨i, hi⟩).1 + 6 ≤
      directCount G P (eP ⟨i, hi⟩).1 +
        2 * directCount G H (eP ⟨i, hi⟩).1) :
    ThreeZFullCore.equationAt
      (coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)) i = true := by
  classical
  have hSecond := labelledSecondPCount_toNat_le_qCount G P H eP eH i hi
  have hP := labelledPOutCount_toNat G P eP i
  rw [pAt_of_lt (fun j ↦ (eP j).1) i hi] at hP
  have hH := labelledPToHCount_toNat G (fun j ↦ (eP j).1) H eH i
  rw [pAt_of_lt (fun j ↦ (eP j).1) i hi] at hH
  rw [ThreeZFullCore.equationAt,
    secondPCount_coreBits G.Adj _ _ i hi,
    pOutCount_coreBits G.Adj _ _ i hi,
    pToHCount_coreBits G.Adj _ _ i hi]
  have hPCard : P.card = 7 := by simpa using (Fintype.card_congr eP).symm
  have hHCard : H.card = 5 := by simpa using (Fintype.card_congr eH).symm
  have hQLe : qCount G P H (eP ⟨i, hi⟩).1 ≤ 7 := by
    unfold qCount secondNeighborsThrough
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hSecondLe :
      (labelledSecondPCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i).toNat ≤ 7 := hSecond.trans hQLe
  have hPLe :
      (labelledPOutCount G.Adj (fun j ↦ (eP j).1) i).toNat ≤ 7 := by
    rw [hP]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
  have hHLe :
      (labelledPToHCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i).toNat ≤ 5 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  have hSix : (6 : BitVec 8).toNat = 6 := by decide
  have hTwo : (2 : BitVec 8).toNat = 2 := by decide
  have hLeft :
      (labelledSecondPCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i + 6).toNat =
      (labelledSecondPCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i).toNat + 6 := by
    rw [BitVec.toNat_add, hSix, Nat.mod_eq_of_lt]
    omega
  have hMul :
      ((2 : BitVec 8) * labelledPToHCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i).toNat =
      2 * (labelledPToHCount G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1) i).toNat := by
    rw [BitVec.toNat_mul, hTwo, Nat.mod_eq_of_lt]
    omega
  have hRight :
      (labelledPOutCount G.Adj (fun j ↦ (eP j).1) i +
        2 * labelledPToHCount G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) i).toNat =
      (labelledPOutCount G.Adj (fun j ↦ (eP j).1) i).toNat +
        2 * (labelledPToHCount G.Adj (fun j ↦ (eP j).1)
          (fun j ↦ (eH j).1) i).toNat := by
    rw [BitVec.toNat_add, hMul, Nat.mod_eq_of_lt]
    omega
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [hLeft, hRight]
  rw [hP, hH]
  omega

omit [DecidableEq V] in
theorem fullOrdered_coreBits_true (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (hDegree : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (eP ⟨i, hi⟩).1 =
        3 + directCount G H (eP ⟨i, hi⟩).1 +
          directCount G P (eP ⟨i, hi⟩).1)
    (hDegreeLt : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (eP ⟨i, hi⟩).1 < 256)
    (hSorted : ∀ q : Nat, (hq : q < 6) →
      G.outdegree (eP ⟨q + 1, by omega⟩).1 ≤
          G.outdegree (eP ⟨q, by omega⟩).1 ∧
        (G.outdegree (eP ⟨q, by omega⟩).1 =
            G.outdegree (eP ⟨q + 1, by omega⟩).1 →
          directCount G H (eP ⟨q + 1, by omega⟩).1 ≤
            directCount G H (eP ⟨q, by omega⟩).1)) :
    ThreeZFullCore.interchangeableOrdered
      (coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)) = true := by
  classical
  let bits := coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)
  have hPair : ∀ q : Nat, (hq : q < 6) →
      ((ThreeZFullCore.retainedDegree bits (q + 1)).ule
          (ThreeZFullCore.retainedDegree bits q) &&
        (!(ThreeZFullCore.retainedDegree bits q ==
            ThreeZFullCore.retainedDegree bits (q + 1)) ||
          (pToHCount bits (q + 1)).ule (pToHCount bits q))) = true := by
    intro q hq
    have hd0 := fullRetainedDegree_coreBits_toNat G P H eP eH q (by omega)
      (hDegree q (by omega)) (hDegreeLt q (by omega))
    have hd1 := fullRetainedDegree_coreBits_toNat G P H eP eH (q + 1) (by omega)
      (hDegree (q + 1) (by omega)) (hDegreeLt (q + 1) (by omega))
    change (ThreeZFullCore.retainedDegree bits q).toNat = _ at hd0
    change (ThreeZFullCore.retainedDegree bits (q + 1)).toNat = _ at hd1
    have hh0 := labelledPToHCount_toNat G (fun j ↦ (eP j).1) H eH q
    rw [pAt_of_lt (fun j ↦ (eP j).1) q (by omega)] at hh0
    have hh0' : (pToHCount bits q).toNat =
        directCount G H (eP ⟨q, by omega⟩).1 := by
      change (pToHCount (coreBits G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1)) q).toNat = _
      rw [pToHCount_coreBits G.Adj _ _ q (by omega)]
      exact hh0
    have hh1 := labelledPToHCount_toNat G (fun j ↦ (eP j).1) H eH (q + 1)
    rw [pAt_of_lt (fun j ↦ (eP j).1) (q + 1) (by omega)] at hh1
    have hh1' : (pToHCount bits (q + 1)).toNat =
        directCount G H (eP ⟨q + 1, by omega⟩).1 := by
      change (pToHCount (coreBits G.Adj (fun j ↦ (eP j).1)
        (fun j ↦ (eH j).1)) (q + 1)).toNat = _
      rw [pToHCount_coreBits G.Adj _ _ (q + 1) (by omega)]
      exact hh1
    have hs := hSorted q hq
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      BitVec.ule_eq_decide, decide_eq_true_eq]
    constructor
    · simpa [hd0, hd1] using hs.1
    · by_cases heq : ThreeZFullCore.retainedDegree bits q =
          ThreeZFullCore.retainedDegree bits (q + 1)
      · right
        have hdeg : G.outdegree (eP ⟨q, by omega⟩).1 =
            G.outdegree (eP ⟨q + 1, by omega⟩).1 := by
          rw [← hd0, ← hd1, heq]
        simpa [hh0', hh1'] using hs.2 hdeg
      · left
        exact Bool.eq_false_iff.mpr (fun hb ↦ heq (beq_iff_eq.mp hb))
  have h0 := hPair 0 (by omega)
  have h1 := hPair 1 (by omega)
  have h2 := hPair 2 (by omega)
  have h3 := hPair 3 (by omega)
  have h4 := hPair 4 (by omega)
  have h5 := hPair 5 (by omega)
  simp only [Bool.and_eq_true] at h0 h1 h2 h3 h4 h5
  simp only [ThreeZFullCore.interchangeableOrdered, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

/-- Package labelled graph counts as a satisfying assignment of the compact
full-three-`Z` Boolean core. -/
theorem core_true_of_graphData (P H : Finset V)
    (eP : Fin 7 ≃ {v : V // v ∈ P})
    (eH : Fin 5 ≃ {v : V // v ∈ H})
    (alpha internalEdges degreeSum : Nat)
    (hLoopless : ∀ u, ¬G.Adj u u)
    (hAnti : ∀ u v, G.Adj u v → ¬G.Adj v u)
    (hInternal : edgeCount G P P = internalEdges)
    (hPToH : edgeCount G P H + alpha = 17)
    (hHToP : 18 ≤ edgeCount G H P)
    (hDegree : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (eP ⟨i, hi⟩).1 =
        3 + directCount G H (eP ⟨i, hi⟩).1 +
          directCount G P (eP ⟨i, hi⟩).1)
    (hBounds : ∀ i : Nat, (hi : i < 7) →
      8 ≤ G.outdegree (eP ⟨i, hi⟩).1 ∧
        G.outdegree (eP ⟨i, hi⟩).1 ≤ 11)
    (hEquation : ∀ i : Nat, (hi : i < 7) →
      qCount G P H (eP ⟨i, hi⟩).1 + 6 ≤
        directCount G P (eP ⟨i, hi⟩).1 +
          2 * directCount G H (eP ⟨i, hi⟩).1)
    (hSorted : ∀ q : Nat, (hq : q < 6) →
      G.outdegree (eP ⟨q + 1, by omega⟩).1 ≤
          G.outdegree (eP ⟨q, by omega⟩).1 ∧
        (G.outdegree (eP ⟨q, by omega⟩).1 =
            G.outdegree (eP ⟨q + 1, by omega⟩).1 →
          directCount G H (eP ⟨q + 1, by omega⟩).1 ≤
            directCount G H (eP ⟨q, by omega⟩).1))
    (hDegreeSum : ∑ i : Fin 7, G.outdegree (eP i).1 = degreeSum)
    (hAlphaLt : alpha < 256) (hInternalLt : internalEdges < 256)
    (hDegreeSumLt : degreeSum < 256) :
    ThreeZFullCore.core
      (coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1))
      (BitVec.ofNat 8 alpha) (BitVec.ofNat 8 internalEdges)
      (BitVec.ofNat 8 degreeSum) = true := by
  let bits := coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)
  have hOrientedP := orientedOnP_coreBits G.Adj
    (fun j ↦ (eP j).1) (fun j ↦ (eH j).1) hLoopless hAnti
  have hOrientedPH := orientedBetweenPAndH_coreBits G.Adj
    (fun j ↦ (eP j).1) (fun j ↦ (eH j).1) hAnti
  have hPPNat : (totalPOut bits).toNat = edgeCount G P P := by
    rw [totalPOut_coreBits G.Adj]
    exact labelledTotalPOut_toNat G P eP (by
      rw [hInternal]
      exact hInternalLt)
  have hPHNat : (totalPToH bits).toNat = edgeCount G P H := by
    rw [totalPToH_coreBits G.Adj]
    exact labelledTotalPToH_toNat G P H eP eH (by omega)
  have hHPNat : (totalHToP bits).toNat = edgeCount G H P := by
    rw [totalHToP_coreBits G.Adj]
    exact labelledTotalHToP_toNat G P H eP eH (by
      have hPCard : P.card = 7 := by simpa using (Fintype.card_congr eP).symm
      have hHCard : H.card = 5 := by simpa using (Fintype.card_congr eH).symm
      exact (edgeCount_le_card_mul_card G H P).trans_lt (by
        rw [hPCard, hHCard]
        omega))
  have hPP : totalPOut bits = BitVec.ofNat 8 internalEdges := by
    apply BitVec.eq_of_toNat_eq
    rw [hPPNat, hInternal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hInternalLt]
  have hPH : totalPToH bits + BitVec.ofNat 8 alpha = 17 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, hPHNat, BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt hAlphaLt]
    have hSeventeen : (17 : BitVec 8).toNat = 17 := by decide
    rw [hSeventeen, Nat.mod_eq_of_lt (by omega)]
    omega
  have hHP : (18 : BitVec 8).ule (totalHToP bits) = true := by
    have hEighteen : (18 : BitVec 8).toNat = 18 := by decide
    simpa only [BitVec.ule_eq_decide, decide_eq_true_eq, hHPNat,
      hEighteen] using hHToP
  have hAt : ∀ i : Nat, (hi : i < 7) →
      ((8 : BitVec 8).ule (ThreeZFullCore.retainedDegree bits i) &&
        (ThreeZFullCore.retainedDegree bits i).ule 11 &&
        ThreeZFullCore.equationAt bits i) = true := by
    intro i hi
    have hd := fullRetainedDegree_coreBits_toNat G P H eP eH i hi
      (hDegree i hi) (by have := (hBounds i hi).2; omega)
    have heq := fullEquation_coreBits_true G P H eP eH i hi (hEquation i hi)
    simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq]
    have hlo : 8 ≤ (ThreeZFullCore.retainedDegree bits i).toNat := by
      rw [hd]
      exact (hBounds i hi).1
    have hhi : (ThreeZFullCore.retainedDegree bits i).toNat ≤ 11 := by
      rw [hd]
      exact (hBounds i hi).2
    exact ⟨⟨hlo, hhi⟩, heq⟩
  have hAll : allSeven (fun i ↦
      (8 : BitVec 8).ule (ThreeZFullCore.retainedDegree bits i) &&
      (ThreeZFullCore.retainedDegree bits i).ule 11 &&
      ThreeZFullCore.equationAt bits i) = true := by
    have h0 := hAt 0 (by omega)
    have h1 := hAt 1 (by omega)
    have h2 := hAt 2 (by omega)
    have h3 := hAt 3 (by omega)
    have h4 := hAt 4 (by omega)
    have h5 := hAt 5 (by omega)
    have h6 := hAt 6 (by omega)
    simp only [allSeven, Bool.and_eq_true] at h0 h1 h2 h3 h4 h5 h6 ⊢
    exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  have hOrder := fullOrdered_coreBits_true G P H eP eH hDegree
    (fun i hi ↦ by have := (hBounds i hi).2; omega) hSorted
  have hRetained : ∀ i : Nat, (hi : i < 7) →
      (ThreeZFullCore.retainedDegree bits i).toNat =
        G.outdegree (eP ⟨i, hi⟩).1 := by
    intro i hi
    exact fullRetainedDegree_coreBits_toNat G P H eP eH i hi
      (hDegree i hi) (by have := (hBounds i hi).2; omega)
  have hNatSum :
      (ThreeZFullCore.retainedDegree bits 0).toNat +
      (ThreeZFullCore.retainedDegree bits 1).toNat +
      (ThreeZFullCore.retainedDegree bits 2).toNat +
      (ThreeZFullCore.retainedDegree bits 3).toNat +
      (ThreeZFullCore.retainedDegree bits 4).toNat +
      (ThreeZFullCore.retainedDegree bits 5).toNat +
      (ThreeZFullCore.retainedDegree bits 6).toNat = degreeSum := by
    rw [hRetained 0 (by omega), hRetained 1 (by omega),
      hRetained 2 (by omega), hRetained 3 (by omega),
      hRetained 4 (by omega), hRetained 5 (by omega),
      hRetained 6 (by omega)]
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hDegreeSum
  have hSum : sumCountSeven (ThreeZFullCore.retainedDegree bits) =
      BitVec.ofNat 8 degreeSum := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sumCountSeven _ (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hDegreeSumLt]
    exact hNatSum
  have hPPBool : (totalPOut bits == BitVec.ofNat 8 internalEdges) = true := by
    simpa using hPP
  have hPHBool :
      (totalPToH bits + BitVec.ofNat 8 alpha == 17) = true := by
    simpa using hPH
  have hSumBool :
      (sumCountSeven (ThreeZFullCore.retainedDegree bits) ==
        BitVec.ofNat 8 degreeSum) = true := by
    simpa using hSum
  simp only [ThreeZFullCore.core, hOrientedP, hOrientedPH, hOrder,
    Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have hTotals :
      totalPOut (coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)) =
          BitVec.ofNat 8 internalEdges ∧
        totalPToH (coreBits G.Adj (fun j ↦ (eP j).1) (fun j ↦ (eH j).1)) +
          BitVec.ofNat 8 alpha = 17 := by
    exact ⟨hPP, hPH⟩
  aesop

/-- The `m=0`, external-union-at-least-eight graph branch is ruled out by
the compact checked dispatcher. -/
theorem impossible_of_full_union (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 3)
    (hEpsilon : epsilonS G C = 0)
    (hPZ : edgeCount G C.P C.Z = 21)
    (hWCard : 8 ≤ (zExternalUnion G C).card) : False := by
  classical
  have hPB := BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 3 := hz
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hFullPZ := ThreeZExactSeven.all_P_to_Z_of_edgeCount_twentyOne
    G C.P C.Z hPCard hZCard hPZ
  have hCaptured : ∀ p ∈ C.P,
      G.outNeighborFinset p ⊆ C.Z ∪ {C.s} ∪ C.H ∪ C.P := by
    intro p hp
    exact outgoingCaptured_of_p_eq_B G C hG hPB p hp
  have hDegree : ∀ p ∈ C.P, G.outdegree p =
      3 + directCount G C.H p + directCount G C.P p := by
    intro p hp
    rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon p hp]
    have hZCount : directCount G C.Z p = 3 := by
      unfold directCount internalFirstNeighbors
      have hEq : C.Z.filter (G.Adj p) = C.Z := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · exact fun hz ↦ hz.1
        · intro hz
          exact ⟨hz, hFullPZ p hp z hz⟩
      rw [hEq, hZCard]
    omega
  let alpha := 17 - edgeCount G C.P C.H
  let beta := 21 - edgeCount G C.P C.P
  have hPHUpper : edgeCount G C.P C.H ≤ 17 := by
    have hReverse := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    have hCross := cross_edgeCount_add_reverse_le G C.P C.H hG
    rw [hPCard, hHCard] at hCross
    simp [hx, Nat.choose] at hReverse
    omega
  have hPPUpper : edgeCount G C.P C.P ≤ 21 :=
    internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hAlpha : edgeCount G C.P C.H + alpha = 17 := by
    dsimp [alpha]
    omega
  have hBeta : edgeCount G C.P C.P + beta = 21 := by
    dsimp [beta]
    omega
  have hAccounting := degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ p ∈ C.P, epsilonAt G p C.s = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [epsilonAt, no_P_to_s_of_epsilonS_zero G C hEpsilon p hp]
  rw [hNoRoot, hPZ] at hAccounting
  have hDegreeLower : 56 ≤ ∑ p ∈ C.P, G.outdegree p := by
    calc
      56 = ∑ _p ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ p ∈ C.P, G.outdegree p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hMin p
  have hDefects : alpha + beta ≤ 3 := by omega
  have hDegreeSum : ∑ p ∈ C.P, G.outdegree p = 59 - alpha - beta := by
    omega
  have hBounds : ∀ p ∈ C.P, 8 ≤ G.outdegree p ∧ G.outdegree p ≤ 11 := by
    intro p hp
    have hTermLe : G.outdegree p - 8 ≤
        ∑ q ∈ C.P, (G.outdegree q - 8) :=
      Finset.single_le_sum (s := C.P) (f := fun q ↦ G.outdegree q - 8)
        (fun _ _ ↦ Nat.zero_le _) hp
    have hSumRewrite : (∑ q ∈ C.P, G.outdegree q) =
        56 + ∑ q ∈ C.P, (G.outdegree q - 8) := by
      calc
        _ = ∑ q ∈ C.P, (8 + (G.outdegree q - 8)) := by
          apply Finset.sum_congr rfl
          intro q hq
          have := hMin q
          omega
        _ = 56 + ∑ q ∈ C.P, (G.outdegree q - 8) := by
          rw [Finset.sum_add_distrib]
          simp [hPCard]
    have hExcessLe : ∑ q ∈ C.P, (G.outdegree q - 8) ≤ 3 := by
      rw [hDegreeSum] at hSumRewrite
      omega
    exact ⟨hMin p, by omega⟩
  have hHP : 18 ≤ edgeCount G C.H C.P := by
    have hc := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    simpa [hx, Nat.choose] using hc
  have hEquation := equation_of_full_union G C hFullPZ hCaptured hEpsilon
    hNoSeymour hDegree hWCard
  have hAlphaSmall : alpha ≤ 1 := by
    by_contra hAlpha
    have hAlphaLarge : 2 ≤ alpha := by omega
    let S := C.P.filter fun p ↦ G.outdegree p = 8
    have hSP : S ⊆ C.P := Finset.filter_subset _ _
    have hExcessRewrite : (∑ p ∈ C.P, G.outdegree p) =
        56 + ∑ p ∈ C.P, (G.outdegree p - 8) := by
      calc
        _ = ∑ p ∈ C.P, (8 + (G.outdegree p - 8)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have := hMin p
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hPCard]
    have hExcess : ∑ p ∈ C.P, (G.outdegree p - 8) =
        3 - alpha - beta := by
      rw [hDegreeSum] at hExcessRewrite
      omega
    have hCard := card_le_exact_degree_add_excess
      (V := V) C.P G.outdegree 8 (fun p _hp ↦ hMin p)
    change C.P.card ≤ S.card + ∑ p ∈ C.P, (G.outdegree p - 8) at hCard
    have hSNonempty : S.Nonempty := by
      apply Finset.card_pos.mp
      rw [hPCard, hExcess] at hCard
      omega
    have hMissingP := card_internalMissingPairs_add_edgeCount G C.P hG
    have hChoose : Nat.choose 7 2 = 21 := by decide
    rw [hPCard, hChoose] at hMissingP
    have hMissingMono := Finset.card_le_card
      (internalMissingPairs_mono G hSP)
    have hMissingS : (internalMissingPairs G S).card ≤ beta := by omega
    obtain ⟨p, hpS, hKing⟩ := exists_noRootStatus_king_bound
      G C.P S (fun _ ↦ 3) (directCount G C.H) 8 hSNonempty hSP hG
      (by
        intro q hqS
        have hq := Finset.mem_filter.mp hqS
        have hDegreeQ := hDegree q hq.1
        omega)
      (by
        intro q hqS
        have hq := Finset.mem_filter.mp hqS
        have hSecondLe :
            (internalSecondNeighbors (G := G) S q).card ≤
              qCount G C.P C.H q := by
          apply Finset.card_le_card
          exact (internalSecondNeighbors_mono G hSP q).trans
            (internalSecondNeighbors_subset_secondNeighborsThrough
              G C.P C.H q)
        have hEq := hEquation q hq.1
        have hDegreeQ := hDegree q hq.1
        omega)
    rw [hPCard, hExcess] at hCard
    omega
  by_cases hLogical : alpha + beta = 3 ∧ beta ≤ 1
  · have hDegreeSumTight : ∑ p ∈ C.P, G.outdegree p = C.P.card * 8 := by
      rw [hDegreeSum, hPCard]
      omega
    have hDegreeEight : ∀ p ∈ C.P, G.outdegree p = 8 :=
      pointwise_eq_of_sum_eq_card_mul C.P G.outdegree 8
        (fun p hp ↦ hMin p) hDegreeSumTight
    have hPNonempty : C.P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hpP, hKing⟩ :=
      exists_internalReachWithinTwo_add_edgeDefect_ge G C.P hPNonempty hG
    rw [hPCard] at hKing
    have hChoose : Nat.choose 7 2 = 21 := by decide
    rw [hChoose] at hKing
    have hSecondLe :
        (internalSecondNeighbors (G := G) C.P p).card ≤ qCount G C.P C.H p :=
      Finset.card_le_card
        (internalSecondNeighbors_subset_secondNeighborsThrough G C.P C.H p)
    rw [card_internalReachWithinTwo G C.P p hG] at hKing
    have hEq := hEquation p hpP
    have hDeg := hDegree p hpP
    have hEight := hDegreeEight p hpP
    omega
  · have hCertified : alpha + beta ≤ 2 ∨ 2 ≤ beta := by omega
    let eP : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
    let p := sortedAllFinsetEquiv G.outdegree (directCount G C.H) C.P eP
    let h : Fin 5 ≃ {v : V // v ∈ C.H} := finsetEquivFin C.H hHCard
    have hCountLt : ∀ v, directCount G C.H v < 256 := by
      intro v
      have := (Finset.card_le_card
        (Finset.filter_subset (p := G.Adj v) C.H)).trans_eq hHCard
      change (C.H.filter (G.Adj v)).card < 256
      omega
    have hSorted := sortedAllFinsetEquiv_order G.outdegree (directCount G C.H)
      C.P eP hCountLt
    have hDegreeLabel : ∀ i : Nat, (hi : i < 7) →
        G.outdegree (p ⟨i, hi⟩).1 =
          3 + directCount G C.H (p ⟨i, hi⟩).1 +
            directCount G C.P (p ⟨i, hi⟩).1 := by
      intro i hi
      exact hDegree (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2
    have hBoundsLabel : ∀ i : Nat, (hi : i < 7) →
        8 ≤ G.outdegree (p ⟨i, hi⟩).1 ∧ G.outdegree (p ⟨i, hi⟩).1 ≤ 11 := by
      intro i hi
      exact hBounds (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2
    have hEquationLabel : ∀ i : Nat, (hi : i < 7) →
        qCount G C.P C.H (p ⟨i, hi⟩).1 + 6 ≤
          directCount G C.P (p ⟨i, hi⟩).1 +
            2 * directCount G C.H (p ⟨i, hi⟩).1 := by
      intro i hi
      exact hEquation (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2
    have hDegreeSumLabel : ∑ i : Fin 7, G.outdegree (p i).1 =
        59 - alpha - beta := by
      rw [← sum_finset_eq_sum_fin C.P p G.outdegree]
      exact hDegreeSum
    let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
    have hCore := core_true_of_graphData G C.P C.H p h alpha (21 - beta)
      (59 - alpha - beta) hG.1 hG.2 (by omega) hAlpha hHP hDegreeLabel
      hBoundsLabel hEquationLabel hSorted hDegreeSumLabel (by omega) (by omega)
      (by omega)
    have hFalse := ThreeZFullCore.core_unsat alpha beta hDefects hAlphaSmall
      hCertified bits
    change ThreeZFullCore.core bits (BitVec.ofNat 8 alpha)
      (BitVec.ofNat 8 (21 - beta)) (BitVec.ofNat 8 (59 - alpha - beta)) = true
      at hCore
    rw [hFalse] at hCore
    contradiction

end SeymourEight.ThreeZFullUnion
