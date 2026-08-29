import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.BroadFourAssembly
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourLowPatterns
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourLowNormalization
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.BroadFourSharpKing

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Exact low-defect assembly for four `Z` vertices

The graph labels already sort the `P` rows and `Z` columns.  A tiny Boolean
normalization lemma therefore reduces defects one and two to their canonical
incidence masks before invoking the checked exact-defect certificates.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowBridge

open Shared BroadFourCore BroadFourLowCore BroadFourLabels
open BroadFourBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev graphBits (C : G.LocalConfiguration)
    (L : Labels G C) : Encoding :=
  coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)

private theorem pZIncidenceCode_eq (C : G.LocalConfiguration)
    (L : Labels G C) (z : Nat) (hz : z < 4) :
    pZIncidenceCode (graphBits G C L) z =
      BroadFourLabels.zIncidenceCode G (fun i => (L.p i).1)
        (L.z ⟨z, hz⟩).1 := by
  simp only [pZIncidenceCode, BroadFourLabels.zIncidenceCode]
  rw [pToZ_coreBits G.Adj _ _ _ 6 z (by omega) hz,
    pToZ_coreBits G.Adj _ _ _ 5 z (by omega) hz,
    pToZ_coreBits G.Adj _ _ _ 4 z (by omega) hz,
    pToZ_coreBits G.Adj _ _ _ 3 z (by omega) hz,
    pToZ_coreBits G.Adj _ _ _ 2 z (by omega) hz,
    pToZ_coreBits G.Adj _ _ _ 1 z (by omega) hz,
    pToZ_coreBits G.Adj _ _ _ 0 z (by omega) hz]
  simp

private theorem zFullKey_toNat (C : G.LocalConfiguration)
    (L : Labels G C) (z : Nat) (hz : z < 4) :
    (zFullKey (graphBits G C L) z).toNat =
      BroadFourLabels.zColumnKey G (fun i => (L.p i).1)
        (L.z ⟨z, hz⟩).1 := by
  rw [zFullKey, BroadFourLabels.zColumnKey, BitVec.toNat_add,
    BitVec.toNat_mul]
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [BroadFourBridge.zColumnCode_toNat G C L z hz,
    pZIncidenceCode_eq G C L z hz]
  have hDegree : BroadFourLabels.zColumnDegree G (fun i => (L.p i).1)
      (L.z ⟨z, hz⟩).1 ≤ 7 := by
    rw [BroadFourLabels.zColumnDegree]
    calc
      _ ≤ ∑ _i : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> omega
      _ = 7 := by simp
  have hCode : (BroadFourLabels.zIncidenceCode G (fun i => (L.p i).1)
      (L.z ⟨z, hz⟩).1).toNat < 128 := by
    exact (BroadFourLabels.zIncidenceCode G (fun i => (L.p i).1)
      (L.z ⟨z, hz⟩).1).toFin.isLt
  rw [show (128 : BitVec 16).toNat = 128 by decide,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem orderedZFull_true (C : G.LocalConfiguration)
    (L : Labels G C)
    (hOrder : ∀ q : Fin 3,
      BroadFourLabels.zColumnKey G (fun i => (L.p i).1)
          (L.z ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.zColumnKey G (fun i => (L.p i).1)
          (L.z ⟨q.val, by omega⟩).1) :
    orderedZFull (graphBits G C L) = true := by
  rw [orderedZFull, BroadFourBridge.all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zFullKey_toNat G C L (z + 1) (by omega),
    zFullKey_toNat G C L z (by omega)]
  exact hOrder ⟨z, hz⟩

private theorem pHIn_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (h : Nat) (hh : h < 6) :
    (pHIn (graphBits G C L) h).toNat =
      ∑ p ∈ C.P, if G.Adj p (L.a ⟨h + 1, by omega⟩).1 then 1 else 0 := by
  classical
  rw [pHIn, BroadFourBridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  calc
    (∑ i : Fin 7, if pToH (graphBits G C L) i h then 1 else 0) =
        ∑ i : Fin 7,
          if G.Adj (L.p i).1 (L.a ⟨h + 1, by omega⟩).1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pToH_coreBits G.Adj _ _ _ i h i.isLt hh]
      simp
    _ = ∑ x : {v : V // v ∈ C.P},
          if G.Adj x.1 (L.a ⟨h + 1, by omega⟩).1 then 1 else 0 := by
      exact Equiv.sum_comp L.p (fun x : {v : V // v ∈ C.P} ↦
        if G.Adj x.1 (L.a ⟨h + 1, by omega⟩).1 then 1 else 0)
    _ = ∑ p ∈ C.P,
          if G.Adj p (L.a ⟨h + 1, by omega⟩).1 then 1 else 0 := by
      rw [show (Finset.univ : Finset {v : V // v ∈ C.P}) = C.P.attach by
        exact Finset.univ_eq_attach C.P]
      exact C.P.sum_attach
        (fun p ↦ if G.Adj p (L.a ⟨h + 1, by omega⟩).1 then 1 else 0)

private theorem hRowKey_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hHCard : C.H.card = 6) (h : Nat) (hh : h < 6) :
    (hRowKey (graphBits G C L) h).toNat =
      hDegreeKey G C (L.a ⟨h + 1, by omega⟩).1 := by
  rw [hRowKey, hDegreeKey, BitVec.toNat_add, BitVec.toNat_mul,
    hPOut_toNat G C L hHCard h hh,
    pHIn_toNat G C L h hh]
  have hOut : Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1 ≤
      C.P.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr L.p).symm
  have hIn : (∑ p ∈ C.P,
      if G.Adj p (L.a ⟨h + 1, by omega⟩).1 then 1 else 0) ≤ 7 := by
    calc
      _ ≤ ∑ _p ∈ C.P, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        split <;> omega
      _ = 7 := by simp [hPCard]
  rw [hPCard] at hOut
  change ((16 * Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1) % 256 +
      (∑ p ∈ C.P, if G.Adj p (L.a ⟨h + 1, by omega⟩).1 then 1 else 0)) %
      256 = 16 * Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1 +
      ∑ p ∈ C.P, if G.Adj p (L.a ⟨h + 1, by omega⟩).1 then 1 else 0
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem zFour_impossible
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 2) (hr : C.r = 7)
    (hx : C.x = 4) (hNoRoot : epsilonS G C = 0)
    (hy : BSevenKTwo.y G C = 0) (hz : C.z = 4) : False := by
  have hPB : C.P = C.B :=
    RepeatedSharedOmissionBridge.p_eq_B G C hBCard hr
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 2 := by
    change C.A1.card = 2 at hk
    exact hk
  have hXCard : C.X.card = 4 := by
    change C.X.card = 4 at hx
    exact hx
  have hRBase := BSevenKTwo.x_add_card_R_eq_five G C hG hRootDegree hk
  have hRCard : C.R.card = 1 := by omega
  have hHCard := BSevenKTwo.H_card_eq_x_add_two G C hk
  rw [hx] at hHCard
  have hZCard : C.Z.card = 4 := by
    change C.Z.card = 4 at hz
    exact hz
  let L := canonicalLabels G C hPCard hACard hA1Card hXCard hRCard
    hHCard hZCard
  have hPOrder : ∀ q : Fin 6,
      BroadFourLabels.pKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.pKey G C (L.p ⟨q.val, by omega⟩).1 := by
    intro q
    exact canonicalLabels_p_order G C hPCard hACard hA1Card hXCard hRCard
      hHCard hZCard q q.isLt
  have hZOrder : ∀ q : Fin 3,
      BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.zColumnDegree G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val, by omega⟩).1 := by
    intro q
    exact canonicalLabels_z_order G C hPCard hACard hA1Card hXCard hRCard
      hHCard hZCard q q.isLt
  have hZKeyOrder : ∀ q : Fin 3,
      BroadFourLabels.zColumnKey G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val + 1, by omega⟩).1 ≤
        BroadFourLabels.zColumnKey G (fun i ↦ (L.p i).1)
          (L.z ⟨q.val, by omega⟩).1 := by
    intro q
    exact canonicalLabels_z_key_order G C hPCard hACard hA1Card hXCard
      hRCard hHCard hZCard q q.isLt
  let bits := graphBits G C L
  have hTwentyFive := twentyFive_le_H_to_P G C hG hMin hRootDegree hk hx
    hy hPB
  have hHPUpper := H_to_P_add_externalMissing_le_thirtyFive G C hG hMin
    hPB hNoRoot hPCard hZCard hHCard
  have hBroad : broadCore bits = true := by
    simpa [bits] using broadCore_true G C L hG hMin hNoSeymour hPivot hPB hk
      hXCard hNoRoot hHCard hPCard hZCard (by omega) hPOrder hZOrder
  have hM : (externalMissing bits).toNat =
      28 - edgeCount G C.P C.Z := by
    simpa [bits] using externalMissing_toNat G C L hG hHCard
  have hOP : orderedP bits = true := by
    have hRoot := edgeCount_P_root_zero G C hNoRoot
    simpa [bits] using orderedP_true G C L hG hPB hRoot hHCard hPOrder
  have hOZ : orderedZ bits = true := by
    simpa [bits] using orderedZ_true G C L hZOrder
  have hOZFull : orderedZFull bits = true := by
    simpa [bits] using BroadFourLowBridge.orderedZFull_true G C L hZKeyOrder
  have hSharp : sharpKing bits = true := by
    exact sharpKing_of_orientedP bits (by
      simpa [bits] using orientedP_true G C L hG)
  have hOrderedH : orderedHClasses bits = true := by
    rw [orderedHClasses, Bool.and_eq_true]
    constructor
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hRowKey_toNat G C L hHCard 1 (by omega),
        hRowKey_toNat G C L hHCard 0 (by omega)]
      simpa [L] using canonicalLabels_aOne_key_order G C hPCard hACard
        hA1Card hXCard hRCard hHCard hZCard
    · rw [BroadFourBridge.all_eq_true_iff]
      intro i hi
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hRowKey_toNat G C L hHCard (i + 3) (by omega),
        hRowKey_toNat G C L hHCard (i + 2) (by omega)]
      simpa [L] using canonicalLabels_x_key_order G C hPCard hACard
        hA1Card hXCard hRCard hHCard hZCard i hi
  have hHP : (totalHToP bits).toNat = edgeCount G C.H C.P := by
    simpa [bits] using totalHToP_toNat G C L hHCard
  have hLowerBool : (25 : BitVec 8).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHP]
    exact hTwentyFive
  have hUpperBool :
      (totalHToP bits + externalMissing bits).ule 35 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
    rw [hHP, hM]
    have hLt : edgeCount G C.H C.P +
        (28 - edgeCount G C.P C.Z) < 256 := by omega
    rw [Nat.mod_eq_of_lt hLt]
    exact hHPUpper
  have hBounds : lowHPBounds bits = true := by
    rw [lowHPBounds, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hOrderedH, hLowerBool⟩, hUpperBool⟩
  have contradictionAt (mode : BitVec 3)
      (hPattern : selectedLowPattern mode bits = true) : False := by
    have hCore : selectedLowPatternCore mode bits = true := by
      simp [selectedLowPatternCore, hBroad, hSharp, hBounds, hOZFull,
        hPattern]
    rw [selectedLowPattern_unsat mode bits] at hCore
    exact Bool.noConfusion hCore
  by_cases hLow : 28 - edgeCount G C.P C.Z ≤ 2
  · have hMBool : (externalMissing bits).ule 2 = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [show (2 : BitVec 8).toNat = 2 by decide, hM]
      exact hLow
    have hCover := selectedLowPattern_cover bits hOP hOZ hOZFull hMBool
    have hCases : selectedLowPattern 0 bits = true ∨
        selectedLowPattern 1 bits = true ∨
        selectedLowPattern 2 bits = true ∨
        selectedLowPattern 3 bits = true ∨
        selectedLowPattern 4 bits = true := by
      simpa [BroadFourCore.any, or_assoc] using hCover
    rcases hCases with h0 | h1 | h2 | h3 | h4
    · exact contradictionAt 0 h0
    · exact contradictionAt 1 h1
    · exact contradictionAt 2 h2
    · exact contradictionAt 3 h3
    · exact contradictionAt 4 h4
  · have hHigh : 3 ≤ 28 - edgeCount G C.P C.Z := by omega
    have hPattern : selectedLowPattern 5 bits = true := by
      change (3 : BitVec 8).ule (externalMissing bits) = true
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hM]
      exact hHigh
    exact contradictionAt 5 hPattern

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.BroadFourLowBridge
