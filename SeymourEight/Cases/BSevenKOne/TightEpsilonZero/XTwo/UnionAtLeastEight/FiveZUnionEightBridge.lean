import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.FiveZUnionEightCapacity
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactSelectedBridge
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.AllMissing
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.UnionAtLeastEight.HighMissingProjection
import SeymourEight.Shared.CertificateLabels
import SeymourEight.Shared.SameStatusKing

set_option linter.style.header false

/-!
# Graph bridge for the five-`Z`, union-at-least-eight certificate
-/

namespace SeymourEight.FiveZUnionEightBridge

open FiveZExactRisk FiveZExactCoreBridge FiveZExactGraphBridge
  FiveZExactGlobalBridge FiveZExactSelectedBridge
  FiveZUnionEightCapacity Shared BSevenKOneCounting CertificateBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def compressedPKey (C : G.LocalConfiguration) (u : V) : Nat :=
  (5 - directCount G C.Z u) * 32 + directCount G C.H u * 8 +
    directCount G C.P u

theorem pZOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (h : Fin 3 → V) (w : Fin 6 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    (pZOut (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a) source).toNat =
      directCount G C.Z (p ⟨source, hs⟩).1 := by
  rw [pZOut, toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.Z z
  intro j
  rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) w a source j hs j.isLt]
  simp

theorem pHOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (w : Fin 6 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    (pHOut (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a) source).toNat = directCount G C.H (p ⟨source, hs⟩).1 := by
  rw [pHOut, toNat_count_eq_fin_sum 3 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H h
  intro j
  rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    z w a source j hs j.isLt]
  simp

theorem pOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (h : Fin 3 → V) (w : Fin 6 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    (pOut (coreBits G.Adj (fun j ↦ (p j).1) h z w a) source).toNat =
      directCount G C.P (p ⟨source, hs⟩).1 := by
  rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) h z w a
    source j hs j.isLt]
  simp

theorem sumPToH_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (w : Fin 6 → V) (a : Fin 8 → V) :
    (sumCount 7 (pHOut (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) z w a))).toNat = edgeCount G C.P C.H := by
  rw [toNat_sumCount_of_le 7 3 _ (by omega)]
  · rw [← Fin.sum_univ_eq_sum_range]
    rw [edgeCount_eq_sum_fin G C.P C.H p]
    apply Finset.sum_congr rfl
    intro i hi
    exact pHOut_coreBits_toNat G C p z h w a i i.isLt
  · intro i hi
    rw [pHOut, toNat_count_eq_fin_sum 3 _ (by omega)]
    calc
      _ ≤ ∑ _j : Fin 3, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        split <;> omega
      _ = 3 := by simp

theorem sumPOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (h : Fin 3 → V) (w : Fin 6 → V) (a : Fin 8 → V) :
    (sumCount 7 (pOut (coreBits G.Adj (fun j ↦ (p j).1) h z w a))).toNat =
      edgeCount G C.P C.P := by
  rw [toNat_sumCount_of_le 7 7 _ (by omega)]
  · rw [← Fin.sum_univ_eq_sum_range]
    rw [edgeCount_eq_sum_fin G C.P C.P p]
    apply Finset.sum_congr rfl
    intro i hi
    exact pOut_coreBits_toNat G C p z h w a i i.isLt
  · intro i hi
    rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    calc
      _ ≤ ∑ _j : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        split <;> omega
      _ = 7 := by simp

theorem sumPDegree_coreBits_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (w : Fin 6 → V) (a : Fin 8 → V) :
    (sumCount 7 (pDegree (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (z j).1) w a))).toNat =
      ∑ u ∈ C.P, G.outdegree u := by
  rw [toNat_sumCount_of_le 7 15 _ (by omega)]
  · rw [← Fin.sum_univ_eq_sum_range]
    rw [sum_finset_eq_sum_fin C.P p G.outdegree]
    apply Finset.sum_congr rfl
    intro i hi
    exact pDegree_selected_toNat G C hG hPB hEpsilon p z w h a i i.isLt
  · intro i hi
    unfold pDegree
    rw [BitVec.toNat_add, BitVec.toNat_add]
    have hZLe : (pZOut (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) (fun j ↦ (z j).1) w a) i).toNat ≤ 5 := by
      rw [pZOut, toNat_count_eq_fin_sum 5 _ (by omega)]
      calc
        _ ≤ ∑ _j : Fin 5, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          split <;> omega
        _ = 5 := by simp
    have hHLe : (pHOut (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) (fun j ↦ (z j).1) w a) i).toNat ≤ 3 := by
      rw [pHOut, toNat_count_eq_fin_sum 3 _ (by omega)]
      calc
        _ ≤ ∑ _j : Fin 3, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          split <;> omega
        _ = 3 := by simp
    have hPLe : (pOut (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) (fun j ↦ (z j).1) w a) i).toNat ≤ 7 := by
      rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
      calc
        _ ≤ ∑ _j : Fin 7, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          split <;> omega
        _ = 7 := by simp
    simp only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem secondPCount_coreBits_toNat_le_PSecondCard
    (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    (secondPCount (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) z w a) source).toNat ≤
      (C.P.filter fun v ↦ v ∈
        G.secondOutNeighborFinset (p ⟨source, hs⟩).1).card := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1)
    (fun j ↦ (h j).1) z w a
  rw [secondPCount]
  apply count_le_filterCard C.P p _
    (fun v ↦ v ∈ G.secondOutNeighborFinset (p ⟨source, hs⟩).1)
    (by omega)
  intro j hBit
  exact secondPViaPOrH_selected_true_mem G C p z w h a
    source j hs j.isLt hBit

theorem fiveZExternalLower_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (h : Fin 3 → V) (w : Fin 6 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    (fiveZExternalLower (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a) source).toNat =
      if directCount G C.Z (p ⟨source, hs⟩).1 = 5 then 8
      else if directCount G C.Z (p ⟨source, hs⟩).1 = 4 then 6 else 5 := by
  have hPZ := pZOut_coreBits_toNat G C p z h w a source hs
  unfold fiveZExternalLower
  have hEqFive : pZOut (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a) source = 5 ↔
      directCount G C.Z (p ⟨source, hs⟩).1 = 5 := by
    constructor <;> intro hEq
    · have := congrArg BitVec.toNat hEq
      simpa [hPZ] using this
    · apply BitVec.eq_of_toNat_eq
      simp [hPZ, hEq]
  have hEqFour : pZOut (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a) source = 4 ↔
      directCount G C.Z (p ⟨source, hs⟩).1 = 4 := by
    constructor <;> intro hEq
    · have := congrArg BitVec.toNat hEq
      simpa [hPZ] using this
    · apply BitVec.eq_of_toNat_eq
      simp [hPZ, hEq]
  simp only [hEqFive, hEqFour]
  split
  · rfl
  · split <;> rfl

theorem pNonSeymourUnionEight_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hMissing : 35 - edgeCount G C.P C.Z ≤ 3)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (w : Fin 6 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 7) :
    pNonSeymourUnionEight
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w a) source = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w a
  let u := (p ⟨source, hs⟩).1
  let PS := C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset u
  have hPSecond := secondPCount_coreBits_toNat_le_PSecondCard G C p
    (fun j ↦ (z j).1) w h a source hs
  change (secondPCount bits source).toNat ≤ PS.card at hPSecond
  have hExternal := fiveZExternalLower_nat_le_second_add_H G C hG hMin
    hPB hEpsilon hPCard hZCard hMissing hFullUnion u (p ⟨source, hs⟩).2
  change PS.card +
      (if directCount G C.Z u = 5 then 8
        else if directCount G C.Z u = 4 then 6 else 5) ≤
    G.secondOutdegree u + directCount G C.H u at hExternal
  have hExternalDecode := fiveZExternalLower_coreBits_toNat G C p z
    (fun j ↦ (h j).1) w a source hs
  change (fiveZExternalLower bits source).toNat =
      (if directCount G C.Z u = 5 then 8
        else if directCount G C.Z u = 4 then 6 else 5) at hExternalDecode
  have hDegree := pDegree_selected_toNat G C hG hPB hEpsilon p z w h a
    source hs
  change (pDegree bits source).toNat = G.outdegree u at hDegree
  have hH := pHOut_coreBits_toNat G C p (fun j ↦ (z j).1) h w a
    source hs
  change (pHOut bits source).toNat = directCount G C.H u at hH
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    apply Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
    intro hu
    exact hNoSeymour ⟨u, hu⟩
  have hSecondLe : (secondPCount bits source).toNat ≤ 7 := by
    rw [secondPCount, toNat_count_eq_fin_sum 7 _ (by omega)]
    calc
      _ ≤ ∑ _j : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        split <;> omega
      _ = 7 := by simp
  have hExternalLe : (fiveZExternalLower bits source).toNat ≤ 8 := by
    rw [hExternalDecode]
    split
    · omega
    · split <;> omega
  have hDegreeLe : (pDegree bits source).toNat ≤ 15 := by
    rw [hDegree]
    have hCaptured := FiveZExactPBridge.P_outdegree_eq_Z_add_H_add_P
      G C hG hPB hEpsilon u (p ⟨source, hs⟩).2
    have hZLe : directCount G C.Z u ≤ 5 := by
      calc _ ≤ C.Z.card := Finset.card_le_card (Finset.filter_subset _ _)
           _ = 5 := hZCard
    have hHLe : directCount G C.H u ≤ 3 := by
      calc _ ≤ C.H.card := Finset.card_le_card (Finset.filter_subset _ _)
           _ = 3 := by simpa using (Fintype.card_congr h).symm
    have hPLe : directCount G C.P u ≤ 7 := by
      calc _ ≤ C.P.card := Finset.card_le_card (Finset.filter_subset _ _)
           _ = 7 := hPCard
    omega
  have hHLe : (pHOut bits source).toNat ≤ 3 := by
    rw [hH]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr h).symm)
  change (secondPCount bits source + fiveZExternalLower bits source).ult
    (pDegree bits source + pHOut bits source) = true
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [BitVec.toNat_add, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    hExternalDecode, hDegree, hH]
  omega

/-- Every graph in the aggregate five-`Z` branch produces a satisfying
assignment of the unsliced core. -/
theorem familyCoreUnionEight_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 2)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (hPZ : 32 ≤ edgeCount G C.P C.Z)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (w : Fin 6 → V) (a : Fin 8 → V) :
    familyCoreUnionEight
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w a) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w a
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr p).symm
  have hZCard : C.Z.card = 5 := by simpa using (Fintype.card_congr z).symm
  have hSquares := orientedSquare_coreBits_true G.Adj hG.1
    (fun u v huv ↦ hG.2 huv) (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a
  have hCross := orientedCross_coreBits_true G.Adj
    (fun u v huv ↦ hG.2 huv) (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a
  have hHTotalNat := totalHToP_coreBits_toNat G C p h
    (fun j ↦ (z j).1) w a
  have hHTotalLower : 11 ≤ edgeCount G C.H C.P := by
    have hCount := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    simpa only [hx, Nat.choose] using hCount
  have hHTotal : (11 : BitVec 8).ule (totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hHTotalNat]
    exact hHTotalLower
  have hMissingNat := totalMissingPZ_coreBits_toNat_add_edges G C p z
    (fun j ↦ (h j).1) w a
  change (totalMissingPZ bits).toNat + edgeCount G C.P C.Z = 35 at hMissingNat
  have hMissing : (totalMissingPZ bits).ule 3 = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    change (totalMissingPZ bits).toNat ≤ 3
    omega
  have hDegrees : all 7 (fun i =>
      (8 : BitVec 8).ule (pDegree bits i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [pDegree_selected_toNat G C hG hPB hEpsilon p z w h a i hi]
    exact hMin _
  have hRows : all 7 (pNonSeymourUnionEight bits) = true := by
    rw [all_eq_true_iff]
    intro i hi
    exact pNonSeymourUnionEight_coreBits_true G C hG hMin hNoSeymour
      hPB hEpsilon hPCard hZCard (by omega) hFullUnion p z h w a i hi
  simp only [familyCoreUnionEight, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hSquares.1, hCross.1⟩, hHTotal⟩, hMissing⟩,
    hDegrees⟩, hRows⟩

/-- The aggregate certificate rules out the five-`Z`, external-union-at-least
eight branch once the three exact label sets have been chosen. -/
theorem impossible_unionEight_of_exactCards (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 2)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (hPZ : 32 ≤ edgeCount G C.P C.Z)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card)
    (hPCard : C.P.card = 7) (hZCard : C.Z.card = 5)
    (hHCard : C.H.card = 3) : False := by
  classical
  let pRaw : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let p : Fin 7 ≃ {v : V // v ∈ C.P} :=
    CertificateLabels.sortedFinsetEquiv (compressedPKey G C) C.P pRaw
  let z : Fin 5 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let h : Fin 3 ≃ {v : V // v ∈ C.H} := finsetEquivFin C.H hHCard
  let w : Fin 6 → V := fun _ ↦ C.s
  let a : Fin 8 → V := fun _ ↦ C.s
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w a
  have hCore := familyCoreUnionEight_coreBits_true G C hG hMin hNoSeymour
    hRootDegree hk hx hPB hEpsilon hPZ hFullUnion p z h w a
  change familyCoreUnionEight bits = true at hCore
  let missing := 35 - edgeCount G C.P C.Z
  let alpha := 10 - edgeCount G C.P C.H
  let beta := 21 - edgeCount G C.P C.P
  have hHTotalLower : 11 ≤ edgeCount G C.H C.P := by
    have hCount := eight_add_choose_x_succ_le_H_to_P
      G C hG hMin hPB hRootDegree hk
    simpa only [hx, Nat.choose] using hCount
  have hPHUpper : edgeCount G C.P C.H ≤ 10 := by
    have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
    rw [hHCard, hPCard] at hCross
    omega
  have hPPUpper : edgeCount G C.P C.P ≤ 21 := by
    exact internal_edgeCount_le_twentyOne G C.P hG hPCard
  have hPZUpper : edgeCount G C.P C.Z ≤ 35 := by
    have hCap := edgeCount_le_card_mul_card G C.P C.Z
    rw [hPCard, hZCard] at hCap
    exact hCap
  have hDegreeLower : 56 ≤ ∑ u ∈ C.P, G.outdegree u := by
    calc
      56 = ∑ _u ∈ C.P, 8 := by simp [hPCard]
      _ ≤ ∑ u ∈ C.P, G.outdegree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hMin u
  have hDegreeAccounting :=
    degreeSum_eq_local_edgeCounts_of_p_eq_B G C hG hPB
  have hNoRoot : ∑ u ∈ C.P, epsilonAt G u C.s = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [epsilonAt, FiveZExactPBridge.no_P_to_s_of_epsilonS_zero
      G C hEpsilon u hu]
  have hMissingLe : missing ≤ 3 := by
    dsimp [missing]
    omega
  have hMissingAdd : missing + edgeCount G C.P C.Z = 35 := by
    dsimp [missing]
    omega
  have hAlphaAdd : edgeCount G C.P C.H + alpha = 10 := by
    dsimp [alpha]
    omega
  have hBetaAdd : edgeCount G C.P C.P + beta = 21 := by
    dsimp [beta]
    omega
  have hDegreeSumNat : ∑ u ∈ C.P, G.outdegree u =
      66 - missing - alpha - beta := by
    rw [hNoRoot] at hDegreeAccounting
    omega
  have hMissingNat := totalMissingPZ_coreBits_toNat_add_edges G C p z
    (fun j ↦ (h j).1) w a
  change (totalMissingPZ bits).toNat + edgeCount G C.P C.Z = 35 at hMissingNat
  have hMissingEq : totalMissingPZ bits = BitVec.ofNat 8 missing := by
    apply BitVec.eq_of_toNat_eq
    simp [missing]
    omega
  have hPHDecode := sumPToH_coreBits_toNat G C p
    (fun j ↦ (z j).1) h w a
  change (sumCount 7 (pHOut bits)).toNat = edgeCount G C.P C.H at hPHDecode
  have hPPDecode := sumPOut_coreBits_toNat G C p
    (fun j ↦ (z j).1) (fun j ↦ (h j).1) w a
  change (sumCount 7 (pOut bits)).toNat = edgeCount G C.P C.P at hPPDecode
  have hAlphaSmall : alpha ≤ 6 := by
    by_contra hAlpha
    have hAlphaLarge : 7 ≤ alpha := by omega
    let D := C.P.filter fun u ↦ G.outdegree u = 8
    let S := D.filter fun u ↦ directCount G C.Z u = 5
    have hSP : S ⊆ C.P :=
      (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hExcessRewrite : (∑ u ∈ C.P, G.outdegree u) =
        56 + ∑ u ∈ C.P, (G.outdegree u - 8) := by
      calc
        _ = ∑ u ∈ C.P, (8 + (G.outdegree u - 8)) := by
          apply Finset.sum_congr rfl
          intro u hu
          have := hMin u
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hPCard]
    have hExcess : ∑ u ∈ C.P, (G.outdegree u - 8) =
        10 - missing - alpha - beta := by
      rw [hDegreeSumNat] at hExcessRewrite
      omega
    have hDCard := card_le_exact_degree_add_excess
      (V := V) C.P G.outdegree 8 (fun u _hu ↦ hMin u)
    change C.P.card ≤ D.card + ∑ u ∈ C.P, (G.outdegree u - 8) at hDCard
    have hNonfull := card_nonfull_rows_le_capacity_defect G C.P C.Z
    rw [hPCard, hZCard] at hNonfull
    have hNonfullCard :
        (C.P.filter fun u ↦ directCount G C.Z u ≠ 5).card ≤ missing := by
      omega
    have hSPartition : S.card +
        (D.filter fun u ↦ directCount G C.Z u ≠ 5).card = D.card := by
      simpa [S] using
        D.card_filter_add_card_filter_not (fun u ↦ directCount G C.Z u = 5)
    have hBadSubset : D.filter (fun u ↦ directCount G C.Z u ≠ 5) ⊆
        C.P.filter (fun u ↦ directCount G C.Z u ≠ 5) := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huD, huBad⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp huD).1, huBad⟩
    have hBadCard := Finset.card_le_card hBadSubset
    have hSCard : alpha + beta - 3 ≤ S.card := by
      rw [hPCard, hExcess] at hDCard
      omega
    have hSNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    have hMissingP := card_internalMissingPairs_add_edgeCount G C.P hG
    have hChoose : Nat.choose 7 2 = 21 := by decide
    rw [hPCard, hChoose] at hMissingP
    have hMissingMono := Finset.card_le_card
      (internalMissingPairs_mono G hSP)
    have hMissingS : (internalMissingPairs G S).card ≤ beta := by omega
    obtain ⟨u, huS, hKing⟩ := exists_noRootStatus_king_bound
      G C.P S (fun _ ↦ 5) (directCount G C.H) 8
      hSNonempty hSP hG
      (by
        intro q hqS
        have hqD := (Finset.mem_filter.mp hqS).1
        have hqExact := (Finset.mem_filter.mp hqD).2
        have hqP := hSP hqS
        have hqZ := (Finset.mem_filter.mp hqS).2
        have hDegreeQ := FiveZExactPBridge.P_outdegree_eq_Z_add_H_add_P
          G C hG hPB hEpsilon q hqP
        omega)
      (by
        intro q hqS
        have hqP := hSP hqS
        have hqD := (Finset.mem_filter.mp hqS).1
        have hqExact := (Finset.mem_filter.mp hqD).2
        have hqZ := (Finset.mem_filter.mp hqS).2
        let PS := C.P.filter fun v ↦ v ∈ G.secondOutNeighborFinset q
        have hInternalSecondLe :
            (internalSecondNeighbors (G := G) S q).card ≤ PS.card := by
          apply Finset.card_le_card
          intro v hv
          rcases Finset.mem_filter.mp hv with
            ⟨hvS, hNotAdj, hvq, w', hwS, hqw, hwv⟩
          apply Finset.mem_filter.mpr
          refine ⟨hSP hvS, ?_⟩
          rw [Digraph.mem_secondOutNeighborFinset,
            Digraph.mem_secondOutNeighborSet]
          exact ⟨⟨w', hqw, hwv⟩, hNotAdj, hvq⟩
        have hExternalQ := fiveZExternalLower_nat_le_second_add_H
          G C hG hMin hPB hEpsilon hPCard hZCard hMissingLe
          hFullUnion q hqP
        change PS.card +
            (if directCount G C.Z q = 5 then 8
              else if directCount G C.Z q = 4 then 6 else 5) ≤
          G.secondOutdegree q + directCount G C.H q at hExternalQ
        simp only [hqZ, if_pos] at hExternalQ
        have hStrict : G.secondOutdegree q < G.outdegree q := by
          apply Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
          intro hqSeymour
          exact hNoSeymour ⟨q, hqSeymour⟩
        omega)
    omega
  have allMissing_impossible : False := by
    let missingBits : Nat → BitVec 2 := fun i =>
      BitVec.ofNat 2 (5 - (pZOut bits i).toNat)
    have hRows : all 7 (fun i =>
        HighMissingCompressed.rowMissing missingBits i ==
          (5 - pZOut bits i)) = true := by
      rw [all_eq_true_iff]
      intro i hi
      simp only [beq_iff_eq]
      have hOldNat := pZOut_coreBits_toNat G C p z (fun j ↦ (h j).1) w a i hi
      have hDirectLe : directCount G C.Z (p ⟨i, hi⟩).1 ≤ 5 := by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      have hRowLe := directZ_row_missing_le_total G C hPCard hZCard
        (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2
      change 5 - directCount G C.Z (p ⟨i, hi⟩).1 ≤ missing at hRowLe
      have hOldLeBV : pZOut bits i ≤ (5 : BitVec 8) := by
        rw [BitVec.le_def]
        rw [hOldNat]
        exact hDirectLe
      apply BitVec.eq_of_toNat_eq
      have hFive : (5 : BitVec 8).toNat = 5 := by decide
      rw [HighMissingCompressed.rowMissing,
        BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (by
        have := (missingBits i).isLt
        omega)]
      simp only [missingBits, BitVec.toNat_ofNat, Nat.reducePow]
      have hDefectLt : 5 - directCount G C.Z (p ⟨i, hi⟩).1 < 4 := by omega
      have hDefectLtOld : 5 - (pZOut bits i).toNat < 4 := by
        rw [hOldNat]
        exact hDefectLt
      rw [Nat.mod_eq_of_lt hDefectLtOld,
        BitVec.toNat_sub_of_le hOldLeBV,
        hOldNat, hFive]
    have hMissingTotal := HighMissingCompressed.totalMissingPZ_eq_of_rows
      bits missingBits hRows
    have hNewMissingLe :
        (HighMissingCompressed.totalMissingPZ missingBits).ule 3 = true := by
      rw [hMissingTotal]
      have hExpanded := hCore
      simp only [familyCoreUnionEight, Bool.and_eq_true] at hExpanded
      exact hExpanded.1.1.2
    have hProjectPH := HighMissingCompressed.totalPToH_projectRaw bits
    have hProjectHP := HighMissingCompressed.totalHToP_projectRaw bits
    have hProjectPP := HighMissingCompressed.totalPOut_projectRaw bits
    have hPHLower : (4 : BitVec 8).ule
        (HighMissingCompressed.totalPToH
          (HighMissingCompressed.projectRaw bits)) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      have hFour : (4 : BitVec 8).toNat = 4 := by decide
      rw [hProjectPH, hPHDecode]
      rw [hFour]
      omega
    have hHPDecode := totalHToP_coreBits_toNat G C p h
      (fun j ↦ (z j).1) w a
    have hCross := cross_edgeCount_add_reverse_le G C.H C.P hG
    rw [hHCard, hPCard] at hCross
    have hPHCapacity :
        (HighMissingCompressed.totalHToP
            (HighMissingCompressed.projectRaw bits) +
          HighMissingCompressed.totalPToH
            (HighMissingCompressed.projectRaw bits)).ule 21 = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add]
      have hTwentyOne : (21 : BitVec 8).toNat = 21 := by decide
      rw [hProjectHP, hProjectPH, hHPDecode, hPHDecode,
        Nat.mod_eq_of_lt (by omega), hTwentyOne]
      exact hCross
    have hDegreeCut :
        (21 + HighMissingCompressed.totalMissingPZ missingBits).ule
          (HighMissingCompressed.totalPOut
              (HighMissingCompressed.projectRaw bits) +
            HighMissingCompressed.totalPToH
              (HighMissingCompressed.projectRaw bits)) = true := by
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq,
        BitVec.toNat_add]
      have hTwentyOne : (21 : BitVec 8).toNat = 21 := by decide
      rw [hMissingTotal, hMissingEq, hProjectPP, hProjectPH,
        hPPDecode, hPHDecode]
      simp only [BitVec.toNat_ofNat, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), hTwentyOne]
      omega
    have hRowMissingNat (i : Nat) (hi : i < 7) :
        (HighMissingCompressed.rowMissing missingBits i).toNat =
          5 - directCount G C.Z (p ⟨i, hi⟩).1 := by
      have hOldNat := pZOut_coreBits_toNat G C p z (fun j ↦ (h j).1) w a i hi
      have hDirectLe : directCount G C.Z (p ⟨i, hi⟩).1 ≤ 5 := by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
      have hRowLe := directZ_row_missing_le_total G C hPCard hZCard
        (p ⟨i, hi⟩).1 (p ⟨i, hi⟩).2
      change 5 - directCount G C.Z (p ⟨i, hi⟩).1 ≤ missing at hRowLe
      rw [HighMissingCompressed.rowMissing,
        BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (by
        have := (missingBits i).isLt
        omega)]
      dsimp [missingBits]
      rw [hOldNat]
      simp only [BitVec.toNat_ofNat, Nat.reducePow]
      have hDefectLt : 5 - directCount G C.Z (p ⟨i, hi⟩).1 < 4 := by omega
      rw [Nat.mod_eq_of_lt hDefectLt]
    have hRowKeyNat (i : Nat) (hi : i < 7) :
        (HighMissingCompressed.pRowKey
          (HighMissingCompressed.projectRaw bits) missingBits i).toNat =
            compressedPKey G C (p ⟨i, hi⟩).1 := by
      rw [HighMissingCompressed.pRowKey]
      simp only [BitVec.toNat_add, BitVec.toNat_mul]
      norm_num [BitVec.toNat_ofNat]
      rw [HighMissingCompressed.pHOut_projectRaw bits i hi,
        HighMissingCompressed.pOut_projectRaw bits i hi,
        pHOut_coreBits_toNat G C p (fun j ↦ (z j).1) h w a i hi,
        pOut_coreBits_toNat G C p (fun j ↦ (z j).1)
          (fun j ↦ (h j).1) w a i hi,
        hRowMissingNat i hi]
      unfold compressedPKey
      have hHLe : directCount G C.H (p ⟨i, hi⟩).1 ≤ 3 := by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
      have hPLe : directCount G C.P (p ⟨i, hi⟩).1 ≤ 7 := by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
      have h32 : (32 : BitVec 8).toNat = 32 := by decide
      have h8 : (8 : BitVec 8).toNat = 8 := by decide
      rw [h32, h8]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hOrdered : HighMissingCompressed.orderedP
        (HighMissingCompressed.projectRaw bits) missingBits = true := by
      rw [HighMissingCompressed.orderedP, all_eq_true_iff]
      intro i hi
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [hRowKeyNat (i + 1) (by omega), hRowKeyNat i (by omega)]
      have hSort := CertificateLabels.sorted_key_anti
        (compressedPKey G C) C.P (finsetEquivFin C.P hPCard)
          (i := (⟨i, by omega⟩ : Fin 7))
          (j := (⟨i + 1, by omega⟩ : Fin 7))
          (show i ≤ i + 1 from Nat.le_succ i)
      simpa [p, pRaw] using hSort
    have hProjected := HighMissingCompressed.allMissingCore_of_projection
      bits missingBits hCore hRows hNewMissingLe hOrdered hPHCapacity
        hDegreeCut hPHLower
    rw [HighMissingCompressed.allMissingCore_unsat
      (HighMissingCompressed.projectRaw bits) missingBits] at hProjected
    contradiction
  exact allMissing_impossible

/-- Graph-level form of the aggregate union-at-least-eight contradiction. -/
theorem impossible_exactFiveZ_unionAtLeastEight (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hBCard : C.B.card = 7)
    (hk : C.k = 1) (hx : C.x = 2) (hz : C.z = 5)
    (hEpsilon : epsilonS G C = 0)
    (hPZ : 32 ≤ edgeCount G C.P C.Z)
    (hFullUnion : 8 ≤ (zExternalUnion G C).card) : False := by
  have hPB := SeymourEight.BSevenKOne.p_eq_B G C hG hMin hBCard hk
  have hPCard : C.P.card = 7 := by rw [hPB]; exact hBCard
  have hZCard : C.Z.card = 5 := by
    change C.Z.card = 5 at hz
    exact hz
  have hHCard : C.H.card = 3 := by
    change C.h = 3
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  exact impossible_unionEight_of_exactCards G C hG hMin hNoSeymour
    hRootDegree hk hx hPB hEpsilon hPZ hFullUnion hPCard hZCard hHCard

end SeymourEight.FiveZUnionEightBridge
