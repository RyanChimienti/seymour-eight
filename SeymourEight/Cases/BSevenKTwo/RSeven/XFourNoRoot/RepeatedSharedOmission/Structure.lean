import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.BooleanBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge

open Shared RepeatedSharedOmissionCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem aOut_toNat (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (source : Nat) (hs : source < 8) :
    (ThetaFourCore.aOut
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source).toNat =
      directCount G C.A (L.a ⟨source, hs⟩).1 := by
  rw [ThetaFourCore.aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A L.a _
  intro j
  rw [aArc_coreBits G.Adj _ _ _ source j hs j.isLt]
  simp

theorem aPOut_toNat (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (source : Nat) (hs : source < 8) :
    (ThetaFourCore.aPOut
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) source).toNat =
      directCount G C.P (L.a ⟨source, hs⟩).1 := by
  rw [ThetaFourCore.aPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P L.p _
  intro j
  have hA0P : ∀ i : Fin 7, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  unfold ThetaFourCore.aToP
  by_cases hs0 : source = 0
  · subst source
    simp [hA0P]
  by_cases hs7 : source < 7
  · have hsh : source - 1 < 6 := by omega
    rw [if_neg hs0, if_pos hs7, ThetaFourCore.hToP,
      pToH_coreBits G.Adj _ _ _ j (source - 1) j.isLt hsh]
    have hiEq : (⟨source - 1 + 1, by omega⟩ : Fin 8) = ⟨source, hs⟩ :=
      Fin.ext (by simp; omega)
    have haeq : (L.a ⟨source - 1 + 1, by omega⟩).1 =
        (L.a ⟨source, hs⟩).1 := by rw [hiEq]
    rw [haeq]
    rcases T.ph_complete j ⟨source - 1, hsh⟩ with hp | ha
    · rw [haeq] at hp
      simp [hp, hG.2 hp]
    · rw [haeq] at ha
      simp [ha, hG.2 ha]
  · have hsEq : source = 7 := by omega
    subst source
    rw [if_neg (by omega : ¬7 = 0), if_neg (by omega : ¬7 < 7),
      rToP_coreBits G.Adj _ _ _ j j.isLt]
    simp

theorem pBlockCounts (C : G.LocalConfiguration)
    (L : Profile21111Labels G C) (T : TightCounts G C L)
    (hG : G.IsOriented) (hHCard : C.H.card = 6)
    (p : Nat) (hp : p < 7) :
    (ThetaFourCore.pOut
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) p).toNat = directCount G C.P (L.p ⟨p, hp⟩).1 ∧
    (ThetaFourCore.pHOut
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) p).toNat = directCount G C.H (L.p ⟨p, hp⟩).1 ∧
    (ThetaFourCore.pZOut
      (coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
        (fun i ↦ (L.z i).1)) p).toNat = directCount G C.Z (L.p ⟨p, hp⟩).1 := by
  let bits := coreBits G.Adj (fun i ↦ (L.p i).1) (fun i ↦ (L.a i).1)
    (fun i ↦ (L.z i).1)
  have hP : (ThetaFourCore.pOut bits p).toNat =
      directCount G C.P (L.p ⟨p, hp⟩).1 := by
    rw [ThetaFourCore.pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P L.p _
    intro j
    rw [pArc_coreBits G.Adj _ _ _ (fun i => hG.1 _)
      T.p_complete (by intro i j hij; exact hG.2 hij) p j hp j.isLt]
    simp
  have hH : (ThetaFourCore.pHOut bits p).toNat =
      directCount G C.H (L.p ⟨p, hp⟩).1 := by
    rw [ThetaFourCore.pHOut, toNat_count_eq_fin_sum 6 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H (hLabelEquiv G C L hHCard) _
    intro j
    rw [pToH_coreBits G.Adj _ _ _ p j hp j.isLt]
    simp
  have hZ : (ThetaFourCore.pZOut bits p).toNat =
      directCount G C.Z (L.p ⟨p, hp⟩).1 := by
    rw [ThetaFourCore.pZOut, toNat_count_eq_fin_sum 4 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Z L.z _
    intro j
    rw [pToZ_coreBits G.Adj _ _ _ p j hp j.isLt]
    simp
  exact ⟨hP, hH, hZ⟩

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
