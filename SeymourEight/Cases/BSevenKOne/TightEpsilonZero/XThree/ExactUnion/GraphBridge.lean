import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.CoreBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactPBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactHBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactGlobalBridge
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.UnionAtLeastEight.CoreBridge

set_option linter.style.header false

/-!
# Graph bridge for the exact-seven four-`Z` core

This first layer verifies the decoder and all retained first-neighborhood
degree equations.  Second-neighborhood soundness is kept in a separate layer.
-/

namespace SeymourEight.FourZExactSevenGraphBridge

open FourZExactSeven FourZExactSevenBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZExactPBridge FiveZExactGlobalBridge
  FiveZExactHBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

abbrev zExternalUnion (C : G.LocalConfiguration) : Finset V :=
  FiveZExactGraphBridge.zExternalUnion G C

theorem pOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) (i : Nat) (hi : i < 7) :
    (FourZExactSeven.pOut (coreBits G.Adj (fun j ↦ (p j).1) h a z w) i).toNat =
      directCount G C.P (p ⟨i, hi⟩).1 := by
  rw [FourZExactSeven.pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) h a z w i j hi j.isLt]
  simp

theorem pHOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) (i : Nat) (hi : i < 7) :
    (FourZExactSeven.pHOut (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w) i).toNat =
      directCount G C.H (p ⟨i, hi⟩).1 := by
  rw [FourZExactSeven.pHOut, toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.H h
  intro j
  rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    a z w i j hi j.isLt]
  simp

theorem hPOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) (i : Nat) (hi : i < 4) :
    (FourZExactSeven.hPOut (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w) i).toNat =
      directCount G C.P (h ⟨i, hi⟩).1 := by
  rw [FourZExactSeven.hPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    a z w i j hi j.isLt]
  simp

omit [DecidableEq V] in
theorem aOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 4 → V)
    (a : Fin 8 ≃ {v : V // v ∈ C.A}) (z : Fin 4 → V) (w : Fin 7 → V)
    (i : Nat) (hi : i < 8) :
    (FourZExactSeven.aOut (coreBits G.Adj p h (fun j ↦ (a j).1) z w) i).toNat =
      directCount G C.A (a ⟨i, hi⟩).1 := by
  classical
  rw [FourZExactSeven.aOut, toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A a
  intro j
  rw [aArc_coreBits G.Adj p h (fun j ↦ (a j).1) z w i j hi j.isLt]
  simp

theorem zArcOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (w : Fin 7 → V)
    (i : Nat) (hi : i < 4) :
    (count 4 (zArc (coreBits G.Adj p h a (fun j ↦ (z j).1) w) i)).toNat =
      directCount G C.Z (z ⟨i, hi⟩).1 := by
  rw [toNat_count_eq_fin_sum 4 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.Z z
  intro j
  rw [zArc_coreBits G.Adj p h a (fun j ↦ (z j).1) w i j hi j.isLt]
  simp

theorem zWOut_toNat (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ zExternalUnion G C})
    (i : Nat) (hi : i < 4) :
    (count 7 (zToW (coreBits G.Adj p h a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) i)).toNat =
      directCount G (zExternalUnion G C) (z ⟨i, hi⟩).1 := by
  rw [toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G (zExternalUnion G C) w
  intro j
  rw [zToW_coreBits G.Adj p h a (fun j ↦ (z j).1) (fun j ↦ (w j).1)
    i j hi j.isLt]
  simp

theorem totalPToH_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) :
    (FourZExactSeven.totalPToH (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w)).toNat =
      edgeCount G C.P C.H := by
  rw [FourZExactSeven.totalPToH, toNat_count_eq_fin_sum 28 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.P C.H p]
  simp_rw [directCount_eq_sum_fin G C.H h]
  simp only [Fin.sum_univ_succ]
  simp [pToH_coreBits, Nat.add_assoc]

theorem totalHToP_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V) :
    (FourZExactSeven.totalHToP (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w)).toNat =
      edgeCount G C.H C.P := by
  rw [FourZExactSeven.totalHToP, toNat_count_eq_fin_sum 28 _ (by omega)]
  rw [edgeCount_eq_sum_fin G C.H C.P h]
  simp_rw [directCount_eq_sum_fin G C.P p]
  simp only [Fin.sum_univ_succ]
  simp [hToP_coreBits, Nat.add_assoc]

/-- Exact graph degree of a labelled `P` vertex. -/
theorem pDegree_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V)
    (hPZ : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (i : Nat) (hi : i < 7) :
    (FourZExactSeven.pDegree missing (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) a z w) i).toNat = G.outdegree (p ⟨i, hi⟩).1 := by
  have hH := pHOut_toNat G C p h a z w i hi
  have hP := pOut_toNat G C p (fun j ↦ (h j).1) a z w i hi
  have hHLe : directCount G C.H (p ⟨i, hi⟩).1 ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr h).symm)
  have hPLe : directCount G C.P (p ⟨i, hi⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon _ (p ⟨i, hi⟩).2]
  by_cases hex : missing = 1 ∧ i = 0
  · have hm : missing = 1 := hex.1
    have hi0 : i = 0 := hex.2
    subst missing
    subst i
    rw [FourZExactSeven.pDegree]
    simp only [decide_true, Bool.true_and, ↓reduceIte]
    rw [BitVec.toNat_add, BitVec.toNat_add, hH, hP]
    have hThree : (3 : BitVec 8).toNat = 3 := by decide
    rw [hThree, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hPZ 0 hi]
    simp
  · have hBool : ¬(missing = 1 && i = 0) := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hex
    rw [FourZExactSeven.pDegree, if_neg hBool,
      BitVec.toNat_add, BitVec.toNat_add, hH, hP]
    have hFour : (4 : BitVec 8).toNat = 4 := by decide
    rw [hFour, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hZ := hPZ i hi
    rw [if_neg hex] at hZ
    omega

/-- Exact graph degree of a labelled `H` vertex. -/
theorem hDegree_toNat (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPB : C.P = C.B) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 ≃ {v : V // v ∈ C.A}) (z : Fin 4 → V) (w : Fin 7 → V)
    (hAH : ∀ j : Fin 4, (a ⟨j + 1, by omega⟩).1 = (h j).1)
    (i : Nat) (hi : i < 4) :
    (FourZExactSeven.hDegree (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (a j).1) z w) i).toNat = G.outdegree (h ⟨i, hi⟩).1 := by
  have hA := aOut_toNat G C (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    a z w (i + 1) (by omega)
  have hP := hPOut_toNat G C p h (fun j ↦ (a j).1) z w i hi
  have hALe : directCount G C.A (a ⟨i + 1, by omega⟩).1 ≤ 8 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr a).symm)
  have hPLe : directCount G C.P (h ⟨i, hi⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  rw [FourZExactSeven.hDegree, BitVec.toNat_add, hA, hP, Nat.mod_eq_of_lt (by omega)]
  have hEq := H_outdegree_eq_A_add_P G C hG hPB
    (h ⟨i, hi⟩).1 (h ⟨i, hi⟩).2
  rw [hAH ⟨i, hi⟩] at hA
  have hDirectEq : directCount G C.A (a ⟨i + 1, by omega⟩).1 =
      directCount G C.A (h ⟨i, hi⟩).1 := by rw [hAH ⟨i, hi⟩]
  rw [hDirectEq]
  exact hEq.symm

/-- The certificate's lexicographic `P` symmetry break follows from a graph
ordering by outdegree and then by the number of direct `H` arcs. -/
theorem orderedP_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 → V) (w : Fin 7 → V)
    (hRows : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hSorted : ∀ (q : Nat)
      (hq : q < 6 - (if missing = 1 then 1 else 0)),
      let i := q + (if missing = 1 then 1 else 0)
      G.outdegree (p ⟨i + 1, by omega⟩).1 ≤
          G.outdegree (p ⟨i, by omega⟩).1 ∧
        (G.outdegree (p ⟨i, by omega⟩).1 =
            G.outdegree (p ⟨i + 1, by omega⟩).1 →
          directCount G C.H (p ⟨i + 1, by omega⟩).1 ≤
            directCount G C.H (p ⟨i, by omega⟩).1)) :
    FourZExactSeven.orderedP missing
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
  rw [FourZExactSeven.orderedP, all_eq_true_iff]
  intro q hq
  let first := if missing = 1 then 1 else 0
  let i := q + first
  have hs := hSorted q hq
  dsimp only at hs
  have hi : i < 7 := by
    by_cases hm : missing = 1 <;> simp [i, first, hm] at hq ⊢ <;> omega
  have hi1 : i + 1 < 7 := by
    by_cases hm : missing = 1 <;> simp [i, first, hm] at hq ⊢ <;> omega
  have hs' : G.outdegree (p ⟨i + 1, hi1⟩).1 ≤
        G.outdegree (p ⟨i, hi⟩).1 ∧
      (G.outdegree (p ⟨i, hi⟩).1 = G.outdegree (p ⟨i + 1, hi1⟩).1 →
        directCount G C.H (p ⟨i + 1, hi1⟩).1 ≤
          directCount G C.H (p ⟨i, hi⟩).1) := by
    simpa only [i, first] using hs
  have hd0 := pDegree_toNat G C hG hPB hEpsilon missing p h a z w hRows i hi
  have hd1 := pDegree_toNat G C hG hPB hEpsilon missing p h a z w hRows
    (i + 1) hi1
  have hh0 := pHOut_toNat G C p h a z w i hi
  have hh1 := pHOut_toNat G C p h a z w (i + 1) hi1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    BitVec.ule_eq_decide, decide_eq_true_eq]
  change (FourZExactSeven.pDegree missing bits (i + 1)).toNat ≤
      (FourZExactSeven.pDegree missing bits i).toNat ∧
    ((FourZExactSeven.pDegree missing bits i ==
        FourZExactSeven.pDegree missing bits (i + 1)) = false ∨
      (FourZExactSeven.pHOut bits (i + 1)).toNat ≤
        (FourZExactSeven.pHOut bits i).toNat)
  refine ⟨by rw [hd1, hd0]; exact hs'.1, ?_⟩
  by_cases heq : FourZExactSeven.pDegree missing bits i =
      FourZExactSeven.pDegree missing bits (i + 1)
  · right
    have hdeg : G.outdegree (p ⟨i, hi⟩).1 =
        G.outdegree (p ⟨i + 1, hi1⟩).1 := by
      rw [← hd0, ← hd1, heq]
    rw [hh1, hh0]
    exact hs'.2 hdeg
  · left
    simp [heq]

end SeymourEight.FourZExactSevenGraphBridge
