import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.HighDefect.CoreBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactLabels

set_option linter.style.header false
set_option maxRecDepth 10000

/-!
# Graph encoding for the projected high-defect core

The segmented certificate layout is exposed through one unified twenty-vertex
decoder.  Later soundness proofs can reason about `coreArc` without revisiting
the six physical bit ranges.
-/

namespace SeymourEight.FiveZHighDefectGraphBridge

open FiveZHighDefect FiveZHighDefectBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def labelledVertex (a : Fin 8 → V) (p : Fin 7 → V) (z : Fin 5 → V)
    (i : Nat) : V :=
  if hiA : i < 8 then a ⟨i, hiA⟩
  else if hiP : i < 15 then p ⟨i - 8, by omega⟩
  else if hiZ : i < 20 then z ⟨i - 15, by omega⟩
  else z 0

omit [Fintype V] [DecidableEq V] in
theorem coreArc_coreBits
    (p : Fin 7 → V) (h : Fin 3 → V) (r : Fin 4 → V)
    (z : Fin 5 → V) (a : Fin 8 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0) (p i))
    (hP0 : ∀ i : Fin 7, ¬G.Adj (p i) (a 0))
    (hAH : ∀ i : Fin 3, a ⟨i + 1, by omega⟩ = h i)
    (hAR : ∀ i : Fin 4, a ⟨i + 4, by omega⟩ = r i)
    (hPR : ∀ i : Fin 7, ∀ j : Fin 4, ¬G.Adj (p i) (r j))
    (hAZ : ∀ i : Fin 8, ∀ j : Fin 5, ¬G.Adj (a i) (z j))
    (u v : Nat) (hu : u < 15) (hv : v < 20) :
    coreArc (coreBits G.Adj p h r z a) u v =
      decide (G.Adj (labelledVertex a p z u) (labelledVertex a p z v)) := by
  classical
  let bits := coreBits G.Adj p h r z a
  have hA1 : a (1 : Fin 8) = h 0 := by simpa using hAH 0
  have hA2 : a (2 : Fin 8) = h 1 := by simpa using hAH 1
  have hA3 : a (3 : Fin 8) = h 2 := by simpa using hAH 2
  have hA4 : a (4 : Fin 8) = r 0 := by simpa using hAR 0
  have hA5 : a (5 : Fin 8) = r 1 := by simpa using hAR 1
  have hA6 : a (6 : Fin 8) = r 2 := by simpa using hAR 2
  have hA7 : a (7 : Fin 8) = r 3 := by simpa using hAR 3
  have hA1' (ph : 0 < 3) (pa : 1 < 8) : h ⟨0, ph⟩ = a ⟨1, pa⟩ := by
    simpa using hA1.symm
  have hA2' (ph : 1 < 3) (pa : 2 < 8) : h ⟨1, ph⟩ = a ⟨2, pa⟩ := by
    simpa using hA2.symm
  have hA3' (ph : 2 < 3) (pa : 3 < 8) : h ⟨2, ph⟩ = a ⟨3, pa⟩ := by
    simpa using hA3.symm
  have hA4' (pr : 0 < 4) (pa : 4 < 8) : r ⟨0, pr⟩ = a ⟨4, pa⟩ := by
    simpa using hA4.symm
  have hA5' (pr : 1 < 4) (pa : 5 < 8) : r ⟨1, pr⟩ = a ⟨5, pa⟩ := by
    simpa using hA5.symm
  have hA6' (pr : 2 < 4) (pa : 6 < 8) : r ⟨2, pr⟩ = a ⟨6, pa⟩ := by
    simpa using hA6.symm
  have hA7' (pr : 3 < 4) (pa : 7 < 8) : r ⟨3, pr⟩ = a ⟨7, pa⟩ := by
    simpa using hA7.symm
  by_cases huA : u < 8
  · rw [coreArc, if_pos huA]
    have hSource : labelledVertex a p z u = a ⟨u, huA⟩ := by
      simp [labelledVertex, huA]
    rw [hSource]
    by_cases hvA : v < 8
    · rw [if_pos hvA, aArc_coreBits G.Adj p h r z a u v huA hvA]
      simp [labelledVertex, hvA]
    by_cases hvP : v < 15
    · rw [if_neg hvA, if_pos hvP]
      have hvP' : v - 8 < 7 := by omega
      have hTarget : labelledVertex a p z v = p ⟨v - 8, hvP'⟩ := by
        simp [labelledVertex, hvA, hvP]
      rw [hTarget]
      have huCases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨
          u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 := by omega
      rcases huCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [aToP] using hA0P ⟨v - 8, hvP'⟩
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hToP_coreBits G.Adj p h r z a 0 (v - 8) (by omega) hvP',
          hA1' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hToP_coreBits G.Adj p h r z a 1 (v - 8) (by omega) hvP',
          hA2' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_pos (by omega),
          hToP_coreBits G.Adj p h r z a 2 (v - 8) (by omega) hvP',
          hA3' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rToP_coreBits G.Adj p h r z a 0 (v - 8) (by omega) hvP',
          hA4' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rToP_coreBits G.Adj p h r z a 1 (v - 8) (by omega) hvP',
          hA5' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rToP_coreBits G.Adj p h r z a 2 (v - 8) (by omega) hvP',
          hA6' (by omega) (by omega)]
      · rw [aToP, if_neg (by omega), if_neg (by omega),
          rToP_coreBits G.Adj p h r z a 3 (v - 8) (by omega) hvP',
          hA7' (by omega) (by omega)]
    · rw [if_neg hvA, if_neg hvP]
      have hvZ : v - 15 < 5 := by omega
      have hTarget : labelledVertex a p z v = z ⟨v - 15, hvZ⟩ := by
        simp [labelledVertex, hvA, hvP, hv]
      rw [hTarget]
      simp [hAZ]
  · rw [coreArc, if_neg huA, if_pos hu]
    have huP : u - 8 < 7 := by omega
    have hSource : labelledVertex a p z u = p ⟨u - 8, huP⟩ := by
      simp [labelledVertex, huA, hu]
    rw [hSource]
    by_cases hvA : v < 8
    · rw [if_pos hvA]
      have hvCases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨
          v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by omega
      rcases hvCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [pToA, labelledVertex, huA, hu] using hP0 ⟨u - 8, huP⟩
      · rw [pToA, pToH_coreBits G.Adj p h r z a (u - 8) 0 huP (by omega),
          hA1' (by omega) (by omega)]
        simp [labelledVertex]
      · rw [pToA, pToH_coreBits G.Adj p h r z a (u - 8) 1 huP (by omega),
          hA2' (by omega) (by omega)]
        simp [labelledVertex]
      · rw [pToA, pToH_coreBits G.Adj p h r z a (u - 8) 2 huP (by omega),
          hA3' (by omega) (by omega)]
        simp [labelledVertex]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (4 : Fin 8)) := by
          rw [hA4]
          exact hPR ⟨u - 8, huP⟩ 0
        simp [pToA, labelledVertex, hnot]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (5 : Fin 8)) := by
          rw [hA5]
          exact hPR ⟨u - 8, huP⟩ 1
        simp [pToA, labelledVertex, hnot]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (6 : Fin 8)) := by
          rw [hA6]
          exact hPR ⟨u - 8, huP⟩ 2
        simp [pToA, labelledVertex, hnot]
      · have hnot : ¬G.Adj (p ⟨u - 8, huP⟩) (a (7 : Fin 8)) := by
          rw [hA7]
          exact hPR ⟨u - 8, huP⟩ 3
        simp [pToA, labelledVertex, hnot]
    by_cases hvP : v < 15
    · rw [if_neg hvA, if_pos hvP,
        pArc_coreBits G.Adj p h r z a (u - 8) (v - 8) huP (by omega)]
      simp [labelledVertex, hvA, hvP]
    · rw [if_neg hvA, if_neg hvP, if_pos hv,
        pToZ_coreBits G.Adj p h r z a (u - 8) (v - 15) huP (by omega)]
      simp [labelledVertex, hvA, hvP, hv]

end SeymourEight.FiveZHighDefectGraphBridge
