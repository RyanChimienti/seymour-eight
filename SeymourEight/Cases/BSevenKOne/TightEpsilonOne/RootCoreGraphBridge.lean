import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.RootRows.All
import SeymourEight.Cases.BSevenKOne.TightEpsilonOne.TerminalCoreGraphBridge
import SeymourEight.Cases.BSevenKOne.Counting
import SeymourEight.Shared.SameStatusKing
import Mathlib.Data.Fin.Tuple.Sort

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.EpsilonOneRootCoreGraphBridge

open BSevenKOne BSevenKOneCounting BSevenKOneTerminal CertificateBridge
  EpsilonOneRootCore FinalBranch FinalDefects Shared TerminalAlphaBeta
  TerminalCore TerminalCoreBridge TerminalCoreGraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

set_option maxHeartbeats 800000 in
/-- Boolean payload at one position of the 140-bit root-neighborhood core. -/
def coreBitAt (p : Fin 7 → V) (h : Fin 5 → V) (z : Fin 2 → V)
    (s : V) (n : Nat) : Bool :=
  if hnP : n < 49 then
    decide (G.Adj (p ⟨n / 7, by omega⟩)
      (p ⟨n % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnPH : n < 84 then
    let q := n - 49
    decide (G.Adj (p ⟨q / 5, by omega⟩)
      (h ⟨q % 5, Nat.mod_lt _ (by omega)⟩))
  else if hnHP : n < 119 then
    let q := n - 84
    decide (G.Adj (h ⟨q / 7, by omega⟩)
      (p ⟨q % 7, Nat.mod_lt _ (by omega)⟩))
  else if hnExternal : n < 140 then
    let q := n - 119
    if q % 3 = 0 then decide (G.Adj (p ⟨q / 3, by omega⟩) s)
    else decide (G.Adj (p ⟨q / 3, by omega⟩)
      (z ⟨q % 3 - 1, by omega⟩))
  else false

set_option maxHeartbeats 800000 in
/-- Encode the three retained incidence matrices and the `P→({s}∪Z)` rows. -/
def coreBits (p : Fin 7 → V) (h : Fin 5 → V) (z : Fin 2 → V)
    (s : V) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE
      (List.ofFn fun n : Fin 140 ↦ coreBitAt G p h z s n))

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
@[simp]
theorem getLsbD_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (n : Nat) (hn : n < 140) :
    (coreBits G p h z s).getLsbD n = coreBitAt G p h z s n := by
  classical
  rw [coreBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa using hn) false,
    List.getElem_ofFn]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
@[simp]
theorem pArc_coreBits (p : Fin 7 → V) (h : Fin 5 → V) (z : Fin 2 → V)
    (s : V) (i j : Nat) (hi : i < 7) (hj : j < 7) :
    EpsilonOneRootCore.pArc (coreBits G p h z s) i j =
      decide (G.Adj (p ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  classical
  have hDiv : (i * 7 + j) / 7 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * 7 + j) % 7 = j := Nat.mul_add_mod_of_lt hj
  rw [EpsilonOneRootCore.pArc,
    getLsbD_coreBits G p h z s (i * 7 + j) (by omega)]
  simp [coreBitAt, show i * 7 + j < 49 by omega, hDiv, hMod]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
@[simp]
theorem pToH_coreBits (p : Fin 7 → V) (h : Fin 5 → V) (z : Fin 2 → V)
    (s : V) (i j : Nat) (hi : i < 7) (hj : j < 5) :
    EpsilonOneRootCore.pToH (coreBits G p h z s) i j =
      decide (G.Adj (p ⟨i, hi⟩) (h ⟨j, hj⟩)) := by
  classical
  have hDiv : (i * 5 + j) / 5 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * 5 + j) % 5 = j := Nat.mul_add_mod_of_lt hj
  rw [EpsilonOneRootCore.pToH,
    getLsbD_coreBits G p h z s (49 + i * 5 + j) (by omega)]
  simp [coreBitAt, show ¬49 + i * 5 + j < 49 by omega,
    show 49 + i * 5 + j < 84 by omega,
    show 49 + i * 5 + j - 49 = i * 5 + j by omega, hDiv, hMod]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
@[simp]
theorem hToP_coreBits (p : Fin 7 → V) (h : Fin 5 → V) (z : Fin 2 → V)
    (s : V) (i j : Nat) (hi : i < 5) (hj : j < 7) :
    EpsilonOneRootCore.hToP (coreBits G p h z s) i j =
      decide (G.Adj (h ⟨i, hi⟩) (p ⟨j, hj⟩)) := by
  classical
  have hDiv : (i * 7 + j) / 7 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj]
  have hMod : (i * 7 + j) % 7 = j := Nat.mul_add_mod_of_lt hj
  rw [EpsilonOneRootCore.hToP,
    getLsbD_coreBits G p h z s (84 + i * 7 + j) (by omega)]
  simp [coreBitAt, show ¬84 + i * 7 + j < 49 by omega,
    show ¬84 + i * 7 + j < 84 by omega,
    show 84 + i * 7 + j < 119 by omega,
    show 84 + i * 7 + j - 84 = i * 7 + j by omega, hDiv, hMod]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
@[simp]
theorem rootArc_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (i : Nat) (hi : i < 7) :
    EpsilonOneRootCore.rootArc (coreBits G p h z s) i =
      decide (G.Adj (p ⟨i, hi⟩) s) := by
  classical
  rw [EpsilonOneRootCore.rootArc,
    getLsbD_coreBits G p h z s (119 + i * 3) (by omega)]
  simp [coreBitAt, show ¬119 + i * 3 < 49 by omega,
    show ¬119 + i * 3 < 84 by omega,
    show ¬119 + i * 3 < 119 by omega,
    show 119 + i * 3 < 140 by omega,
    show 119 + i * 3 - 119 = i * 3 by omega]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
@[simp]
theorem pToZ_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (i j : Nat) (hi : i < 7) (hj : j < 2) :
    EpsilonOneRootCore.pToZ (coreBits G p h z s) i j =
      decide (G.Adj (p ⟨i, hi⟩) (z ⟨j, hj⟩)) := by
  classical
  rw [EpsilonOneRootCore.pToZ,
    getLsbD_coreBits G p h z s (120 + i * 3 + j) (by omega)]
  have hq : 120 + i * 3 + j - 119 = i * 3 + (j + 1) := by omega
  have hDiv : (i * 3 + (j + 1)) / 3 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt (show j + 1 < 3 by omega)]
  have hMod : (i * 3 + (j + 1)) % 3 = j + 1 :=
    Nat.mul_add_mod_of_lt (by omega)
  simp [coreBitAt, show ¬120 + i * 3 + j < 49 by omega,
    show ¬120 + i * 3 + j < 84 by omega,
    show ¬120 + i * 3 + j < 119 by omega,
    show 120 + i * 3 + j < 140 by omega, hq, hDiv, hMod]

/-! ## Decoded counts -/

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem pOutCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (i : Nat) (hi : i < 7) :
    EpsilonOneRootCore.pOutCount (coreBits G p h z s) i =
      labelledPOutCount G.Adj p i := by
  classical
  simp [EpsilonOneRootCore.pOutCount, labelledPOutCount, labelledPArc,
    sumSeven, pArc_coreBits, pAt_of_lt, hi]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem pToHCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (i : Nat) (hi : i < 7) :
    EpsilonOneRootCore.pToHCount (coreBits G p h z s) i =
      labelledPToHCount G.Adj p h i := by
  classical
  simp [EpsilonOneRootCore.pToHCount, labelledPToHCount, labelledPToH,
    sumFive, pToH_coreBits, pAt_of_lt, hAt_of_lt, hi]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem secondPCount_coreBits (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (i : Nat) (hi : i < 7) :
    EpsilonOneRootCore.secondPCount (coreBits G p h z s) i =
      labelledSecondPCount G.Adj p h i := by
  classical
  simp [EpsilonOneRootCore.secondPCount, EpsilonOneRootCore.reachedViaPOrH,
    labelledSecondPCount, labelledReachedViaPOrH, labelledPArc,
    labelledPToH, labelledHToP, sumSeven, anySeven, anyFive,
    pArc_coreBits, pToH_coreBits, hToP_coreBits, pAt_of_lt, hAt_of_lt, hi]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem orientedOnP_coreBits_true (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) (hG : G.IsOriented) :
    EpsilonOneRootCore.orientedOnP (coreBits G p h z s) = true := by
  classical
  have hLoop : ∀ i : Fin 7, ¬G.Adj (p i) (p i) := fun i ↦ hG.1 _
  have hAnti : ∀ i j : Fin 7, ¬(G.Adj (p i) (p j) ∧ G.Adj (p j) (p i)) := by
    intro i j hij
    exact hG.2 hij.1 hij.2
  have hOr : ∀ i j : Fin 7,
      ¬G.Adj (p i) (p j) ∨ ¬G.Adj (p j) (p i) := by
    intro i j
    by_cases hij : G.Adj (p i) (p j)
    · exact Or.inr (fun hji ↦ hAnti i j ⟨hij, hji⟩)
    · exact Or.inl hij
  simp [EpsilonOneRootCore.orientedOnP, allSeven, pArc_coreBits,
    hLoop, hOr]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem orientedBetweenPAndH_coreBits_true (p : Fin 7 → V)
    (h : Fin 5 → V) (z : Fin 2 → V) (s : V) (hG : G.IsOriented) :
    EpsilonOneRootCore.orientedBetweenPAndH (coreBits G p h z s) = true := by
  classical
  have hAnti : ∀ i : Fin 7, ∀ j : Fin 5,
      ¬(G.Adj (p i) (h j) ∧ G.Adj (h j) (p i)) := by
    intro i j hij
    exact hG.2 hij.1 hij.2
  have hOr : ∀ i : Fin 7, ∀ j : Fin 5,
      ¬G.Adj (p i) (h j) ∨ ¬G.Adj (h j) (p i) := by
    intro i j
    by_cases hij : G.Adj (p i) (h j)
    · exact Or.inr (fun hji ↦ hAnti i j ⟨hij, hji⟩)
    · exact Or.inl hij
  simp [EpsilonOneRootCore.orientedBetweenPAndH, allSeven, allFive,
    pToH_coreBits, hToP_coreBits, hOr]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem pOutCount_toNat (P : Finset V) (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 5 → V) (z : Fin 2 → V) (s : V) (i : Nat) (hi : i < 7) :
    (EpsilonOneRootCore.pOutCount
      (coreBits G (fun j ↦ (p j).1) h z s) i).toNat =
      directCount G P (p ⟨i, hi⟩).1 := by
  classical
  rw [pOutCount_coreBits G (fun j ↦ (p j).1) h z s i hi]
  simpa only [pAt_of_lt (fun j ↦ (p j).1) i hi] using
    labelledPOutCount_toNat G P p i

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem pToHCount_toNat (H : Finset V) (p : Fin 7 → V)
    (h : Fin 5 ≃ {v : V // v ∈ H}) (z : Fin 2 → V) (s : V)
    (i : Nat) (hi : i < 7) :
    (EpsilonOneRootCore.pToHCount
      (coreBits G p (fun j ↦ (h j).1) z s) i).toNat =
      directCount G H (p ⟨i, hi⟩) := by
  classical
  rw [pToHCount_coreBits G p (fun j ↦ (h j).1) z s i hi]
  simpa only [pAt_of_lt p i hi] using
    labelledPToHCount_toNat G p H h i

set_option maxHeartbeats 800000 in
theorem externalCount_toNat (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 5 → V)
    (z : Fin 2 ≃ {v : V // v ∈ C.Z}) (i : Nat) (hi : i < 7) :
    (EpsilonOneRootCore.externalCount
      (coreBits G p h (fun j ↦ (z j).1) C.s) i).toNat =
      epsilonAt G (p ⟨i, hi⟩) C.s + directCount G C.Z (p ⟨i, hi⟩) := by
  have hZ := directCount_eq_sum_bool G C.Z z (p ⟨i, hi⟩)
    (fun j ↦ decide (G.Adj (p ⟨i, hi⟩) (z j).1)) (fun j ↦ by simp)
  simp only [Fin.sum_univ_succ] at hZ
  rw [EpsilonOneRootCore.externalCount, rootArc_coreBits G p h
    (fun j ↦ (z j).1) C.s i hi,
    pToZ_coreBits G p h (fun j ↦ (z j).1) C.s i 0 hi (by omega),
    pToZ_coreBits G p h (fun j ↦ (z j).1) C.s i 1 hi (by omega)]
  simp only [bitCount, epsilonAt]
  by_cases hs : G.Adj (p ⟨i, hi⟩) C.s <;>
    by_cases hz0 : G.Adj (p ⟨i, hi⟩) (z 0).1 <;>
    by_cases hz1 : G.Adj (p ⟨i, hi⟩) (z 1).1 <;>
    simp [hs, hz0, hz1] at hZ ⊢ <;> omega

set_option maxHeartbeats 800000 in
theorem retainedDegree_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (z : Fin 2 ≃ {v : V // v ∈ C.Z}) (i : Nat) (hi : i < 7) :
    (EpsilonOneRootCore.retainedDegree
      (coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) C.s) i).toNat =
      G.outdegree (p ⟨i, hi⟩).1 := by
  let u := (p ⟨i, hi⟩).1
  have huP : u ∈ C.P := (p ⟨i, hi⟩).2
  have hCaptured := outgoingCaptured_of_p_eq_B G C hG hPB u huP
  have hDegree : G.outdegree u = directCount G C.Z u + epsilonAt G u C.s +
      directCount G C.H u + directCount G C.P u := by
    unfold Digraph.outdegree directCount internalFirstNeighbors
    have hUnion : G.outNeighborFinset u =
        (C.Z ∪ {C.s} ∪ C.H ∪ C.P).filter (G.Adj u) := by
      ext v
      simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
        Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro huv
        exact ⟨by simpa only [Finset.mem_union, Finset.mem_singleton] using
          hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩
      · exact fun hv ↦ hv.2
    rw [hUnion]
    have hZs : Disjoint C.Z {C.s} := by
      rw [Finset.disjoint_left]
      intro v hvZ hvs
      exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C
        (Finset.mem_singleton.mp hvs ▸ hvZ)
    have hZsH : Disjoint (C.Z ∪ {C.s}) C.H := by
      rw [Finset.disjoint_left]
      intro v hv hvH
      rcases Finset.mem_union.mp hv with hvZ | hvs
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
      · have hvsEq : v = C.s := Finset.mem_singleton.mp hvs
        subst v
        exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1 hvH
    have hAllP : Disjoint (C.Z ∪ {C.s} ∪ C.H) C.P := by
      rw [Finset.disjoint_left]
      intro v hv hvP
      rcases Finset.mem_union.mp hv with hv | hvH
      · rcases Finset.mem_union.mp hv with hvZ | hvs
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
        · have hvsEq : v = C.s := Finset.mem_singleton.mp hvs
          subst v
          exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
    have hZsFilter : Disjoint (C.Z.filter (G.Adj u))
        (({C.s} : Finset V).filter (G.Adj u)) :=
      Finset.disjoint_filter_filter (p := G.Adj u) (q := G.Adj u) hZs
    have hZsHFilter : Disjoint
        ((C.Z.filter (G.Adj u)) ∪ (({C.s} : Finset V).filter (G.Adj u)))
        (C.H.filter (G.Adj u)) := by
      rw [Finset.disjoint_left]
      intro v hv hvH
      apply (Finset.disjoint_left.mp hZsH) ?_ (Finset.mem_filter.mp hvH).1
      rcases Finset.mem_union.mp hv with hvZ | hvs
      · exact Finset.mem_union_left _ (Finset.mem_filter.mp hvZ).1
      · exact Finset.mem_union_right _ (Finset.mem_filter.mp hvs).1
    have hAllPFilter : Disjoint
        (((C.Z.filter (G.Adj u)) ∪ (({C.s} : Finset V).filter (G.Adj u))) ∪
          (C.H.filter (G.Adj u))) (C.P.filter (G.Adj u)) := by
      rw [Finset.disjoint_left]
      intro v hv hvP
      apply (Finset.disjoint_left.mp hAllP) ?_ (Finset.mem_filter.mp hvP).1
      rcases Finset.mem_union.mp hv with hvZs | hvH
      · rcases Finset.mem_union.mp hvZs with hvZ | hvs
        · exact Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mp hvZ).1)
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_filter.mp hvs).1)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mp hvH).1
    rw [Finset.filter_union, Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint hAllPFilter,
      Finset.card_union_of_disjoint hZsHFilter,
      Finset.card_union_of_disjoint hZsFilter]
    have hRootCard : (({C.s} : Finset V).filter (G.Adj u)).card =
        epsilonAt G u C.s := by
      by_cases hus : G.Adj u C.s
      · have hEq : ({C.s} : Finset V).filter (G.Adj u) = {C.s} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · exact fun hv ↦ hv.1
          · intro hv
            subst v
            exact ⟨rfl, hus⟩
        rw [hEq]
        simp [epsilonAt, hus]
      · have hEq : ({C.s} : Finset V).filter (G.Adj u) = ∅ := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_singleton,
            Finset.notMem_empty, iff_false]
          intro hv
          exact hus (hv.1 ▸ hv.2)
        rw [hEq]
        simp [epsilonAt, hus]
    rw [hRootCard]
  have hExternal := externalCount_toNat G C (fun j ↦ (p j).1)
    (fun j ↦ (h j).1) z i hi
  have hPH := pToHCount_toNat G C.H (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) C.s i hi
  have hPP := pOutCount_toNat G C.P p (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) C.s i hi
  have hZCard : C.Z.card = 2 := by
    simpa using (Fintype.card_congr z).symm
  have hHCard : C.H.card = 5 := by
    simpa using (Fintype.card_congr h).symm
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr p).symm
  have hExternalLe : epsilonAt G u C.s + directCount G C.Z u ≤ 3 := by
    have hZLe : directCount G C.Z u ≤ 2 := by
      exact (Finset.card_le_card
        (Finset.filter_subset (G.Adj u) C.Z)).trans_eq hZCard
    have hEpsilonLe : epsilonAt G u C.s ≤ 1 := by
      unfold epsilonAt
      split <;> omega
    omega
  have hPHLe : directCount G C.H u ≤ 5 :=
    (Finset.card_le_card (Finset.filter_subset (G.Adj u) C.H)).trans_eq hHCard
  have hPPLe : directCount G C.P u ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset (G.Adj u) C.P)).trans_eq hPCard
  change G.outdegree (p ⟨i, hi⟩).1 =
    directCount G C.Z (p ⟨i, hi⟩).1 +
      epsilonAt G (p ⟨i, hi⟩).1 C.s +
      directCount G C.H (p ⟨i, hi⟩).1 +
      directCount G C.P (p ⟨i, hi⟩).1 at hDegree
  change epsilonAt G (p ⟨i, hi⟩).1 C.s +
    directCount G C.Z (p ⟨i, hi⟩).1 ≤ 3 at hExternalLe
  change directCount G C.H (p ⟨i, hi⟩).1 ≤ 5 at hPHLe
  change directCount G C.P (p ⟨i, hi⟩).1 ≤ 7 at hPPLe
  simp only [EpsilonOneRootCore.retainedDegree, BitVec.toNat_add,
    Nat.reducePow, hExternal, hPH, hPP]
  omega

/-! ## The root-neighborhood inequality -/

set_option maxHeartbeats 800000 in
/-- A `P`-vertex cannot point from `P` into the residual part `R` of `A`. -/
theorem P_not_adj_R (C : G.LocalConfiguration) (p r : V)
    (hp : p ∈ C.P) (hr : r ∈ C.R) : ¬G.Adj p r := by
  intro hpr
  have hrX : r ∈ C.X := by
    apply Finset.mem_inter.mpr
    constructor
    · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨p, Finset.mem_union_right C.A1 hp, hpr⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hr, ?_⟩
      intro hParts
      apply (Finset.mem_sdiff.mp hr).2
      rcases Finset.mem_union.mp hParts with hrA1 | hra1
      · exact Finset.mem_union_left {C.a1}
          (Finset.mem_union_left C.X hrA1)
      · exact Finset.mem_union_right (C.A1 ∪ C.X) hra1
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))

set_option maxHeartbeats 800000 in
/-- Among the eight root outneighbors, a `P`-vertex can directly hit only `H`. -/
theorem direct_A_le_direct_H (C : G.LocalConfiguration) (hG : G.IsOriented)
    (p : V) (hp : p ∈ C.P) :
    directCount G C.A p ≤ directCount G C.H p := by
  apply Finset.card_le_card
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvA, hpv⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hpv⟩
  have hvParts : v ∈ (C.A1 ∪ C.X ∪ {C.a1}) ∪ C.R := by
    rw [Digraph.LocalConfiguration.local_parts_union_R (G := G) C]
    exact hvA
  rcases Finset.mem_union.mp hvParts with hvMain | hvR
  · rcases Finset.mem_union.mp hvMain with hvH | hva1
    · simpa [Digraph.LocalConfiguration.H] using hvH
    · have hvEq : v = C.a1 := Finset.mem_singleton.mp hva1
      subst v
      have ha1p : G.Adj C.a1 p := (Finset.mem_filter.mp hp).2
      exact (hG.2 hpv ha1p).elim
  · exact (P_not_adj_R G C p v hp hvR hpv).elim

set_option maxHeartbeats 800000 in
/-- Pointwise local degree decomposition for a member of `P=B`. -/
theorem pDegree_eq_external_add_H_add_P (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B) (p : V) (hp : p ∈ C.P) :
    G.outdegree p = directCount G C.Z p + epsilonAt G p C.s +
      directCount G C.H p + directCount G C.P p := by
  have hCaptured := outgoingCaptured_of_p_eq_B G C hG hPB p hp
  rw [outdegree_eq_directCount_of_captured G
    (C.Z ∪ {C.s} ∪ C.H ∪ C.P) p hCaptured]
  have hZs : Disjoint C.Z {C.s} := by
    rw [Finset.disjoint_left]
    intro v hvZ hvs
    exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C
      (Finset.mem_singleton.mp hvs ▸ hvZ)
  have hZsH : Disjoint (C.Z ∪ {C.s}) C.H := by
    rw [Finset.disjoint_left]
    intro v hv hvH
    rcases Finset.mem_union.mp hv with hvZ | hvs
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
    · have hvEq : v = C.s := Finset.mem_singleton.mp hvs
      subst v
      exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1 hvH
  have hAllP : Disjoint (C.Z ∪ {C.s} ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hv hvP
    rcases Finset.mem_union.mp hv with hv | hvH
    · rcases Finset.mem_union.mp hv with hvZ | hvs
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
      · have hvEq : v = C.s := Finset.mem_singleton.mp hvs
        subst v
        exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  rw [directCount_union_of_disjoint G _ _ p hAllP,
    directCount_union_of_disjoint G _ _ p hZsH,
    directCount_union_of_disjoint G _ _ p hZs]
  by_cases hps : G.Adj p C.s
  · have hRootFilter : ({C.s} : Finset V).filter (G.Adj p) = {C.s} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hv ↦ hv.1
      · intro hv
        subst v
        exact ⟨rfl, hps⟩
    simp [directCount, internalFirstNeighbors, epsilonAt, hps, hRootFilter]
  · have hRootFilter : ({C.s} : Finset V).filter (G.Adj p) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]
      intro hv
      exact hps (hv.1 ▸ hv.2)
    simp [directCount, internalFirstNeighbors, epsilonAt, hps, hRootFilter]

set_option maxHeartbeats 800000 in
/-- If `p→s`, the eight vertices of `A=N⁺(s)` and the represented strict
second neighbors in `P` give a disjoint lower bound for `N⁺⁺(p)`. -/
theorem rootNeighborhoodEquation (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (p : V) (hp : p ∈ C.P) (hps : G.Adj p C.s) :
    qCount G C.P C.H p + 9 ≤
      epsilonAt G p C.s + directCount G C.Z p +
        2 * directCount G C.H p + directCount G C.P p := by
  let Anew : Finset V := C.A.filter fun v ↦ ¬G.Adj p v
  have hAnewSecond : Anew ⊆ G.secondOutNeighborFinset p := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvA, hNotAdj⟩
    have hsv : G.Adj C.s v :=
      (Digraph.mem_outNeighborFinset (G := G)).mp hvA
    have hvp : v ≠ p := by
      intro hvp
      subst v
      exact hG.2 hps hsv
    rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨C.s, hps, hsv⟩, hNotAdj, hvp⟩
  have hQSecond : secondNeighborsThrough G C.P (C.P ∪ C.H) p ⊆
      G.secondOutNeighborFinset p :=
    secondNeighborsThrough_subset_secondOutNeighborFinset G C.P (C.P ∪ C.H) p
  have hAnewQDisjoint :
      Disjoint Anew (secondNeighborsThrough G C.P (C.P ∪ C.H) p) := by
    rw [Finset.disjoint_left]
    intro v hvA hvQ
    have hvA' : v ∈ C.A := (Finset.mem_filter.mp hvA).1
    have hvP : v ∈ C.P := (Finset.mem_filter.mp hvQ).1
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA'
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hSecondCard : Anew.card + qCount G C.P C.H p ≤
      G.secondOutdegree p := by
    have hSubset := Finset.union_subset hAnewSecond hQSecond
    have hCard := Finset.card_le_card hSubset
    rw [Finset.card_union_of_disjoint hAnewQDisjoint] at hCard
    exact hCard
  have hASplit : directCount G C.A p + Anew.card = 8 := by
    have hSplit := Finset.card_filter_add_card_filter_not
      (s := C.A) (G.Adj p)
    change directCount G C.A p + Anew.card = C.A.card at hSplit
    have hACard : C.A.card = 8 := by
      unfold Digraph.LocalConfiguration.A
      change (G.outNeighborFinset C.s).card = 8 at hRootDegree
      exact hRootDegree
    omega
  have hDirectA := direct_A_le_direct_H G C hG p hp
  have hDegree : G.outdegree p = directCount G C.Z p + epsilonAt G p C.s +
      directCount G C.H p + directCount G C.P p := by
    have hCaptured := outgoingCaptured_of_p_eq_B G C hG hPB p hp
    unfold Digraph.outdegree directCount internalFirstNeighbors
    have hUnion : G.outNeighborFinset p =
        (C.Z ∪ {C.s} ∪ C.H ∪ C.P).filter (G.Adj p) := by
      ext v
      simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter,
        Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro hpv
        exact ⟨by simpa only [Finset.mem_union, Finset.mem_singleton] using
          hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr hpv), hpv⟩
      · exact fun hv ↦ hv.2
    rw [hUnion]
    -- These four local classes are pairwise disjoint; `simp` can count the
    -- filtered union once the membership impossibilities are exposed.
    have hsZ := Digraph.LocalConfiguration.s_notMem_Z (G := G) C
    have hsH := Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1
    have hsP := Digraph.LocalConfiguration.s_notMem_P (G := G) C
    have hZH := Digraph.LocalConfiguration.disjoint_Z_H (G := G) C
    have hZP := Digraph.LocalConfiguration.disjoint_Z_P (G := G) C
    have hHP := Digraph.LocalConfiguration.disjoint_H_P (G := G) C
    rw [Finset.filter_union, Finset.filter_union, Finset.filter_union]
    have hPairwise :
        ((C.Z.filter (G.Adj p)) ∪ (({C.s} : Finset V).filter (G.Adj p)) ∪
          C.H.filter (G.Adj p) ∪ C.P.filter (G.Adj p)).card =
        (C.Z.filter (G.Adj p)).card +
          (({C.s} : Finset V).filter (G.Adj p)).card +
          (C.H.filter (G.Adj p)).card + (C.P.filter (G.Adj p)).card := by
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_union_of_disjoint]
        · rw [Finset.card_union_of_disjoint]
          exact Finset.disjoint_filter_filter (p := G.Adj p) (q := G.Adj p)
            (by simpa [Finset.disjoint_left] using
              (show Disjoint C.Z ({C.s} : Finset V) from by
                rw [Finset.disjoint_left]
                exact fun _ hz hsingle ↦ hsZ (Finset.mem_singleton.mp hsingle ▸ hz)))
        · rw [Finset.disjoint_left]
          intro v hv hvH
          rcases Finset.mem_union.mp hv with hvZ | hvs
          · exact (Finset.disjoint_left.mp hZH)
              (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvH).1
          · exact hsH (Finset.mem_singleton.mp (Finset.mem_filter.mp hvs).1 ▸
              (Finset.mem_filter.mp hvH).1)
      · rw [Finset.disjoint_left]
        intro v hv hvP
        rcases Finset.mem_union.mp hv with hvZH | hvH
        · rcases Finset.mem_union.mp hvZH with hvZ | hvs
          · exact (Finset.disjoint_left.mp hZP)
              (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
          · exact hsP (Finset.mem_singleton.mp (Finset.mem_filter.mp hvs).1 ▸
              (Finset.mem_filter.mp hvP).1)
        · exact (Finset.disjoint_left.mp hHP)
            (Finset.mem_filter.mp hvH).1 (Finset.mem_filter.mp hvP).1
    rw [hPairwise]
    have hRootCard : (({C.s} : Finset V).filter (G.Adj p)).card = 1 := by
      have hEq : ({C.s} : Finset V).filter (G.Adj p) = {C.s} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun hv ↦ hv.1
        · intro hv
          subst v
          exact ⟨rfl, hps⟩
      simp [hEq]
    rw [hRootCard]
    simp [epsilonAt, hps, Nat.add_left_comm, Nat.add_comm]
  have hSecondLt : G.secondOutdegree p < G.outdegree p := by
    have hpNot : ¬G.IsSeymourVertex p := by
      intro hpSeymour
      exact hNoSeymour ⟨p, hpSeymour⟩
    unfold Digraph.IsSeymourVertex at hpNot
    omega
  omega

set_option maxHeartbeats 800000 in
/-- The graph root-neighborhood inequality implies the corresponding Boolean
row of the compact core. -/
theorem rootEquationAt_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (z : Fin 2 ≃ {v : V // v ∈ C.Z}) (i : Nat) (hi : i < 7) :
    EpsilonOneRootCore.rootEquationAt
      (coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) C.s) i = true := by
  let bits := coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) C.s
  let u := (p ⟨i, hi⟩).1
  by_cases hps : G.Adj u C.s
  · have hEquation := rootNeighborhoodEquation G C hG hPB hNoSeymour
      hRootDegree u (p ⟨i, hi⟩).2 hps
    have hSecondNat : (EpsilonOneRootCore.secondPCount bits i).toNat ≤
        qCount G C.P C.H u := by
      rw [show EpsilonOneRootCore.secondPCount bits i =
          labelledSecondPCount G.Adj (fun j ↦ (p j).1)
            (fun j ↦ (h j).1) i by
        exact secondPCount_coreBits G (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1) C.s i hi]
      dsimp [u]
      exact labelledSecondPCount_toNat_le_qCount G C.P C.H p h i hi
    have hExternalNat : (EpsilonOneRootCore.externalCount bits i).toNat =
        epsilonAt G u C.s + directCount G C.Z u := by
      dsimp [bits, u]
      exact externalCount_toNat G C (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) z i hi
    have hPHNat : (EpsilonOneRootCore.pToHCount bits i).toNat =
        directCount G C.H u := by
      dsimp [bits, u]
      exact pToHCount_toNat G C.H (fun j ↦ (p j).1) h
        (fun j ↦ (z j).1) C.s i hi
    have hPPNat : (EpsilonOneRootCore.pOutCount bits i).toNat =
        directCount G C.P u := by
      dsimp [bits, u]
      exact pOutCount_toNat G C.P p (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) C.s i hi
    have hRoot : EpsilonOneRootCore.rootArc bits i = true := by
      dsimp [bits, u]
      simpa [rootArc_coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) C.s i hi] using hps
    have hPLe : directCount G C.P u ≤ 7 := by
      have hPCard : C.P.card = 7 := by
        simpa using (Fintype.card_congr p).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hHLe : directCount G C.H u ≤ 5 := by
      have hHCard : C.H.card = 5 := by
        simpa using (Fintype.card_congr h).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
    have hZLe : directCount G C.Z u ≤ 2 := by
      have hZCard : C.Z.card = 2 := by
        simpa using (Fintype.card_congr z).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
    have hQLe : qCount G C.P C.H u ≤ 7 := by
      unfold qCount secondNeighborsThrough
      have hPCard : C.P.card = 7 := by
        simpa using (Fintype.card_congr p).symm
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hNine : (9 : BitVec 8).toNat = 9 := by decide
    have hTwo : (2 : BitVec 8).toNat = 2 := by decide
    dsimp [u] at hEquation hSecondNat hExternalNat hPHNat hPPNat hPLe hHLe hZLe hQLe hps
    have hLeftNat :
        (EpsilonOneRootCore.secondPCount bits i + 9).toNat =
          (EpsilonOneRootCore.secondPCount bits i).toNat + 9 := by
      simp only [BitVec.toNat_add, Nat.reducePow, hNine]
      omega
    have hExternalLeNat :
        (EpsilonOneRootCore.externalCount bits i).toNat ≤ 3 := by
      rw [hExternalNat]
      simp [epsilonAt, hps]
      omega
    have hRightNat :
        (EpsilonOneRootCore.externalCount bits i +
          2 * EpsilonOneRootCore.pToHCount bits i +
          EpsilonOneRootCore.pOutCount bits i).toNat =
        (EpsilonOneRootCore.externalCount bits i).toNat +
          2 * (EpsilonOneRootCore.pToHCount bits i).toNat +
          (EpsilonOneRootCore.pOutCount bits i).toNat := by
      simp only [BitVec.toNat_add, BitVec.toNat_mul, Nat.reducePow, hTwo]
      omega
    change EpsilonOneRootCore.rootEquationAt bits i = true
    simp only [EpsilonOneRootCore.rootEquationAt, hRoot, Bool.not_true,
      Bool.false_or, BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hLeftNat, hRightNat, hExternalNat, hPHNat, hPPNat]
    omega
  · have hRoot : EpsilonOneRootCore.rootArc bits i = false := by
      dsimp [u] at hps
      dsimp [bits, u]
      rw [rootArc_coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) C.s i hi]
      simp [hps]
    change EpsilonOneRootCore.rootEquationAt bits i = true
    simp [EpsilonOneRootCore.rootEquationAt, hRoot]

/-! ## Aggregate decoding -/

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem totalPToH_toNat (P H : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 5 ≃ {v : V // v ∈ H}) (z : Fin 2 → V) (s : V) :
    (EpsilonOneRootCore.totalPToH
      (coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1) z s)).toNat =
      edgeCount G P H := by
  classical
  have hLt : edgeCount G P H < 256 := by
    have hPCard : P.card = 7 := by simpa using (Fintype.card_congr p).symm
    have hHCard : H.card = 5 := by simpa using (Fintype.card_congr h).symm
    calc
      edgeCount G P H ≤ P.card * H.card := edgeCount_le_card_mul_card G P H
      _ = 35 := by rw [hPCard, hHCard]
      _ < 256 := by omega
  have hLabel := labelledTotalPToH_toNat G P H p h hLt
  rw [← hLabel]
  congr 1
  simp [EpsilonOneRootCore.totalPToH, labelledTotalPToH,
    sumCountSeven, pToHCount_coreBits]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem totalPOut_toNat (P : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P}) (h : Fin 5 → V)
    (z : Fin 2 → V) (s : V) :
    (EpsilonOneRootCore.totalPOut
      (coreBits G (fun j ↦ (p j).1) h z s)).toNat = edgeCount G P P := by
  classical
  have hLt : edgeCount G P P < 256 := by
    have hPCard : P.card = 7 := by simpa using (Fintype.card_congr p).symm
    calc
      edgeCount G P P ≤ P.card * P.card := edgeCount_le_card_mul_card G P P
      _ = 49 := by rw [hPCard]
      _ < 256 := by omega
  have hLabel := labelledTotalPOut_toNat G P p hLt
  rw [← hLabel]
  congr 1
  simp [EpsilonOneRootCore.totalPOut, sumCountSeven, pOutCount_coreBits]

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem totalHToP_toNat (P H : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P})
    (h : Fin 5 ≃ {v : V // v ∈ H}) (z : Fin 2 → V) (s : V) :
    (EpsilonOneRootCore.totalHToP
      (coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1) z s)).toNat =
      edgeCount G H P := by
  classical
  have hLt : edgeCount G H P < 256 := by
    have hPCard : P.card = 7 := by simpa using (Fintype.card_congr p).symm
    have hHCard : H.card = 5 := by simpa using (Fintype.card_congr h).symm
    calc
      edgeCount G H P ≤ H.card * P.card := edgeCount_le_card_mul_card G H P
      _ = 35 := by rw [hPCard, hHCard]
      _ < 256 := by omega
  have hLabel := labelledTotalHToP_toNat G P H p h hLt
  rw [← hLabel]
  congr 1
  simp [EpsilonOneRootCore.totalHToP, labelledTotalHToP,
    labelledHToPCount, labelledHToP, sumCountFive, sumSeven, hToP_coreBits]

set_option maxHeartbeats 800000 in
theorem totalExternal_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 5 → V)
    (z : Fin 2 ≃ {v : V // v ∈ C.Z}) :
    (EpsilonOneRootCore.totalExternal
      (coreBits G (fun j ↦ (p j).1) h (fun j ↦ (z j).1) C.s)).toNat =
      edgeCount G C.P (externalTargets G C) := by
  let bits := coreBits G (fun j ↦ (p j).1) h (fun j ↦ (z j).1) C.s
  have hRow : ∀ i : Nat, (hi : i < 7) →
      (EpsilonOneRootCore.externalCount bits i).toNat =
        epsilonAt G (p ⟨i, hi⟩).1 C.s + directCount G C.Z (p ⟨i, hi⟩).1 := by
    intro i hi
    exact externalCount_toNat G C (fun j ↦ (p j).1) h z i hi
  have hRootSum : (∑ i : Fin 7, epsilonAt G (p i).1 C.s) =
      ∑ u ∈ C.P, epsilonAt G u C.s := by
    calc
      _ = ∑ u : {v : V // v ∈ C.P}, epsilonAt G u.1 C.s :=
        Equiv.sum_comp p (fun u : {v : V // v ∈ C.P} ↦
          epsilonAt G u.1 C.s)
      _ = _ := by
        rw [show (Finset.univ : Finset {v : V // v ∈ C.P}) = C.P.attach by
          exact Finset.univ_eq_attach C.P]
        exact C.P.sum_attach (fun u ↦ epsilonAt G u C.s)
  have hNaturalSum :
      (EpsilonOneRootCore.externalCount bits 0).toNat +
      (EpsilonOneRootCore.externalCount bits 1).toNat +
      (EpsilonOneRootCore.externalCount bits 2).toNat +
      (EpsilonOneRootCore.externalCount bits 3).toNat +
      (EpsilonOneRootCore.externalCount bits 4).toNat +
      (EpsilonOneRootCore.externalCount bits 5).toNat +
      (EpsilonOneRootCore.externalCount bits 6).toNat =
      edgeCount G C.P (externalTargets G C) := by
    have hFinSum : ∑ i : Fin 7,
        (EpsilonOneRootCore.externalCount bits i).toNat =
        edgeCount G C.P (externalTargets G C) := by
      calc
        _ = ∑ i : Fin 7, (epsilonAt G (p i).1 C.s +
            directCount G C.Z (p i).1) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hRow i i.isLt
        _ = (∑ i : Fin 7, epsilonAt G (p i).1 C.s) +
            ∑ i : Fin 7, directCount G C.Z (p i).1 :=
          Finset.sum_add_distrib
        _ = (∑ u ∈ C.P, epsilonAt G u C.s) + edgeCount G C.P C.Z := by
          rw [hRootSum]
          exact congrArg _ (edgeCount_eq_sum_fin G C.P C.Z p).symm
        _ = edgeCount G C.P (externalTargets G C) := by
          rw [edgeCount_externalTargets G C]
          omega
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hFinSum
  rw [EpsilonOneRootCore.totalExternal, toNat_sumCountSeven _ (by
    have hZCard : C.Z.card = 2 := by simpa using (Fintype.card_congr z).symm
    have hEach : ∀ i : Nat, (hi : i < 7) →
        epsilonAt G (p ⟨i, hi⟩).1 C.s +
          directCount G C.Z (p ⟨i, hi⟩).1 ≤ 3 := by
      intro i hi
      have hzLe : directCount G C.Z (p ⟨i, hi⟩).1 ≤ 2 := by
        exact (Finset.card_le_card
          (Finset.filter_subset (G.Adj (p ⟨i, hi⟩).1) C.Z)).trans_eq hZCard
      have heLe : epsilonAt G (p ⟨i, hi⟩).1 C.s ≤ 1 := by
        unfold epsilonAt
        split <;> omega
      omega
    have hr0 := hRow 0 (by omega)
    have hr1 := hRow 1 (by omega)
    have hr2 := hRow 2 (by omega)
    have hr3 := hRow 3 (by omega)
    have hr4 := hRow 4 (by omega)
    have hr5 := hRow 5 (by omega)
    have hr6 := hRow 6 (by omega)
    have h0 := hEach 0 (by omega)
    have h1 := hEach 1 (by omega)
    have h2 := hEach 2 (by omega)
    have h3 := hEach 3 (by omega)
    have h4 := hEach 4 (by omega)
    have h5 := hEach 5 (by omega)
    have h6 := hEach 6 (by omega)
    rw [hr0, hr1, hr2, hr3, hr4, hr5, hr6]
    omega)]
  exact hNaturalSum

set_option maxHeartbeats 800000 in
theorem rootReached_coreBits_true (C : G.LocalConfiguration)
    (hEpsilon : epsilonS G C = 1)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (h : Fin 5 → V) (z : Fin 2 → V) :
    EpsilonOneRootCore.rootReached
      (coreBits G (fun j ↦ (p j).1) h z C.s) = true := by
  rw [epsilonS_eq_ite] at hEpsilon
  split at hEpsilon
  next hExists =>
    obtain ⟨u, huP, hus⟩ := hExists
    obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
    have hus' : G.Adj (p i).1 C.s := by simpa [hi] using hus
    simp only [EpsilonOneRootCore.rootReached, anySeven, Bool.or_eq_true]
    have hBit : EpsilonOneRootCore.rootArc
        (coreBits G (fun j ↦ (p j).1) h z C.s) i = true := by
      rw [rootArc_coreBits G (fun j ↦ (p j).1) h z C.s i i.isLt]
      simpa using hus'
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
        i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases hiCases with hi0 | hi1 | hi2 | hi3 | hi4 | hi5 | hi6 <;>
      subst i <;> simp_all
  next hNone => omega

set_option maxHeartbeats 800000 in
theorem totalRetainedDegree_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (z : Fin 2 ≃ {v : V // v ∈ C.Z}) :
    (EpsilonOneRootCore.totalRetainedDegree
      (coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) C.s)).toNat =
      ∑ u ∈ C.P, G.outdegree u := by
  let bits := coreBits G (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) C.s
  have hRow : ∀ i : Nat, (hi : i < 7) →
      (EpsilonOneRootCore.retainedDegree bits i).toNat =
        G.outdegree (p ⟨i, hi⟩).1 := by
    intro i hi
    exact retainedDegree_toNat G C hG hPB p h z i hi
  have hZCard : C.Z.card = 2 := by simpa using (Fintype.card_congr z).symm
  have hHCard : C.H.card = 5 := by simpa using (Fintype.card_congr h).symm
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hDegreeLe : ∀ i : Nat, (hi : i < 7) →
      G.outdegree (p ⟨i, hi⟩).1 ≤ 15 := by
    intro i hi
    let u := (p ⟨i, hi⟩).1
    have hCaptured := outgoingCaptured_of_p_eq_B G C hG hPB u (p ⟨i, hi⟩).2
    have hCard := Finset.card_le_card hCaptured
    have hUnionCard : (C.Z ∪ {C.s} ∪ C.H ∪ C.P).card ≤
        C.Z.card + 1 + C.H.card + C.P.card := by
      calc
        _ ≤ (C.Z ∪ {C.s} ∪ C.H).card + C.P.card := Finset.card_union_le _ _
        _ ≤ ((C.Z ∪ {C.s}).card + C.H.card) + C.P.card := by
          gcongr
          exact Finset.card_union_le _ _
        _ ≤ ((C.Z.card + 1) + C.H.card) + C.P.card := by
          gcongr
          exact Finset.card_union_le _ _
    change G.outdegree u ≤ 15
    unfold Digraph.outdegree
    omega
  have hFinSum : (∑ i : Fin 7,
      (EpsilonOneRootCore.retainedDegree bits i).toNat) =
      ∑ u ∈ C.P, G.outdegree u := by
    calc
      _ = ∑ i : Fin 7, G.outdegree (p i).1 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hRow i i.isLt
      _ = ∑ u : {v : V // v ∈ C.P}, G.outdegree u.1 :=
        Equiv.sum_comp p (fun u : {v : V // v ∈ C.P} ↦ G.outdegree u.1)
      _ = _ := by
        rw [show (Finset.univ : Finset {v : V // v ∈ C.P}) = C.P.attach by
          exact Finset.univ_eq_attach C.P]
        exact C.P.sum_attach G.outdegree
  rw [EpsilonOneRootCore.totalRetainedDegree, toNat_sumCountSeven _ (by
    have hr0 := hRow 0 (by omega)
    have hr1 := hRow 1 (by omega)
    have hr2 := hRow 2 (by omega)
    have hr3 := hRow 3 (by omega)
    have hr4 := hRow 4 (by omega)
    have hr5 := hRow 5 (by omega)
    have hr6 := hRow 6 (by omega)
    have h0 := hDegreeLe 0 (by omega)
    have h1 := hDegreeLe 1 (by omega)
    have h2 := hDegreeLe 2 (by omega)
    have h3 := hDegreeLe 3 (by omega)
    have h4 := hDegreeLe 4 (by omega)
    have h5 := hDegreeLe 5 (by omega)
    have h6 := hDegreeLe 6 (by omega)
    rw [hr0, hr1, hr2, hr3, hr4, hr5, hr6]
    omega)]
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using hFinSum

/-! ## Canonical ordering of the seven `P` labels -/

set_option maxHeartbeats 800000 in
/-- Sort by degree, then root incidence, then the `P→H` row count. -/
noncomputable def rootSortedFinsetEquiv
    (degree rootCount hCount : V → Nat) (P : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P}) : Fin 7 ≃ {v : V // v ∈ P} :=
  (Tuple.sort (fun i : Fin 7 ↦ OrderDual.toDual
    (65536 * degree (p i).1 + 256 * rootCount (p i).1 + hCount (p i).1))).trans p

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem rootSorted_key_anti
    (degree rootCount hCount : V → Nat) (P : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P}) {i j : Fin 7} (hij : i ≤ j) :
    65536 * degree (rootSortedFinsetEquiv degree rootCount hCount P p i).1 +
        256 * rootCount (rootSortedFinsetEquiv degree rootCount hCount P p i).1 +
        hCount (rootSortedFinsetEquiv degree rootCount hCount P p i).1 ≥
      65536 * degree (rootSortedFinsetEquiv degree rootCount hCount P p j).1 +
        256 * rootCount (rootSortedFinsetEquiv degree rootCount hCount P p j).1 +
        hCount (rootSortedFinsetEquiv degree rootCount hCount P p j).1 := by
  exact Tuple.monotone_sort (fun q : Fin 7 ↦ OrderDual.toDual
    (65536 * degree (p q).1 + 256 * rootCount (p q).1 + hCount (p q).1)) hij

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem rootSorted_degree_anti
    (degree rootCount hCount : V → Nat) (P : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P})
    (hRootLe : ∀ v, rootCount v ≤ 1) (hHLt : ∀ v, hCount v < 256)
    {i j : Fin 7} (hij : i ≤ j) :
    degree (rootSortedFinsetEquiv degree rootCount hCount P p j).1 ≤
      degree (rootSortedFinsetEquiv degree rootCount hCount P p i).1 := by
  have hKey := rootSorted_key_anti degree rootCount hCount P p hij
  have hri := hRootLe (rootSortedFinsetEquiv degree rootCount hCount P p i).1
  have hrj := hRootLe (rootSortedFinsetEquiv degree rootCount hCount P p j).1
  have hhi := hHLt (rootSortedFinsetEquiv degree rootCount hCount P p i).1
  have hhj := hHLt (rootSortedFinsetEquiv degree rootCount hCount P p j).1
  omega

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem rootSorted_root_anti_of_degree_eq
    (degree rootCount hCount : V → Nat) (P : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P})
    (hHLt : ∀ v, hCount v < 256) {i j : Fin 7} (hij : i ≤ j)
    (hDegree : degree (rootSortedFinsetEquiv degree rootCount hCount P p i).1 =
      degree (rootSortedFinsetEquiv degree rootCount hCount P p j).1) :
    rootCount (rootSortedFinsetEquiv degree rootCount hCount P p j).1 ≤
      rootCount (rootSortedFinsetEquiv degree rootCount hCount P p i).1 := by
  have hKey := rootSorted_key_anti degree rootCount hCount P p hij
  have hhi := hHLt (rootSortedFinsetEquiv degree rootCount hCount P p i).1
  have hhj := hHLt (rootSortedFinsetEquiv degree rootCount hCount P p j).1
  omega

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] in
theorem rootSorted_h_anti_of_degree_root_eq
    (degree rootCount hCount : V → Nat) (P : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ P}) {i j : Fin 7} (hij : i ≤ j)
    (hDegree : degree (rootSortedFinsetEquiv degree rootCount hCount P p i).1 =
      degree (rootSortedFinsetEquiv degree rootCount hCount P p j).1)
    (hRoot : rootCount (rootSortedFinsetEquiv degree rootCount hCount P p i).1 =
      rootCount (rootSortedFinsetEquiv degree rootCount hCount P p j).1) :
    hCount (rootSortedFinsetEquiv degree rootCount hCount P p j).1 ≤
      hCount (rootSortedFinsetEquiv degree rootCount hCount P p i).1 := by
  have hKey := rootSorted_key_anti degree rootCount hCount P p hij
  omega

set_option maxHeartbeats 800000 in
theorem orderedPair_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p0 : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (z : Fin 2 ≃ {v : V // v ∈ C.Z})
    (i j : Fin 7) (hij : i ≤ j) :
    let p := rootSortedFinsetEquiv G.outdegree
      (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
    let bits := coreBits G (fun q ↦ (p q).1) (fun q ↦ (h q).1)
      (fun q ↦ (z q).1) C.s
    ((EpsilonOneRootCore.retainedDegree bits j).ule
        (EpsilonOneRootCore.retainedDegree bits i) &&
      (!(EpsilonOneRootCore.retainedDegree bits i ==
          EpsilonOneRootCore.retainedDegree bits j) ||
        ((!EpsilonOneRootCore.rootArc bits j ||
            EpsilonOneRootCore.rootArc bits i) &&
          (!(EpsilonOneRootCore.rootArc bits i ==
              EpsilonOneRootCore.rootArc bits j) ||
            (EpsilonOneRootCore.pToHCount bits j).ule
              (EpsilonOneRootCore.pToHCount bits i))))) = true := by
  dsimp only
  let p := rootSortedFinsetEquiv G.outdegree
    (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
  let bits := coreBits G (fun q ↦ (p q).1) (fun q ↦ (h q).1)
    (fun q ↦ (z q).1) C.s
  have hRootLe : ∀ v, epsilonAt G v C.s ≤ 1 := by
    intro v
    unfold epsilonAt
    split <;> omega
  have hHLt : ∀ v, directCount G C.H v < 256 := by
    intro v
    have hHCard : C.H.card = 5 := by simpa using (Fintype.card_congr h).symm
    have hLe : directCount G C.H v ≤ 5 := by
      exact (Finset.card_le_card
        (Finset.filter_subset (G.Adj v) C.H)).trans_eq hHCard
    omega
  have hDegreeLe := rootSorted_degree_anti G.outdegree
    (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
    hRootLe hHLt hij
  have hDegreeNat : ∀ q : Fin 7,
      (EpsilonOneRootCore.retainedDegree bits q).toNat = G.outdegree (p q).1 := by
    intro q
    exact retainedDegree_toNat G C hG hPB p h z q q.isLt
  have hHNat : ∀ q : Fin 7,
      (EpsilonOneRootCore.pToHCount bits q).toNat = directCount G C.H (p q).1 := by
    intro q
    exact pToHCount_toNat G C.H (fun k ↦ (p k).1) h
      (fun k ↦ (z k).1) C.s q q.isLt
  have hRootNat : ∀ q : Fin 7,
      (EpsilonOneRootCore.rootArc bits q = true ↔ G.Adj (p q).1 C.s) := by
    intro q
    dsimp [bits]
    rw [rootArc_coreBits G (fun k ↦ (p k).1) (fun k ↦ (h k).1)
      (fun k ↦ (z k).1) C.s q q.isLt]
    simp
  have hFirst : (EpsilonOneRootCore.retainedDegree bits j).ule
      (EpsilonOneRootCore.retainedDegree bits i) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hDegreeNat]
    exact hDegreeLe
  rw [Bool.and_eq_true]
  refine ⟨hFirst, ?_⟩
  by_cases hDegreeEq : EpsilonOneRootCore.retainedDegree bits i =
      EpsilonOneRootCore.retainedDegree bits j
  · have hGraphDegreeEq : G.outdegree (p i).1 = G.outdegree (p j).1 := by
      rw [← hDegreeNat i, ← hDegreeNat j, hDegreeEq]
    have hRootLe' := rootSorted_root_anti_of_degree_eq G.outdegree
      (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0 hHLt hij
      hGraphDegreeEq
    have hRootOrder : (!EpsilonOneRootCore.rootArc bits j ||
        EpsilonOneRootCore.rootArc bits i) = true := by
      by_cases hiRoot : G.Adj (p i).1 C.s <;>
        by_cases hjRoot : G.Adj (p j).1 C.s
      · have hiBit := (hRootNat i).mpr hiRoot
        have hjBit := (hRootNat j).mpr hjRoot
        simp [hiBit, hjBit]
      · have hiBit := (hRootNat i).mpr hiRoot
        have hjBit : EpsilonOneRootCore.rootArc bits j = false := by
          exact Bool.eq_false_of_not_eq_true (fun hbit ↦ hjRoot ((hRootNat j).mp hbit))
        simp [hiBit, hjBit]
      · have hiE : epsilonAt G (p i).1 C.s = 0 := by simp [epsilonAt, hiRoot]
        have hjE : epsilonAt G (p j).1 C.s = 1 := by simp [epsilonAt, hjRoot]
        change epsilonAt G (p j).1 C.s ≤ epsilonAt G (p i).1 C.s at hRootLe'
        omega
      · have hjBit : EpsilonOneRootCore.rootArc bits j = false := by
          exact Bool.eq_false_of_not_eq_true (fun hbit ↦ hjRoot ((hRootNat j).mp hbit))
        simp [hjBit]
    rw [Bool.or_eq_true]
    apply Or.inr
    rw [Bool.and_eq_true]
    refine ⟨hRootOrder, ?_⟩
    by_cases hRootEq : EpsilonOneRootCore.rootArc bits i =
        EpsilonOneRootCore.rootArc bits j
    · have hGraphRootEq : epsilonAt G (p i).1 C.s = epsilonAt G (p j).1 C.s := by
        dsimp [bits] at hRootEq
        rw [rootArc_coreBits G _ _ _ C.s i i.isLt,
          rootArc_coreBits G _ _ _ C.s j j.isLt] at hRootEq
        unfold epsilonAt
        split <;> split <;> simp_all
      have hHLe' := rootSorted_h_anti_of_degree_root_eq G.outdegree
        (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0 hij
        hGraphDegreeEq hGraphRootEq
      have hHBit : (EpsilonOneRootCore.pToHCount bits j).ule
          (EpsilonOneRootCore.pToHCount bits i) = true := by
        simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hHNat]
        exact hHLe'
      rw [Bool.or_eq_true]
      exact Or.inr hHBit
    · rw [Bool.or_eq_true]
      apply Or.inl
      simp only [Bool.not_eq_true']
      apply Bool.eq_false_iff.mpr
      intro hEq
      exact hRootEq (beq_iff_eq.mp hEq)
  · rw [Bool.or_eq_true]
    apply Or.inl
    simpa using hDegreeEq

set_option maxHeartbeats 800000 in
theorem orderedP_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (p0 : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (z : Fin 2 ≃ {v : V // v ∈ C.Z}) :
    let p := rootSortedFinsetEquiv G.outdegree
      (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
    EpsilonOneRootCore.orderedP
      (coreBits G (fun q ↦ (p q).1) (fun q ↦ (h q).1)
        (fun q ↦ (z q).1) C.s) = true := by
  dsimp only
  unfold EpsilonOneRootCore.orderedP
  simp only [Bool.and_eq_true]
  have h01 := orderedPair_coreBits_true G C hG hPB p0 h z 0 1 (by omega)
  have h12 := orderedPair_coreBits_true G C hG hPB p0 h z 1 2 (by omega)
  have h23 := orderedPair_coreBits_true G C hG hPB p0 h z 2 3 (by omega)
  have h34 := orderedPair_coreBits_true G C hG hPB p0 h z 3 4 (by omega)
  have h45 := orderedPair_coreBits_true G C hG hPB p0 h z 4 5 (by omega)
  have h56 := orderedPair_coreBits_true G C hG hPB p0 h z 5 6 (by omega)
  simp only [Bool.and_eq_true] at h01 h12 h23 h34 h45 h56
  exact ⟨⟨⟨⟨⟨⟨h01.1, h01.2⟩, ⟨h12.1, h12.2⟩⟩,
    ⟨h23.1, h23.2⟩⟩, ⟨h34.1, h34.2⟩⟩,
    ⟨h45.1, h45.2⟩⟩, ⟨h56.1, h56.2⟩⟩

/-! ## Packaging and terminal contradiction -/

set_option linter.flexible false in
set_option maxHeartbeats 800000 in
theorem coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 1)
    (p0 : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (z : Fin 2 ≃ {v : V // v ∈ C.Z})
    (missing alpha beta : Nat)
    (hExternal : edgeCount G C.P (externalTargets G C) + missing = 21)
    (hPToH : edgeCount G C.P C.H + alpha = 17)
    (hPOut : edgeCount G C.P C.P + beta = 21)
    (hHToP : 18 ≤ edgeCount G C.H C.P)
    (hDegreeSum : (∑ u ∈ C.P, G.outdegree u) + missing + alpha + beta = 59) :
    let p := rootSortedFinsetEquiv G.outdegree
      (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
    EpsilonOneRootCore.core missing alpha beta
      (coreBits G (fun q ↦ (p q).1) (fun q ↦ (h q).1)
        (fun q ↦ (z q).1) C.s) = true := by
  dsimp only
  let p := rootSortedFinsetEquiv G.outdegree
    (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
  let bits := coreBits G (fun q ↦ (p q).1) (fun q ↦ (h q).1)
    (fun q ↦ (z q).1) C.s
  have hOrP := orientedOnP_coreBits_true G (fun q ↦ (p q).1)
    (fun q ↦ (h q).1) (fun q ↦ (z q).1) C.s hG
  have hOrPH := orientedBetweenPAndH_coreBits_true G (fun q ↦ (p q).1)
    (fun q ↦ (h q).1) (fun q ↦ (z q).1) C.s hG
  have hRoot := rootReached_coreBits_true G C hEpsilon p
    (fun q ↦ (h q).1) (fun q ↦ (z q).1)
  have hExternalNat := totalExternal_toNat G C p (fun q ↦ (h q).1) z
  have hPToHNat := totalPToH_toNat G C.P C.H p h
    (fun q ↦ (z q).1) C.s
  have hPOutNat := totalPOut_toNat G C.P p (fun q ↦ (h q).1)
    (fun q ↦ (z q).1) C.s
  have hHToPNat := totalHToP_toNat G C.P C.H p h
    (fun q ↦ (z q).1) C.s
  have hDegreeNat := totalRetainedDegree_toNat G C hG hPB p h z
  change (EpsilonOneRootCore.totalExternal bits).toNat =
    edgeCount G C.P (externalTargets G C) at hExternalNat
  change (EpsilonOneRootCore.totalPToH bits).toNat =
    edgeCount G C.P C.H at hPToHNat
  change (EpsilonOneRootCore.totalPOut bits).toNat =
    edgeCount G C.P C.P at hPOutNat
  change (EpsilonOneRootCore.totalHToP bits).toNat =
    edgeCount G C.H C.P at hHToPNat
  change (EpsilonOneRootCore.totalRetainedDegree bits).toNat =
    ∑ u ∈ C.P, G.outdegree u at hDegreeNat
  have hMissingLe : missing ≤ 21 := by omega
  have hAlphaLe : alpha ≤ 17 := by omega
  have hBetaLe : beta ≤ 21 := by omega
  have hDefectsLe : missing + alpha + beta ≤ 59 := by omega
  have hTwentyOne : (21 : BitVec 8).toNat = 21 := by decide
  have hSeventeen : (17 : BitVec 8).toNat = 17 := by decide
  have hFiftyNine : (59 : BitVec 8).toNat = 59 := by decide
  have hExternalSum : (EpsilonOneRootCore.totalExternal bits).toNat +
      missing = 21 := by omega
  have hPToHSum : (EpsilonOneRootCore.totalPToH bits).toNat + alpha = 17 := by omega
  have hPOutSum : (EpsilonOneRootCore.totalPOut bits).toNat + beta = 21 := by omega
  have hDegreeSum' : (EpsilonOneRootCore.totalRetainedDegree bits).toNat +
      missing + alpha + beta = 59 := by omega
  have hExternalBit : EpsilonOneRootCore.totalExternal bits +
      BitVec.ofNat 8 missing = 21 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
      hTwentyOne]
    omega
  have hPToHBit : EpsilonOneRootCore.totalPToH bits +
      BitVec.ofNat 8 alpha = 17 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, hSeventeen]
    omega
  have hPOutBit : EpsilonOneRootCore.totalPOut bits +
      BitVec.ofNat 8 beta = 21 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, hTwentyOne]
    omega
  have hHToPBit : (18 : BitVec 8).ule
      (EpsilonOneRootCore.totalHToP bits) = true := by
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq, hHToPNat]
    exact hHToP
  have hPer : ∀ i : Nat, (hi : i < 7) →
      ((8 : BitVec 8).ule (EpsilonOneRootCore.retainedDegree bits i) &&
        EpsilonOneRootCore.rootEquationAt bits i) = true := by
    intro i hi
    rw [Bool.and_eq_true]
    constructor
    · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [retainedDegree_toNat G C hG hPB p h z i hi]
      exact hMin _
    · exact rootEquationAt_coreBits_true G C hG hPB hNoSeymour
        hRootDegree p h z i hi
  have hAll : allSeven (fun i ↦
      (8 : BitVec 8).ule (EpsilonOneRootCore.retainedDegree bits i) &&
        EpsilonOneRootCore.rootEquationAt bits i) = true := by
    have h0 := hPer 0 (by omega)
    have h1 := hPer 1 (by omega)
    have h2 := hPer 2 (by omega)
    have h3 := hPer 3 (by omega)
    have h4 := hPer 4 (by omega)
    have h5 := hPer 5 (by omega)
    have h6 := hPer 6 (by omega)
    simp only [allSeven, Bool.and_eq_true] at h0 h1 h2 h3 h4 h5 h6 ⊢
    exact ⟨⟨⟨⟨⟨⟨⟨h0.1, h0.2⟩, ⟨h1.1, h1.2⟩⟩,
      ⟨h2.1, h2.2⟩⟩, ⟨h3.1, h3.2⟩⟩,
      ⟨h4.1, h4.2⟩⟩, ⟨h5.1, h5.2⟩⟩, ⟨h6.1, h6.2⟩⟩
  have hOrdered := orderedP_coreBits_true G C hG hPB p0 h z
  change EpsilonOneRootCore.orderedP bits = true at hOrdered
  have hDegreeBit : EpsilonOneRootCore.totalRetainedDegree bits +
      BitVec.ofNat 8 (missing + alpha + beta) = 59 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, hFiftyNine]
    omega
  change EpsilonOneRootCore.core missing alpha beta bits = true
  simp [EpsilonOneRootCore.core,
    hExternalBit, hPToHBit, hPOutBit, hOrdered, hDegreeBit]
  exact ⟨⟨⟨⟨hOrP, hOrPH⟩, hRoot⟩, hHToPBit⟩, hAll⟩

set_option maxHeartbeats 800000 in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem core_false_of_defects_le_three (missing alpha beta : Nat)
    (hDefects : missing + alpha + beta ≤ 3) (hAlpha : alpha ≤ 1)
    (bits : Encoding) :
    EpsilonOneRootCore.core missing alpha beta bits = false := by
  have hm : missing = 0 ∨ missing = 1 ∨ missing = 2 ∨ missing = 3 := by omega
  rcases hm with rfl | rfl | rfl | rfl
  · have ha : alpha = 0 ∨ alpha = 1 ∨ alpha = 2 ∨ alpha = 3 := by omega
    rcases ha with rfl | rfl | rfl | rfl
    · have hb : beta = 0 ∨ beta = 1 ∨ beta = 2 ∨ beta = 3 := by omega
      rcases hb with rfl | rfl | rfl | rfl
      · exact m0a0b0_unsat bits
      · exact m0a0b1_unsat bits
      · exact m0a0b2_unsat bits
      · exact m0a0b3_unsat bits
    · have hb : beta = 0 ∨ beta = 1 ∨ beta = 2 := by omega
      rcases hb with rfl | rfl | rfl
      · exact m0a1b0_unsat bits
      · exact m0a1b1_unsat bits
      · exact m0a1b2_unsat bits
    · omega
    · omega
  · have ha : alpha = 0 ∨ alpha = 1 ∨ alpha = 2 := by omega
    rcases ha with rfl | rfl | rfl
    · have hb : beta = 0 ∨ beta = 1 ∨ beta = 2 := by omega
      rcases hb with rfl | rfl | rfl
      · exact m1a0b0_unsat bits
      · exact m1a0b1_unsat bits
      · exact m1a0b2_unsat bits
    · have hb : beta = 0 ∨ beta = 1 := by omega
      rcases hb with rfl | rfl
      · exact m1a1b0_unsat bits
      · exact m1a1b1_unsat bits
    · omega
  · have ha : alpha = 0 ∨ alpha = 1 := by omega
    rcases ha with rfl | rfl
    · have hb : beta = 0 ∨ beta = 1 := by omega
      rcases hb with rfl | rfl
      · exact m2a0b0_unsat bits
      · exact m2a0b1_unsat bits
    · have : beta = 0 := by omega
      subst beta
      exact m2a1b0_unsat bits
  · have ha : alpha = 0 := by omega
    have hb : beta = 0 := by omega
    subst alpha
    subst beta
    exact m3a0b0_unsat bits

set_option maxHeartbeats 800000 in
/-- Complete contradiction for the terminal tight epsilon-one row
`(x,z)=(4,2)`, without any full-`P→Z` assumption. -/
theorem tightEpsilonOneXFourImpossible (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hBCard : C.B.card = 7) (hk : C.k = 1)
    (hx : C.x = 4) (hz : C.z = 2) (hEpsilon : epsilonS G C = 1) : False := by
  classical
  have hPCard : C.P.card = 7 := r_eq_seven G C hG hMin hBCard hk
  have hPB := p_eq_B G C hG hMin hBCard hk
  have hHCard : C.H.card = 5 := by
    change C.h = 5
    rw [Digraph.LocalConfiguration.h_eq_k_add_x (G := G) C, hk, hx]
  have hZCard : C.Z.card = 2 := hz
  let p0 : Fin 7 ≃ {v : V // v ∈ C.P} := finsetEquivFin C.P hPCard
  let h : Fin 5 ≃ {v : V // v ∈ C.H} := finsetEquivFin C.H hHCard
  let z : Fin 2 ≃ {v : V // v ∈ C.Z} := finsetEquivFin C.Z hZCard
  let p := rootSortedFinsetEquiv G.outdegree
    (fun v ↦ epsilonAt G v C.s) (directCount G C.H) C.P p0
  let bits := coreBits G (fun q ↦ (p q).1) (fun q ↦ (h q).1)
    (fun q ↦ (z q).1) C.s
  let missing := BSevenKOneTerminal.mDefect G C
  let alpha := BSevenKOneTerminal.alphaDefect G C
  let beta := BSevenKOneTerminal.betaDefect G C
  have hExternal := BSevenKOneTerminal.external_add_mDefect_eq_twentyOne
    G C hG hMin hBCard hk hz hEpsilon
  have hPToH := BSevenKOneTerminal.P_to_H_add_alphaDefect_eq_seventeen
    G C hG hMin hRootDegree hBCard hk hx
  have hPOut := BSevenKOneTerminal.P_internal_add_betaDefect_eq_twentyOne
    G C hG hMin hBCard hk
  have hHToP := BSevenKOneTerminal.eighteen_le_H_to_P
    G C hG hMin hRootDegree hBCard hk hx
  have hExcess := BSevenKOneTerminal.degreeExcessEquation
    G C hG hMin hRootDegree hBCard hk hx hz hEpsilon
  have hDegreeSplit :
      ∑ u ∈ C.P, G.outdegree u =
        56 + ∑ u ∈ C.P, (G.outdegree u - 8) := by
    calc
      _ = ∑ u ∈ C.P, (8 + (G.outdegree u - 8)) := by
        apply Finset.sum_congr rfl
        intro u hu
        have := hMin u
        omega
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [hPCard]
  have hDegreeSum : (∑ u ∈ C.P, G.outdegree u) + missing + alpha + beta = 59 := by
    dsimp [missing, alpha, beta]
    omega
  have hDefects : missing + alpha + beta ≤ 3 := by
    dsimp [missing, alpha, beta]
    omega
  have hAlphaSmall : alpha ≤ 1 := by
    by_contra hAlpha
    have hAlphaLarge : 2 ≤ alpha := by omega
    let D := C.P.filter fun q ↦ G.outdegree q = 8
    let S := D.filter fun q ↦ G.Adj q C.s
    let R := C.P.filter fun q ↦ G.Adj q C.s
    let missingZ := 14 - edgeCount G C.P C.Z
    let missingRoot := 7 - R.card
    have hPZCap : edgeCount G C.P C.Z ≤ 14 := by
      have hCap := edgeCount_le_card_mul_card G C.P C.Z
      rw [hPCard, hZCard] at hCap
      exact hCap
    have hRCardLe : R.card ≤ 7 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hPCard
    have hMissingZAdd : edgeCount G C.P C.Z + missingZ = 14 := by
      dsimp [missingZ]
      omega
    have hMissingRootAdd : R.card + missingRoot = 7 := by
      dsimp [missingRoot]
      omega
    have hRootSum : ∑ q ∈ C.P, epsilonAt G q C.s = R.card := by
      simp [R, epsilonAt]
    have hExternalSplit := edgeCount_externalTargets G C
    have hMissingSplit : missingZ + missingRoot = missing := by
      rw [hRootSum] at hExternalSplit
      omega
    have hDCard := card_le_exact_degree_add_excess
      (V := V) C.P G.outdegree 8 (fun q _hq ↦ hMin q)
    change C.P.card ≤ D.card + ∑ q ∈ C.P, (G.outdegree q - 8) at hDCard
    have hSPartition : S.card + (D.filter fun q ↦ ¬G.Adj q C.s).card =
        D.card := by
      simpa [S] using D.card_filter_add_card_filter_not (fun q ↦ G.Adj q C.s)
    have hNonrootSubset : D.filter (fun q ↦ ¬G.Adj q C.s) ⊆
        C.P.filter (fun q ↦ ¬G.Adj q C.s) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqD, hqRoot⟩
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hqD).1, hqRoot⟩
    have hPPartition : R.card +
        (C.P.filter fun q ↦ ¬G.Adj q C.s).card = 7 := by
      simpa [R, hPCard] using
        C.P.card_filter_add_card_filter_not (fun q ↦ G.Adj q C.s)
    have hNonrootCard : (D.filter fun q ↦ ¬G.Adj q C.s).card ≤
        missingRoot := by
      have := Finset.card_le_card hNonrootSubset
      omega
    have hSCard : 4 + missingZ + alpha + beta ≤ S.card := by
      rw [hPCard] at hDCard
      change (∑ q ∈ C.P, (G.outdegree q - 8)) + missing + alpha + beta = 3
        at hExcess
      omega
    have hSP : S ⊆ C.P := by
      exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hSNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    have hMissingP := card_internalMissingPairs_add_edgeCount G C.P hG
    have hChoose : Nat.choose 7 2 = 21 := by decide
    rw [hPCard, hChoose] at hMissingP
    have hMissingMono := Finset.card_le_card
      (internalMissingPairs_mono G hSP)
    have hMissingS : (internalMissingPairs G S).card ≤ beta := by
      dsimp [beta]
      omega
    obtain ⟨q, hqS, hKing⟩ := exists_rootStatus_king_bound
      G C.P S (directCount G C.Z) (directCount G C.H)
      hSNonempty hSP hG
      (by
        intro u huS
        have huD := (Finset.mem_filter.mp huS).1
        have huExact := (Finset.mem_filter.mp huD).2
        have huP := hSP huS
        have huDegree := pDegree_eq_external_add_H_add_P G C hG hPB u huP
        have huRoot := (Finset.mem_filter.mp huS).2
        simp [epsilonAt, huRoot] at huDegree
        omega)
      (by
        intro u huS
        have huP := hSP huS
        have huRoot := (Finset.mem_filter.mp huS).2
        have huExact := (Finset.mem_filter.mp
          (Finset.mem_filter.mp huS).1).2
        have hSecondLe :
            (internalSecondNeighbors (G := G) S u).card ≤
              qCount G C.P C.H u := by
          apply Finset.card_le_card
          exact (internalSecondNeighbors_mono G hSP u).trans
            (internalSecondNeighbors_subset_secondNeighborsThrough
              G C.P C.H u)
        have hEq := rootNeighborhoodEquation G C hG hPB hNoSeymour
          hRootDegree u huP huRoot
        have hDegreeU := pDegree_eq_external_add_H_add_P
          G C hG hPB u huP
        simp [epsilonAt, huRoot] at hEq hDegreeU
        omega)
    have hRowMissing := row_defect_le_capacity_defect
      G C.P C.Z q (hSP hqS)
    rw [hPCard, hZCard] at hRowMissing
    have hRowZ : 2 - directCount G C.Z q ≤ missingZ := by
      dsimp [missingZ]
      omega
    omega
  have hCore : EpsilonOneRootCore.core missing alpha beta bits = true := by
    exact coreBits_true G C hG hMin hNoSeymour hRootDegree hPB hEpsilon
      p0 h z missing alpha beta hExternal hPToH hPOut hHToP hDegreeSum
  have hFalse := core_false_of_defects_le_three missing alpha beta hDefects
    hAlphaSmall bits
  rw [hFalse] at hCore
  contradiction


end SeymourEight.EpsilonOneRootCoreGraphBridge
