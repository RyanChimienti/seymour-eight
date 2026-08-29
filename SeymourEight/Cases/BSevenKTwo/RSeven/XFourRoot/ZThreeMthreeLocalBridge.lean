import SeymourEight.Cases.BSevenKTwo.RSeven.XFourRoot.ZThreeMtwoAssembly
import SeymourEight.Cases.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmission.TargetedDeletion
import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeMThreeLocal

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeMthreeLocalBridge

open CertificateBridge Shared
open SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge
open SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourLabels
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.RepeatedSharedOmissionBridge
open SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeMThreeLocalCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Labels (C : G.LocalConfiguration) where
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 3 ≃ {v : V // v ∈ (externalTargets G C)}
  a_zero : (a 0).1 = C.a1
  a_h : ∀ i : Fin 6, (a ⟨i + 1, by omega⟩).1 ∈ C.H
  a_aone : ∀ i : Fin 2, (a ⟨i + 1, by omega⟩).1 ∈ C.A1
  a_x : ∀ i : Fin 4, (a ⟨i + 3, by omega⟩).1 ∈ C.X
  a_r : (a 7).1 ∈ C.R

noncomputable def labels (C : G.LocalConfiguration)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hAOneCard : C.A1.card = 2) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 1) (hHCard : C.H.card = 6)
    (hZCard : (externalTargets G C).card = 3) : Labels G C := by
  let p := finsetEquivFin C.P hPCard
  let z := finsetEquivFin (externalTargets G C) hZCard
  let ea := finsetEquivFin C.A1 hAOneCard
  let ex := finsetEquivFin C.X hXCard
  let h := BroadFourLabels.hLabelEquiv G C hHCard ea ex
  let er := finsetEquivFin C.R hRCard
  let a := BroadFourLabels.aLabelEquiv G C hACard h er
  refine ⟨p, a, z, ?_, ?_, ?_, ?_, ?_⟩
  · exact BroadFourLabels.aLabelEquiv_zero G C hACard h er
  · intro i
    rw [BroadFourLabels.aLabelEquiv_h G C hACard h er i]
    exact (h i).2
  · intro i
    rw [BroadFourLabels.aLabelEquiv_h G C hACard h er ⟨i, by omega⟩,
      BroadFourLabels.hLabelEquiv_aOne G C hHCard ea ex i]
    exact (ea i).2
  · intro i
    rw [show (a ⟨i.val + 3, by omega⟩).1 =
        (h ⟨i.val + 2, by omega⟩).1 by
      simpa only [show i.val + 2 + 1 = i.val + 3 by omega] using
        BroadFourLabels.aLabelEquiv_h G C hACard h er
          ⟨i.val + 2, by omega⟩]
    rw [BroadFourLabels.hLabelEquiv_x G C hHCard ea ex i]
    exact (ex i).2
  · rw [BroadFourLabels.aLabelEquiv_r G C hACard h er]
    exact (er 0).2

def pUpperBit (L : Labels G C) : Nat → Bool
  | 0 => decide (G.Adj (L.p 0).1 (L.p 1).1)
  | 1 => decide (G.Adj (L.p 0).1 (L.p 2).1)
  | 2 => decide (G.Adj (L.p 0).1 (L.p 3).1)
  | 3 => decide (G.Adj (L.p 0).1 (L.p 4).1)
  | 4 => decide (G.Adj (L.p 0).1 (L.p 5).1)
  | 5 => decide (G.Adj (L.p 0).1 (L.p 6).1)
  | 6 => decide (G.Adj (L.p 1).1 (L.p 2).1)
  | 7 => decide (G.Adj (L.p 1).1 (L.p 3).1)
  | 8 => decide (G.Adj (L.p 1).1 (L.p 4).1)
  | 9 => decide (G.Adj (L.p 1).1 (L.p 5).1)
  | 10 => decide (G.Adj (L.p 1).1 (L.p 6).1)
  | 11 => decide (G.Adj (L.p 2).1 (L.p 3).1)
  | 12 => decide (G.Adj (L.p 2).1 (L.p 4).1)
  | 13 => decide (G.Adj (L.p 2).1 (L.p 5).1)
  | 14 => decide (G.Adj (L.p 2).1 (L.p 6).1)
  | 15 => decide (G.Adj (L.p 3).1 (L.p 4).1)
  | 16 => decide (G.Adj (L.p 3).1 (L.p 5).1)
  | 17 => decide (G.Adj (L.p 3).1 (L.p 6).1)
  | 18 => decide (G.Adj (L.p 4).1 (L.p 5).1)
  | 19 => decide (G.Adj (L.p 4).1 (L.p 6).1)
  | 20 => decide (G.Adj (L.p 5).1 (L.p 6).1)
  | _ => false

def bitAt (C : G.LocalConfiguration) (L : Labels G C) (n : Nat) : Bool :=
  if hnA : n < 64 then
    decide (G.Adj (L.a ⟨n / 8, by omega⟩).1
      (L.a ⟨n % 8, Nat.mod_lt _ (by omega)⟩).1)
  else if hnP : n < 85 then pUpperBit G L (n - 64)
  else if hnPH : n < 127 then
    let q := n - 85
    decide (G.Adj (L.p ⟨q / 6, by omega⟩).1
      (L.a ⟨q % 6 + 1, by omega⟩).1)
  else if hnPZ : n < 148 then
    let q := n - 127
    decide (G.Adj (L.p ⟨q / 3, by omega⟩).1
      (L.z ⟨q % 3, Nat.mod_lt _ (by omega)⟩).1)
  else if hnRP : n < 155 then
    decide (G.Adj (L.a 7).1 (L.p ⟨n - 148, by omega⟩).1)
  else false

def graphBits (C : G.LocalConfiguration) (L : Labels G C) : Encoding :=
  BitVec.cast (by simp only [List.length_ofFn])
    (BitVec.ofBoolListLE (List.ofFn fun n : Fin 155 => bitAt G C L n))

@[simp] theorem getLsbD_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (n : Nat) (hn : n < 155) :
    (graphBits G C L).getLsbD n = bitAt G C L n := by
  rw [graphBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    ← List.getElem_eq_getD (h := by simpa only [List.length_ofFn] using hn)
      false, List.getElem_ofFn]

private theorem div_index (i j w : Nat) (hj : j < w) :
    (i * w + j) / w = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt hj]

private theorem mod_index (i j w : Nat) (hj : j < w) :
    (i * w + j) % w = j := Nat.mul_add_mod_of_lt hj

@[simp] theorem aArc_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (i j : Nat) (hi : i < 8) (hj : j < 8) :
    aArc (graphBits G C L) i j =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  rw [aArc, getLsbD_graphBits G C L _ (by omega)]
  have hd : (8 * i + j) / 8 = i := by
    simpa [Nat.mul_comm] using div_index i j 8 hj
  have hm : (8 * i + j) % 8 = j := by
    simpa [Nat.mul_comm] using mod_index i j 8 hj
  simp [bitAt, show 8 * i + j < 64 by omega, hd, hm]

@[simp] theorem pToH_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (p h : Nat) (hp : p < 7) (hh : h < 6) :
    pToH (graphBits G C L) p h =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1) := by
  rw [pToH, getLsbD_graphBits G C L _ (by omega)]
  have hd : (6 * p + h) / 6 = p := by
    simpa [Nat.mul_comm] using div_index p h 6 hh
  have hm : (6 * p + h) % 6 = h := by
    simpa [Nat.mul_comm] using mod_index p h 6 hh
  simp [bitAt, show ¬85 + 6 * p + h < 64 by omega,
    show ¬85 + 6 * p + h < 85 by omega,
    show 85 + 6 * p + h < 127 by omega,
    show 85 + 6 * p + h - 85 = 6 * p + h by omega, hd, hm]

@[simp] theorem pToZ_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (p z : Nat) (hp : p < 7) (hz : z < 3) :
    pToZ (graphBits G C L) p z =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  rw [pToZ, getLsbD_graphBits G C L _ (by omega)]
  have hd : (3 * p + z) / 3 = p := by
    simpa [Nat.mul_comm] using div_index p z 3 hz
  have hm : (3 * p + z) % 3 = z := by
    simpa [Nat.mul_comm] using mod_index p z 3 hz
  simp [bitAt, show ¬127 + 3 * p + z < 64 by omega,
    show ¬127 + 3 * p + z < 85 by omega,
    show ¬127 + 3 * p + z < 127 by omega,
    show 127 + 3 * p + z < 148 by omega,
    show 127 + 3 * p + z - 127 = 3 * p + z by omega, hd, hm]

@[simp] theorem rToP_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (p : Nat) (hp : p < 7) :
    rToP (graphBits G C L) p =
      decide (G.Adj (L.a 7).1 (L.p ⟨p, hp⟩).1) := by
  rw [rToP, getLsbD_graphBits G C L _ (by omega)]
  simp [bitAt, show ¬148 + p < 64 by omega,
    show ¬148 + p < 85 by omega, show ¬148 + p < 127 by omega,
    show ¬148 + p < 148 by omega, show 148 + p < 155 by omega]

private theorem upper_bit (C : G.LocalConfiguration) (L : Labels G C)
    (i j : Nat) (hi : i < 7) (hj : j < 7) (hij : i < j) :
    pUpperBit G L (XFourNoRoot.ZThreeMThreeLocalCore.upperIndex i j) =
      decide (G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1) := by
  interval_cases i <;> interval_cases j <;>
    simp_all [XFourNoRoot.ZThreeMThreeLocalCore.upperIndex, pUpperBit]

set_option linter.flexible false in
theorem pArc_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented)
    (hComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    pArc (graphBits G C L) i j =
      decide (G.Adj (L.p ⟨i, hi⟩).1 (L.p ⟨j, hj⟩).1) := by
  unfold pArc
  by_cases heq : i = j
  · subst j
    simp
    exact hG.1 _
  by_cases hij : i < j
  · rw [if_neg heq, if_pos hij, getLsbD_graphBits G C L]
    · have hIndex : 64 + upperIndex i j < 85 := by
        interval_cases i <;> interval_cases j <;> simp_all [upperIndex]
      rw [show bitAt G C L (64 + upperIndex i j) =
          pUpperBit G L (upperIndex i j) by simp [bitAt, hIndex]]
      exact upper_bit G C L i j hi hj hij
    · interval_cases i <;> interval_cases j <;> simp_all [upperIndex]
  · have hji : j < i := by omega
    rw [if_neg heq, if_neg hij, getLsbD_graphBits G C L]
    · have hIndex : 64 + upperIndex j i < 85 := by
        interval_cases i <;> interval_cases j <;> simp_all [upperIndex]
      rw [show bitAt G C L (64 + upperIndex j i) =
          pUpperBit G L (upperIndex j i) by simp [bitAt, hIndex],
        upper_bit G C L j i hj hi hji]
      rcases hComplete ⟨i, hi⟩ ⟨j, hj⟩ (by exact Fin.ne_of_val_ne heq) with h | h
      · simp [h, hG.2 h]
      · simp [h, hG.2 h]
    · interval_cases i <;> interval_cases j <;> simp_all [upperIndex]

def retainedVertexSet (C : G.LocalConfiguration) : Finset V := C.A ∪ C.P ∪ (externalTargets G C)

def labelledVertex (L : Labels G C) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 15 then (L.p ⟨n - 8, by omega⟩).1
  else if hnZ : n < 18 then (L.z ⟨n - 15, by omega⟩).1
  else (L.z 0).1

noncomputable def retainedLabelEquiv (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) :
    Fin 18 ≃ {v : V // v ∈ retainedVertexSet G C} := by
  let f : Fin 18 → {v : V // v ∈ retainedVertexSet G C} := fun i =>
    if hiA : i.val < 8 then
      ⟨(L.a ⟨i.val, hiA⟩).1,
        Finset.mem_union_left (externalTargets G C) (Finset.mem_union_left C.P (L.a _).2)⟩
    else if hiP : i.val < 15 then
      ⟨(L.p ⟨i.val - 8, by omega⟩).1,
        Finset.mem_union_left (externalTargets G C) (Finset.mem_union_right C.A (L.p _).2)⟩
    else ⟨(L.z ⟨i.val - 15, by omega⟩).1,
      Finset.mem_union_right (C.A ∪ C.P) (L.z _).2⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rintro ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvAP | hvZ
    · rcases Finset.mem_union.mp hvAP with hvA | hvP
      · obtain ⟨i, hi⟩ := L.a.surjective ⟨v, hvA⟩
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f] using congrArg Subtype.val hi
      · obtain ⟨i, hi⟩ := L.p.surjective ⟨v, hvP⟩
        refine ⟨⟨i.val + 8, by omega⟩, ?_⟩
        apply Subtype.ext
        simpa [f, show ¬i.val + 8 < 8 by omega,
          show i.val + 8 < 15 by omega] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := L.z.surjective ⟨v, hvZ⟩
      refine ⟨⟨i.val + 15, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [f, show ¬i.val + 15 < 8 by omega,
        show ¬i.val + 15 < 15 by omega] using congrArg Subtype.val hi
  · have hAP : Disjoint C.A C.P := by
      rw [Finset.disjoint_left]
      intro v hvA hvP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
    have hAPZ : Disjoint (C.A ∪ C.P) (externalTargets G C) := by
      rw [Finset.disjoint_left]
      intro v hvAP hvE
      rcases Finset.mem_union.mp hvE with hvZ | hvRoot
      · apply (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
        rcases Finset.mem_union.mp hvAP with hvA | hvP
        · exact Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hvA)
        · exact Finset.mem_union_right ({C.s} ∪ C.A)
            (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
      · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
        · have hvs : v = C.s := by simpa [rootSecondFinset, hReach] using hvRoot
          subst v
          rcases Finset.mem_union.mp hvAP with hvA | hvP
          · exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 hvA
          · exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
        · simp [rootSecondFinset, hReach] at hvRoot
    rw [show Fintype.card {v : V // v ∈ retainedVertexSet G C} =
        (retainedVertexSet G C).card by simp,
      retainedVertexSet, Finset.card_union_of_disjoint hAPZ,
      Finset.card_union_of_disjoint hAP]
    have ha : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
    have hp : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
    have hz : (externalTargets G C).card = 3 := by simpa using (Fintype.card_congr L.z).symm
    simp [ha, hp, hz]

@[simp] theorem retainedLabelEquiv_val (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (i : Fin 18) :
    (retainedLabelEquiv G C L hG i).1 = labelledVertex G L i.val := by
  by_cases hiA : i.val < 8
  · simp [retainedLabelEquiv, labelledVertex, hiA]
  by_cases hiP : i.val < 15
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP]
  · simp [retainedLabelEquiv, labelledVertex, hiA, hiP, i.isLt]

theorem coreArc_graphBits (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (source target : Nat) (hs : source < 15) (ht : target < 18) :
    coreArc (graphBits G C L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  have hA0P : ∀ i : Fin 7, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i ↦ hG.2 (hA0P i)
  have hPR : ∀ i : Fin 7, ¬G.Adj (L.p i).1 (L.a 7).1 :=
    fun i ↦ XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
      G C _ _ (L.p i).2 L.a_r
  unfold coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA, aArc_graphBits G C L source target hsA htA]
      simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP]
        have hti : target - 8 < 7 := by omega
        simp only [aToP]
        by_cases hs0 : source = 0
        · subst source
          simp [hA0P, labelledVertex, htA, htP]
        by_cases hs7 : source < 7
        · have hsh : source - 1 < 6 := by omega
          rw [if_neg hs0, if_pos hs7, hToP,
            pToH_graphBits G C L (target - 8) (source - 1) hti hsh]
          have haeq : (L.a ⟨source - 1 + 1, by omega⟩).1 =
              (L.a ⟨source, hsA⟩).1 := by
            have hiEq : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
                ⟨source, hsA⟩ := by
              apply Fin.ext
              simp
              omega
            rw [hiEq]
          rw [haeq]
          rcases hPHComplete ⟨target - 8, hti⟩ ⟨source - 1, hsh⟩ with hp | hh
          · have hn := hG.2 hp
            rw [haeq] at hp hn
            simp [hp, hn, labelledVertex, hsA, htA, htP]
          · have hn := hG.2 hh
            rw [haeq] at hh hn
            simp [hh, hn, labelledVertex, hsA, htA, htP]
        · have hsEq : source = 7 := by omega
          subst source
          rw [if_neg (by omega : ¬7 = 0), if_neg (by omega : ¬7 < 7),
            rToP_graphBits G C L (target - 8) hti]
          simp [labelledVertex, htA, htP]
      · simp [htP, ht, labelledVertex, hsA, htA,
          A_not_adj_external G C hG
            (L.a ⟨source, hsA⟩).1 (L.z ⟨target - 15, by omega⟩).1
            (L.a _).2 (L.z _).2]
  · have hsP : source < 15 := hs
    rw [if_neg hsA, if_pos hsP]
    by_cases htA : target < 8
    · rw [if_pos htA]
      simp only [pToA]
      by_cases htH : 0 < target ∧ target < 7
      · rw [if_pos (by simpa [Bool.and_eq_true] using htH),
          pToH_graphBits G C L (source - 8) (target - 1) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, show target - 1 + 1 = target by omega]
      · rw [if_neg (by simpa [Bool.and_eq_true] using htH)]
        have htCase : target = 0 ∨ target = 7 := by omega
        rcases htCase with rfl | rfl
        · simp [labelledVertex, hsA, hsP, hP0]
        · simp [labelledVertex, hsA, hsP, hPR]
    · rw [if_neg htA]
      by_cases htP : target < 15
      · rw [if_pos htP,
          pArc_graphBits G C L hG hPComplete (source - 8) (target - 8)
            (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, htP]
      · rw [if_neg htP, if_pos ht,
          pToZ_graphBits G C L (source - 8) (target - 15) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, htP, ht]

private theorem toNat_count (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat =
      ∑ i ∈ Finset.range n, (bitCount (f i)).toNat := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      have hn' : n < 256 := by omega
      have hLe : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) ≤ n := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            cases f i <;> decide
          _ = n := by simp
      rw [count, BitVec.toNat_add, ih hn', Finset.sum_range_succ]
      cases hf : f n
      · simpa [bitCount, hf] using Nat.mod_eq_of_lt
          (by omega : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) < 256)
      · simpa [bitCount, hf] using Nat.mod_eq_of_lt
          (by omega : (∑ i ∈ Finset.range n, (bitCount (f i)).toNat) + 1 < 256)

private theorem toNat_count_eq_fin_sum (n : Nat) (f : Nat → Bool)
    (hn : n < 256) :
    (count n f).toNat = ∑ i : Fin n, if f i then 1 else 0 := by
  rw [toNat_count n f hn,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ (bitCount (f i)).toNat) n]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [bitCount]

private theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · simpa [show i = n by omega] using hn
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

private theorem any_eq_true_iff (n : Nat) (f : Nat → Bool) :
    any n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [any]
  | succ n ih =>
      simp only [any, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hf⟩ | hf)
        · exact ⟨i, by omega, hf⟩
        · exact ⟨n, by omega, hf⟩
      · rintro ⟨i, hi, hf⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, hf⟩
        · exact Or.inr (show i = n by omega ▸ hf)

omit [Fintype V] [DecidableEq V] in
private theorem count_le_filterCard {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, b j = true → Q (e j).1) :
    (count n b).toNat ≤ (S.filter Q).card := by
  classical
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hb : b j = true
  · simp [hb, hGood j hb]
  · have hf := Bool.eq_false_of_not_eq_true hb
    simp [hf]

theorem directCount_graphBits_toNat (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (source : Nat) (hs : source < 15) :
    (directCount (graphBits G C L) source).toNat =
      G.outdegree (labelledVertex G L source) := by
  rw [XFourNoRoot.ZThreeMThreeLocalCore.directCount,
    toNat_count_eq_fin_sum 18 _ (by omega)]
  have hCount : (∑ j : Fin 18, if coreArc (graphBits G C L) source j then 1 else 0) =
      Shared.directCount G (retainedVertexSet G C)
        (labelledVertex G L source) := by
    symm
    apply directCount_eq_sum_bool G (retainedVertexSet G C)
      (retainedLabelEquiv G C L hG)
    intro j
    rw [retainedLabelEquiv_val G C L hG]
    rw [coreArc_graphBits G C L hG hPComplete hPHComplete source j hs j.isLt]
    simp
  rw [hCount]
  apply (outdegree_eq_directCount_of_captured G _ _ ?_).symm
  by_cases hsA : source < 8
  · have heq : labelledVertex G L source = (L.a ⟨source, hsA⟩).1 := by
      simp [labelledVertex, hsA]
    rw [heq]
    simpa [retainedVertexSet,
      SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.retainedVertexSet] using
      SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.A_outgoingCaptured_retained
        G C hG hPB _ (L.a _).2
  · have heq : labelledVertex G L source = (L.p ⟨source - 8, by omega⟩).1 := by
      simp [labelledVertex, hsA, hs]
    rw [heq]
    simpa [retainedVertexSet,
      SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.retainedVertexSet] using
      SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.P_outgoingCaptured_retained
        G C hG hPB _ (L.p _).2

theorem strictSecondLocal_true_mem (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (source target : Nat) (hs : source < 15) (ht : target < 18)
    (hSecond : strictSecondLocal (graphBits G C L) source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 15 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_graphBits G C L hG hPComplete hPHComplete source middle hs
      (by omega)] at hFirst
  rw [coreArc_graphBits G C L hG hPComplete hPHComplete middle target hm ht]
    at hLast
  rw [coreArc_graphBits G C L hG hPComplete hPHComplete source target hs ht]
    at hNotArc
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 18) = ⟨source, by omega⟩ := by
      apply (retainedLabelEquiv G C L hG).injective
      apply Subtype.ext
      simpa [retainedLabelEquiv_val G C L hG] using heq
    exact hne (Fin.ext_iff.mp hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

theorem localSecondCount_le_graph (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (source : Nat) (hs : source < 15) :
    (localSecondCount (graphBits G C L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  have hFiltered := count_le_filterCard (V := V) (retainedVertexSet G C)
    (retainedLabelEquiv G C L hG) (strictSecondLocal (graphBits G C L) source)
    (fun v ↦ v ∈ G.secondOutNeighborFinset (labelledVertex G L source))
    (by omega) (by
      intro j hj
      rw [retainedLabelEquiv_val G C L hG]
      exact strictSecondLocal_true_mem G C L hG hPComplete hPHComplete
        source j hs j.isLt hj)
  unfold localSecondCount Digraph.secondOutdegree
  exact hFiltered.trans (Finset.card_le_card (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2))

theorem nonSeymour_true (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (source : Nat) (hs : source < 15) :
    (localSecondCount (graphBits G C L) source).ult
      (directCount (graphBits G C L) source) = true := by
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  rw [directCount_graphBits_toNat G C L hG hPB hPComplete hPHComplete
    source hs]
  exact (localSecondCount_le_graph G C L hG hPComplete hPHComplete source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h ↦ hNoSeymour ⟨labelledVertex G L source, h⟩))

omit [Fintype V] [DecidableEq V] in
private theorem filterCard_le_count {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (b : Nat → Bool)
    (Q : V → Prop) [DecidablePred Q] (hn : n < 256)
    (hGood : ∀ j : Fin n, Q (e j).1 → b j = true) :
    (S.filter Q).card ≤ (count n b).toNat := by
  classical
  rw [toNat_count_eq_fin_sum n b hn, filterCard_eq_sum_fin S e Q]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hQ : Q (e j).1
  · simp [hQ, hGood j hQ]
  · simp [hQ]

theorem deletionReached_good (C : G.LocalConfiguration) (L : Labels G C)
    (hG : G.IsOriented)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (x : Nat) (hx : x < 4) (source : V)
    (hSourceLabel : labelledVertex G L (3 + x) = source)
    (S : Finset V) (hS : S = (G.outNeighborFinset source).erase C.a1)
    (target : Fin 18) (htNotS : labelledVertex G L target ∉ S)
    (htNeSource : labelledVertex G L target ≠ source)
    (middle : V) (middleIndex : Nat) (hmIndex : middleIndex < 15)
    (hmLabel : labelledVertex G L middleIndex = middle)
    (_hmS : middle ∈ S) (hmt : G.Adj middle (labelledVertex G L target))
    (hRetMiddle : retainedAfterAOneDeletion (graphBits G C L) x middleIndex = true) :
    (decide (target.1 ≠ 3 + x) &&
      !retainedAfterAOneDeletion (graphBits G C L) x target.1 &&
      any 15 (fun middle ↦
        retainedAfterAOneDeletion (graphBits G C L) x middle &&
          coreArc (graphBits G C L) middle target)) = true := by
  have htIndexNe : target.1 ≠ 3 + x := by
    intro heq
    apply htNeSource
    simpa [heq] using hSourceLabel
  have htNotRet : retainedAfterAOneDeletion (graphBits G C L) x target = false := by
    apply Bool.eq_false_of_not_eq_true
    intro htRet
    simp only [retainedAfterAOneDeletion, Bool.and_eq_true,
      decide_eq_true_eq] at htRet
    rcases htRet with ⟨htNeZero, htArc⟩
    rw [coreArc_graphBits G C L hG hPComplete hPHComplete
      (3 + x) target (by omega) target.isLt] at htArc
    have hGraphArc : G.Adj source (labelledVertex G L target) := by
      rw [← hSourceLabel]
      exact of_decide_eq_true htArc
    have htNeA1 : labelledVertex G L target ≠ C.a1 := by
      intro heq
      have hzero : labelledVertex G L 0 = C.a1 := by
        simpa [labelledVertex] using L.a_zero
      have hFin : target = (0 : Fin 18) := by
        apply (retainedLabelEquiv G C L hG).injective
        apply Subtype.ext
        simpa [retainedLabelEquiv_val G C L hG, hzero] using heq
      exact htNeZero (Fin.ext_iff.mp hFin)
    apply htNotS
    rw [hS]
    exact Finset.mem_erase.mpr
      ⟨htNeA1, (Digraph.mem_outNeighborFinset (G := G)).mpr hGraphArc⟩
  have hArc : coreArc (graphBits G C L) middleIndex target = true := by
    rw [coreArc_graphBits G C L hG hPComplete hPHComplete
      middleIndex target hmIndex target.isLt, hmLabel]
    exact decide_eq_true hmt
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    exact ⟨decide_eq_true htIndexNe, by simp [htNotRet]⟩
  · rw [any_eq_true_iff]
    exact ⟨middleIndex, hmIndex, by simp [hRetMiddle, hArc]⟩

theorem xDeletionExpands_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (x : Nat) (hx : x < 4) (hDegree : G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8)
    (hPivotArc : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1) :
    xDeletionExpands (graphBits G C L) x = true := by
  let source := (L.a ⟨3 + x, by omega⟩).1
  let S := (G.outNeighborFinset source).erase C.a1
  let E := G.outNeighborFinsetOf S \ (S ∪ {source})
  have hExpansion : 7 ≤ E.card := by
    simpa [source, S, E] using Digraph.oneArcDeletionExpansion G hBound hG
      hNoSeymour hDegree hPivotArc
  have hSourceA : source ∈ C.A := (L.a ⟨3 + x, by omega⟩).2
  have hESubset : E ⊆ retainedVertexSet G C := by
    intro v hvE
    rcases Finset.mem_sdiff.mp hvE with ⟨hvReach, _⟩
    obtain ⟨middle, hmS, hmv⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hvReach
    have hmOut : middle ∈ G.outNeighborFinset source := Finset.mem_of_mem_erase hmS
    rcases Finset.mem_union.mp
        (XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
          G C hG source hSourceA hmOut)
      with hmA | hmB
    · simpa [retainedVertexSet,
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.retainedVertexSet] using
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.A_outgoingCaptured_retained
          G C hG hPB middle hmA
            ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
    · have hmP : middle ∈ C.P := by simpa [hPB] using hmB
      simpa [retainedVertexSet,
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.retainedVertexSet] using
        SeymourEight.BSevenKTwo.RSeven.XFourRoot.BroadFourBridge.P_outgoingCaptured_retained
          G C hG hPB middle hmP
            ((Digraph.mem_outNeighborFinset (G := G)).mpr hmv)
  have hCount : E.card ≤ (count 18 (fun target ↦
      decide (target ≠ 3 + x) &&
        !retainedAfterAOneDeletion (graphBits G C L) x target &&
        any 15 (fun middle ↦
          retainedAfterAOneDeletion (graphBits G C L) x middle &&
            coreArc (graphBits G C L) middle target))).toNat := by
    have hFilter := filterCard_le_count (V := V) (retainedVertexSet G C)
      (retainedLabelEquiv G C L hG) (fun target ↦
        decide (target ≠ 3 + x) &&
          !retainedAfterAOneDeletion (graphBits G C L) x target &&
          any 15 (fun middle ↦
            retainedAfterAOneDeletion (graphBits G C L) x middle &&
              coreArc (graphBits G C L) middle target))
      (fun v ↦ v ∈ E) (by omega) (by
        intro target htE
        rw [retainedLabelEquiv_val G C L hG] at htE
        rcases Finset.mem_sdiff.mp htE with ⟨htReach, htOutside⟩
        obtain ⟨middle, hmS, hmt⟩ :=
          (Digraph.mem_outNeighborFinsetOf (G := G)).mp htReach
        have hmOut : middle ∈ G.outNeighborFinset source :=
          Finset.mem_of_mem_erase hmS
        rcases Finset.mem_union.mp
            (XFourNoRoot.RepeatedSharedOmissionBridge.A_outgoingCaptured
              G C hG source hSourceA hmOut)
          with hmA | hmB
        · obtain ⟨i, hi⟩ := L.a.surjective ⟨middle, hmA⟩
          let mi := i.val
          have hmi : mi < 15 := by omega
          have hmLabel : labelledVertex G L mi = middle := by
            simp [mi, labelledVertex, i.isLt, congrArg Subtype.val hi]
          have hmNeA1 : middle ≠ C.a1 := (Finset.mem_erase.mp hmS).1
          have hmNeZero : mi ≠ 0 := by
            intro hz
            apply hmNeA1
            rw [← hmLabel, hz]
            simpa [labelledVertex] using L.a_zero
          have hRet : retainedAfterAOneDeletion (graphBits G C L) x mi = true := by
            unfold retainedAfterAOneDeletion
            rw [coreArc_graphBits G C L hG hPComplete hPHComplete
              (3 + x) mi (by omega) (by omega), hmLabel]
            have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
            simpa [hmNeZero, source, labelledVertex,
              show 3 + x < 8 by omega] using hadj
          refine deletionReached_good G C L hG hPComplete hPHComplete x hx source
            (by simp [source, labelledVertex, show 3 + x < 8 by omega]) S rfl
            target ?_ ?_ middle mi hmi hmLabel hmS hmt hRet
          · intro ht; exact htOutside (Finset.mem_union_left {source} ht)
          · intro ht; exact htOutside
              (Finset.mem_union_right S (Finset.mem_singleton.mpr ht))
        · have hmP : middle ∈ C.P := by simpa [hPB] using hmB
          obtain ⟨i, hi⟩ := L.p.surjective ⟨middle, hmP⟩
          let mi := 8 + i.val
          have hmi : mi < 15 := by omega
          have hmLabel : labelledVertex G L mi = middle := by
            simp [mi, labelledVertex, show ¬8 + i.val < 8 by omega,
              show 8 + i.val < 15 by omega, congrArg Subtype.val hi]
          have hRet : retainedAfterAOneDeletion (graphBits G C L) x mi = true := by
            unfold retainedAfterAOneDeletion
            rw [coreArc_graphBits G C L hG hPComplete hPHComplete
              (3 + x) mi (by omega) (by omega), hmLabel]
            have hadj := (Digraph.mem_outNeighborFinset (G := G)).mp hmOut
            simpa [mi, source, labelledVertex,
              show 3 + x < 8 by omega] using hadj
          refine deletionReached_good G C L hG hPComplete hPHComplete x hx source
            (by simp [source, labelledVertex, show 3 + x < 8 by omega]) S rfl
            target ?_ ?_ middle mi hmi hmLabel hmS hmt hRet
          · intro ht; exact htOutside (Finset.mem_union_left {source} ht)
          · intro ht; exact htOutside
              (Finset.mem_union_right S (Finset.mem_singleton.mpr ht)))
    have hFilterEq : ((retainedVertexSet G C).filter fun v ↦ v ∈ E).card =
        E.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv ↦ hv.2, fun hv ↦ ⟨hESubset hv, hv⟩⟩
    rw [hFilterEq] at hFilter
    exact hFilter
  unfold xDeletionExpands
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  exact hExpansion.trans hCount

private theorem sum_fin21_eq_blocks (f : Fin 21 → Nat) :
    (∑ q, f q) = ∑ i : Fin 7, ∑ j : Fin 3,
      f ⟨i * 3 + j, by omega⟩ := by
  rw [← (finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp [finProdFinEquiv]
  omega

theorem core_true
    (hBound : Digraph.LimitedSeymourConjectureOn V 7) (C : G.LocalConfiguration)
    (L : Labels G C) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (hPComplete : ∀ i j : Fin 7, i ≠ j →
      G.Adj (L.p i).1 (L.p j).1 ∨ G.Adj (L.p j).1 (L.p i).1)
    (hPHComplete : ∀ i : Fin 7, ∀ j : Fin 6,
      G.Adj (L.p i).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.p i).1)
    (hHDegree : ∀ j : Fin 6, G.outdegree (L.a ⟨j + 1, by omega⟩).1 = 8)
    (hPDegree : ∀ i : Fin 7, G.outdegree (L.p i).1 = 8)
    (hHTournament : ∀ i j : Fin 6, i ≠ j →
      G.Adj (L.a ⟨i + 1, by omega⟩).1 (L.a ⟨j + 1, by omega⟩).1 ∨
      G.Adj (L.a ⟨j + 1, by omega⟩).1 (L.a ⟨i + 1, by omega⟩).1)
    (hXDomPivot : ∀ x : Fin 4, G.Adj (L.a ⟨x + 3, by omega⟩).1 C.a1)
    (hXDomR : ∀ x : Fin 4, G.Adj (L.a ⟨x + 3, by omega⟩).1 (L.a 7).1)
    (hPZ : edgeCount G C.P (externalTargets G C) = 18) :
    core (graphBits G C L) = true := by
  let bits := graphBits G C L
  have hOrientedA : orientedA bits = true := by
    rw [orientedA, all_eq_true_iff]
    intro i hi
    rw [Bool.and_eq_true, aArc_graphBits G C L i i hi hi]
    constructor
    · simpa using hG.1 (L.a ⟨i, hi⟩).1
    · rw [all_eq_true_iff]
      intro j hj
      rw [aArc_graphBits G C L i j hi hj,
        aArc_graphBits G C L j i hj hi]
      by_cases hij : i = j
      · simp [hij]
      · by_cases h : G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1
        · simp [h, hG.2 h]
        · simp [h]
  have hFixedA : fixedA bits = true := by
    have ha0 : (L.a ⟨0, by omega⟩).1 = C.a1 := by simpa using L.a_zero
    have h01 : aArc bits 0 1 = true := by
      rw [aArc_graphBits G C L 0 1 (by omega) (by omega), ha0]
      simpa using (Finset.mem_filter.mp (L.a_aone 0)).2
    have h02 : aArc bits 0 2 = true := by
      rw [aArc_graphBits G C L 0 2 (by omega) (by omega), ha0]
      simpa using (Finset.mem_filter.mp (L.a_aone 1)).2
    have hTail : all 5 (fun i ↦ !aArc bits 0 (3 + i)) = true := by
      rw [all_eq_true_iff]
      intro i hi
      rw [aArc_graphBits G C L 0 (3 + i) (by omega) (by omega), ha0]
      by_cases hi4 : i < 4
      · have hxMem := L.a_x ⟨i, hi4⟩
        have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
          intro ha
          have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
            Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)) hA1
              (by simpa [Nat.add_comm] using hxMem)
        simp [hn]
      · have hiEq : i = 4 := by omega
        subst i
        have hn : ¬G.Adj C.a1 (L.a 7).1 := by
          intro ha
          have hA1 : (L.a 7).1 ∈ C.A1 := Finset.mem_filter.mpr ⟨(L.a 7).2, ha⟩
          exact (Finset.mem_sdiff.mp L.a_r).2
            (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
        simp [hn]
    have h17 : (!aArc bits 1 7) = true := by
      rw [aArc_graphBits G C L 1 7 (by omega) (by omega)]
      have hn := XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R G C _ _
        (L.a_aone 0) L.a_r
      simpa using hn
    have h27 : (!aArc bits 2 7) = true := by
      rw [aArc_graphBits G C L 2 7 (by omega) (by omega)]
      have hn := XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R G C _ _
        (L.a_aone 1) L.a_r
      simpa using hn
    have hX : all 4 (fun x ↦ aArc bits (3 + x) 0 &&
        aArc bits (3 + x) 7) = true := by
      rw [all_eq_true_iff]
      intro x hx
      rw [aArc_graphBits G C L (3 + x) 0 (by omega) (by omega),
        aArc_graphBits G C L (3 + x) 7 (by omega) (by omega), ha0]
      have hp : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1 := by
        simpa [Nat.add_comm] using hXDomPivot ⟨x, hx⟩
      have hr : G.Adj (L.a ⟨3 + x, by omega⟩).1 (L.a 7).1 := by
        simpa [Nat.add_comm] using hXDomR ⟨x, hx⟩
      simp [hp, hr]
    simp only [fixedA, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨h01, h02⟩, hTail⟩, h17⟩, h27⟩, hX⟩
  have hHTourBool : hTournament bits = true := by
    rw [hTournament, all_eq_true_iff]
    intro i hi
    rw [all_eq_true_iff]
    intro j hj
    rw [aArc_graphBits G C L (1 + i) (1 + j) (by omega) (by omega),
      aArc_graphBits G C L (1 + j) (1 + i) (by omega) (by omega)]
    by_cases hij : i = j
    · simp [hij]
    · rcases hHTournament ⟨i, hi⟩ ⟨j, hj⟩ (by exact Fin.ne_of_val_ne hij)
          with h | h
      · have h' : G.Adj (L.a ⟨1 + i, by omega⟩).1
            (L.a ⟨1 + j, by omega⟩).1 := by simpa [Nat.add_comm] using h
        simp [h', hG.2 h', hij]
      · have h' : G.Adj (L.a ⟨1 + j, by omega⟩).1
            (L.a ⟨1 + i, by omega⟩).1 := by simpa [Nat.add_comm] using h
        simp [h', hG.2 h', hij]
  have hHDegreeBool : hDegreeEight bits = true := by
    rw [hDegreeEight, all_eq_true_iff]
    intro j hj
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [directCount_graphBits_toNat G C L hG hPB hPComplete hPHComplete
      (1 + j) (by omega)]
    have hv : labelledVertex G L (1 + j) =
        (L.a ⟨j + 1, by omega⟩).1 := by
      unfold labelledVertex
      rw [dif_pos (by omega : 1 + j < 8)]
      congr 2
      apply Fin.ext
      simp
      omega
    rw [hv, hHDegree ⟨j, hj⟩]
    decide
  have hPDegreeBool : pDegreeEight bits = true := by
    rw [pDegreeEight, all_eq_true_iff]
    intro p hp
    rw [XFourNoRoot.ZThreeMThreeLocalCore.pDegree_eq_direct bits p hp, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [directCount_graphBits_toNat G C L hG hPB hPComplete hPHComplete
      (8 + p) (by omega)]
    have hv : labelledVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
      simp [labelledVertex, show ¬8 + p < 8 by omega,
        show 8 + p < 15 by omega]
    rw [hv, hPDegree ⟨p, hp⟩]
    decide
  have hTotalPZ : (totalPToZ bits == 18) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [totalPToZ, toNat_count_eq_fin_sum 21 _ (by omega),
      sum_fin21_eq_blocks]
    have hEach (i : Fin 7) :
        (∑ j : Fin 3, if pToZ bits i j then 1 else 0) =
          Shared.directCount G (externalTargets G C) (L.p i).1 := by
      symm
      apply directCount_eq_sum_bool G (externalTargets G C) L.z
      intro j
      rw [pToZ_graphBits G C L i j i.isLt j.isLt]
      simp
    have hFlat :
        (∑ i : Fin 7, ∑ j : Fin 3,
          if pToZ bits ((⟨i.val * 3 + j.val, by omega⟩ : Fin 21).val / 3)
            ((⟨i.val * 3 + j.val, by omega⟩ : Fin 21).val % 3) then 1 else 0) =
        ∑ i : Fin 7, ∑ j : Fin 3, if pToZ bits i j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hDiv : (i.val * 3 + j.val) / 3 = i.val := by omega
      have hMod : (i.val * 3 + j.val) % 3 = j.val := by
        simp
      simp only [hDiv, hMod]
    rw [hFlat]
    simp_rw [hEach]
    rw [← edgeCount_eq_sum_fin G C.P (externalTargets G C) L.p, hPZ]
    decide
  have hANon : aNonSeymour bits = true := by
    rw [aNonSeymour, all_eq_true_iff]
    intro a ha
    exact nonSeymour_true G C L hG hPB hNoSeymour hPComplete hPHComplete
      a (by omega)
  have hPNon : pNonSeymour bits = true := by
    rw [pNonSeymour, all_eq_true_iff]
    intro p hp
    exact nonSeymour_true G C L hG hPB hNoSeymour hPComplete hPHComplete
      (8 + p) (by omega)
  have hDeletion : all 4 (xDeletionExpands bits) = true := by
    rw [all_eq_true_iff]
    intro x hx
    have hd : G.outdegree (L.a ⟨3 + x, by omega⟩).1 = 8 := by
      simpa only [show (x + 2) + 1 = 3 + x by omega] using
        hHDegree ⟨x + 2, by omega⟩
    have hp : G.Adj (L.a ⟨3 + x, by omega⟩).1 C.a1 := by
      simpa only [show x + 3 = 3 + x by omega] using hXDomPivot ⟨x, hx⟩
    exact xDeletionExpands_true G hBound C L hG hPB hNoSeymour
      hPComplete hPHComplete x hx hd hp
  have hTotalEq : totalPToZ bits = 18 := beq_iff_eq.mp hTotalPZ
  change core bits = true
  simp [core, hOrientedA, hFixedA, hHTourBool, hHDegreeBool,
    hPDegreeBool, hTotalEq, hANon, hPNon, hDeletion]

end SeymourEight.BSevenKTwo.RSeven.XFourRoot.ZThreeMthreeLocalBridge
