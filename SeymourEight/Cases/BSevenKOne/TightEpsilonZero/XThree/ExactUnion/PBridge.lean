import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.ZBridge

set_option linter.style.header false

/-! Graph soundness of the seven `P` rows in the exact-seven core. -/

namespace SeymourEight.FourZExactSevenPBridge

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactGlobalBridge
  FiveZExactPBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem secondPViaPOrH_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 7)
    (hSecond : FourZExactSeven.secondPViaPOrH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w)
      source target = true) :
    (p ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [FourZExactSeven.secondPViaPOrH, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hNotArcBool⟩, hReach⟩
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠ (p ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 7) = ⟨source, hs⟩ := by
      apply p.injective
      exact Subtype.ext hEq
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V, G.Adj (p ⟨source, hs⟩).1 middle ∧
      G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [FourZExactSeven.reachedPViaPOrH, Bool.or_eq_true] at hReach
    rcases hReach with hViaP | hViaH
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
        source middle hs hm] at hFirstBool
      rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
        middle target hm ht] at hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, of_decide_eq_true hFirstBool,
        of_decide_eq_true hSecondBool⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 4 _).mp hViaH
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
        source middle hs hm] at hFirstBool
      rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
        middle target hm ht] at hSecondBool
      exact ⟨(h ⟨middle, hm⟩).1, of_decide_eq_true hFirstBool,
        of_decide_eq_true hSecondBool⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondW_true_mem (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (source target : Nat) (hs : source < 7) (ht : target < 7)
    (hSecond : FourZExactSeven.secondW missing overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source target = true) :
    (w ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  simp only [FourZExactSeven.secondW, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotDirectBool⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 4 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 :=
    (hPZ source middle hs hm).mpr hFirstBool
  have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (w ⟨target, ht⟩).1 := by
    rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) middle target hm ht]
      at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotDirect : directWFromP overlap bits source target ≠ true := by
    simpa using hNotDirectBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (w ⟨target, ht⟩).1 := by
    intro hDirect
    have hvCaptured := outgoingCaptured_of_p_eq_B G C hG hPB
      (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2
      ((Digraph.mem_outNeighborFinset (G := G)).mpr hDirect)
    simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
    rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
    · exact (Finset.disjoint_left.mp
        (FiveZExactGraphBridge.disjoint_Z_zExternalUnion G C))
        hvZ (w ⟨target, ht⟩).2
    · have hDirectS : G.Adj (p ⟨source, hs⟩).1 C.s := by
        simpa [hvs] using hDirect
      exact no_P_to_s_of_epsilonS_zero G C hEpsilon _
        (p ⟨source, hs⟩).2 hDirectS
    · let hj : Fin 4 := h.symm ⟨(w ⟨target, ht⟩).1, hvH⟩
      have hjEq : (h hj).1 = (w ⟨target, ht⟩).1 := by
        simp [hj]
      have hjW : (h hj).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C := by
        rw [hjEq]
        exact (w ⟨target, ht⟩).2
      have hIn := (hHInW hj hj.isLt).mp hjW
      obtain ⟨wi, hwi, hMatch⟩ := (any_eq_true_iff 7 _).mp hIn
      have hEqWH := (hWH wi hj hwi hj.isLt).mp hMatch
      have hEqW : (w ⟨wi, hwi⟩).1 = (w ⟨target, ht⟩).1 := by
        simpa [hj] using hEqWH
      have hIndex : (⟨wi, hwi⟩ : Fin 7) = ⟨target, ht⟩ := by
        apply w.injective
        exact Subtype.ext hEqW
      have hwiEq : wi = target := Fin.ext_iff.mp hIndex
      have hPToH : pToH bits source hj = true := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) source hj hs hj.isLt]
        exact decide_eq_true (by simpa [hj] using hDirect)
      apply hNotDirect
      rw [directWFromP, any_eq_true_iff]
      refine ⟨hj, hj.isLt, ?_⟩
      rw [Bool.and_eq_true]
      exact ⟨by simpa [hwiEq] using hMatch, hPToH⟩
    · exact (Finset.disjoint_left.mp
        (FiveZExactGraphBridge.disjoint_P_zExternalUnion G C))
        hvP (w ⟨target, ht⟩).2
  have hTargetVertexNe : (w ⟨target, ht⟩).1 ≠ (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (FiveZExactGraphBridge.disjoint_P_zExternalUnion G C))
      (p ⟨source, hs⟩).2 (hEq ▸ (w ⟨target, ht⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem secondOutsideH_true_mem (C : G.LocalConfiguration)
    (overlap : OverlapType) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (z : Fin 4 → V) (w : Fin 7 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 4)
    (hSecond : FourZExactSeven.secondOutsideH overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w)
      source target = true) :
    (h ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [FourZExactSeven.secondOutsideH, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨⟨_hOutside, hReach⟩, hNotArcBool⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
    source middle hs hm] at hFirstBool
  rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
    middle target hm ht] at hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a z w
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (h ⟨target, ht⟩).1 ≠ (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
      (h ⟨target, ht⟩).2 (hEq ▸ (p ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨middle, hm⟩).1, of_decide_eq_true hFirstBool,
    of_decide_eq_true hSecondBool⟩, hNotArc, hTargetVertexNe⟩

theorem missingZSecond_true_mem (C : G.LocalConfiguration)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (w : Fin 7 → V)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (source : Nat) (hs : source < 7)
    (hSecond : missingZSecond missing
      (coreBits G.Adj (fun j ↦ (p j).1) h a (fun j ↦ (z j).1) w)
      source = true) :
    (z 0).1 ∈ G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [missingZSecond, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hm, hs0⟩, hAny⟩
  obtain ⟨q, hq, hArcBool⟩ := (any_eq_true_iff 3 _).mp hAny
  have hFirstBool : FourZExactSeven.pToZ missing source (q + 1) = true := by
    simp [FourZExactSeven.pToZ, hm, hs0]
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (z ⟨q + 1, by omega⟩).1 :=
    (hPZ source (q + 1) hs (by omega)).mpr hFirstBool
  have hSecond' : G.Adj (z ⟨q + 1, by omega⟩).1 (z 0).1 := by
    rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h a (fun j ↦ (z j).1) w
      (q + 1) 0 (by omega) (by omega)] at hArcBool
    exact of_decide_eq_true hArcBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (z 0).1 := by
    intro hArc
    have := (hPZ source 0 hs (by omega)).mp hArc
    simp [FourZExactSeven.pToZ, hm, hs0] at this
  have hTargetVertexNe : (z 0).1 ≠ (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
      (z 0).2 (hEq ▸ (p ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(z ⟨q + 1, by omega⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem pSecondCount_coreBits_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (source : Nat) (hs : source < 7) :
    (pSecondCount missing overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source).toNat ≤
      G.secondOutdegree (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  let u := (p ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  let QOutside : V → Prop := fun v ↦
    v ∉ FourZExactSevenGraphBridge.zExternalUnion G C ∧
      v ∈ G.secondOutNeighborFinset u
  have hPBound : (count 7 (secondPViaPOrH bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPViaPOrH_true_mem G C p h a (fun j ↦ (z j).1)
      (fun j ↦ (w j).1) source j hs j.isLt hBit
  have hWBound : (count 7 (secondW missing overlap bits source)).toNat ≤
      ((FourZExactSevenGraphBridge.zExternalUnion G C).filter Q).card := by
    apply count_le_filterCard
      (FourZExactSevenGraphBridge.zExternalUnion G C) w _ Q (by omega)
    intro j hBit
    exact secondW_true_mem G C hG hPB hEpsilon missing overlap p h a z w
      hPZ hWH hHInW source j hs j.isLt hBit
  have hHBound :
      (count 4 (secondOutsideH overlap bits source)).toNat ≤
        (C.H.filter QOutside).card := by
    apply count_le_filterCard C.H h _ QOutside (by omega)
    intro j hBit
    have hMem := secondOutsideH_true_mem G C overlap p h a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) source j hs j.isLt hBit
    have hNotWBool : hInW overlap j ≠ true := by
      simp only [bits, FourZExactSeven.secondOutsideH, Bool.and_eq_true]
        at hBit
      simpa using hBit.1.1
    have hNotW : (h j).1 ∉ FourZExactSevenGraphBridge.zExternalUnion G C := by
      intro hjW
      exact hNotWBool ((hHInW j j.isLt).mp hjW)
    exact ⟨hNotW, hMem⟩
  have hZBound : (bitCount (missingZSecond missing bits source)).toNat ≤
      (C.Z.filter Q).card := by
    cases hb : missingZSecond missing bits source
    · simp [bitCount]
    · have hMem := missingZSecond_true_mem G C missing p (fun j ↦ (h j).1)
        a z (fun j ↦ (w j).1) hPZ source hs hb
      have hzFilter : (z 0).1 ∈ C.Z.filter Q :=
        Finset.mem_filter.mpr ⟨(z 0).2, hMem⟩
      have : 1 ≤ (C.Z.filter Q).card :=
        Finset.one_le_card.mpr ⟨(z 0).1, hzFilter⟩
      simpa [bitCount] using this
  have hPCard : (C.P.filter Q).card ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  have hWCard :
      ((FourZExactSevenGraphBridge.zExternalUnion G C).filter Q).card ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr w).symm)
  have hHCard : (C.H.filter QOutside).card ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr h).symm)
  have hZCard : (C.Z.filter Q).card ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr z).symm)
  have hCountNat : (pSecondCount missing overlap bits source).toNat =
      (count 7 (secondPViaPOrH bits source)).toNat +
        (count 7 (secondW missing overlap bits source)).toNat +
          (count 4 (secondOutsideH overlap bits source)).toNat +
            (bitCount (missingZSecond missing bits source)).toNat := by
    rw [pSecondCount, FourZExactSeven.secondPCount,
      FourZExactSeven.secondWCount, FourZExactSeven.secondOutsideHCount,
      BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  let SP := C.P.filter Q
  let SW := (FourZExactSevenGraphBridge.zExternalUnion G C).filter Q
  let SH := C.H.filter QOutside
  let SZ := C.Z.filter Q
  have hP_W : Disjoint SP SW := by
    rw [Finset.disjoint_left]
    intro v hvP hvW
    exact (Finset.disjoint_left.mp
      (FiveZExactGraphBridge.disjoint_P_zExternalUnion G C))
      (Finset.mem_filter.mp hvP).1 (Finset.mem_filter.mp hvW).1
  have hPW_H : Disjoint (SP ∪ SW) SH := by
    rw [Finset.disjoint_left]
    intro v hvPW hvH
    rcases Finset.mem_union.mp hvPW with hvP | hvW
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 (Finset.mem_filter.mp hvP).1
    · exact (Finset.mem_filter.mp hvH).2.1 (Finset.mem_filter.mp hvW).1
  have hPWH_Z : Disjoint (SP ∪ SW ∪ SH) SZ := by
    rw [Finset.disjoint_left]
    intro v hvPWH hvZ
    rcases Finset.mem_union.mp hvPWH with hvPW | hvH
    · rcases Finset.mem_union.mp hvPW with hvP | hvW
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
          (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
      · exact (Finset.disjoint_left.mp
          (FiveZExactGraphBridge.disjoint_Z_zExternalUnion G C))
          (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvW).1
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
        (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvH).1
  have hUnionSubset : SP ∪ SW ∪ SH ∪ SZ ⊆
      G.secondOutNeighborFinset u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvPWH | hvZ
    · rcases Finset.mem_union.mp hvPWH with hvPW | hvH
      · rcases Finset.mem_union.mp hvPW with hvP | hvW
        · exact (Finset.mem_filter.mp hvP).2
        · exact (Finset.mem_filter.mp hvW).2
      · exact (Finset.mem_filter.mp hvH).2.2
    · exact (Finset.mem_filter.mp hvZ).2
  have hUnionCard : (SP ∪ SW ∪ SH ∪ SZ).card =
      SP.card + SW.card + SH.card + SZ.card := by
    rw [Finset.card_union_of_disjoint hPWH_Z,
      Finset.card_union_of_disjoint hPW_H,
      Finset.card_union_of_disjoint hP_W]
  rw [hCountNat]
  calc
    (count 7 (secondPViaPOrH bits source)).toNat +
          (count 7 (secondW missing overlap bits source)).toNat +
        (count 4 (secondOutsideH overlap bits source)).toNat +
      (bitCount (missingZSecond missing bits source)).toNat ≤
        SP.card + SW.card + SH.card + SZ.card := by
      dsimp only [SP, SW, SH, SZ]
      omega
    _ = (SP ∪ SW ∪ SH ∪ SZ).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card := Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (p ⟨source, hs⟩).1 := rfl

theorem p_outdegree_le_fourteen (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (hZCard : C.Z.card = 4) (hHCard : C.H.card = 4)
    (hPCard : C.P.card = 7) (u : V) (hu : u ∈ C.P) :
    G.outdegree u ≤ 14 := by
  have hPInternal : directCount G C.P u ≤ 6 := by
    unfold directCount CertificateBridge.internalFirstNeighbors
    calc
      (C.P.filter (G.Adj u)).card ≤ (C.P.erase u).card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvP, huv⟩
        exact Finset.mem_erase.mpr ⟨fun hvu ↦ hG.1 u (hvu ▸ huv), hvP⟩
      _ = 6 := by rw [Finset.card_erase_of_mem hu, hPCard]
  have hZLe : directCount G C.Z u ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hZCard
  have hHLe : directCount G C.H u ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHCard
  rw [P_outdegree_eq_Z_add_H_add_P G C hG hPB hEpsilon u hu]
  omega

theorem pRow_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZCount : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 7) :
    ((8 : BitVec 8).ule (pDegree missing (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) source) &&
      (pDegree missing (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) source).ule 14 &&
      pNonSeymour missing overlap (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) source) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  let u := (p ⟨source, hs⟩).1
  have hDegree := pDegree_toNat G C hG hPB hEpsilon missing p h a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) hPZCount source hs
  have hSecond := pSecondCount_coreBits_toNat_le_secondOutdegree G C hG hPB
    hEpsilon missing overlap p h a z w hPZ hWH hHInW source hs
  have hZCard : C.Z.card = 4 := by simpa using (Fintype.card_congr z).symm
  have hHCard : C.H.card = 4 := by simpa using (Fintype.card_congr h).symm
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr p).symm
  have hUpper := p_outdegree_le_fourteen G C hG hPB hEpsilon
    hZCard hHCard hPCard u (p ⟨source, hs⟩).2
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hMin u
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hUpper
  · simp only [FourZExactSeven.pNonSeymour, BitVec.ult_eq_decide,
      decide_eq_true_eq]
    rw [hDegree]
    exact hSecond.trans_lt (by simpa [u] using hStrict)

/-- Aggregate exactly matching `CompatibleRowData.pRows`. -/
theorem pRows_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0) (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZCount : ∀ i : Nat, (hi : i < 7) →
      directCount G C.Z (p ⟨i, hi⟩).1 =
        if missing = 1 ∧ i = 0 then 3 else 4)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 7 (fun pi =>
      (8 : BitVec 8).ule (pDegree missing (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) pi) &&
      (pDegree missing (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) pi).ule 14 &&
      pNonSeymour missing overlap (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) pi) = true := by
  rw [all_eq_true_iff]
  intro source hs
  exact pRow_coreBits_true G C hG hPB hEpsilon missing overlap p h a z w
    hPZCount hPZ hWH hHInW hMin hNoSeymour source hs

end SeymourEight.FourZExactSevenPBridge
