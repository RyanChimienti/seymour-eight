import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.HBridge

set_option linter.style.header false

/-!
# The `Z` rows of the exact-seven four-`Z` certificate

The graph-facing hypotheses state exactly the two incidences suppressed by
the finite encoding: the almost-complete `P → Z` block and the overlap between
the seven external-union labels and `H`.
-/

namespace SeymourEight.FourZExactSevenZBridge

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactGlobalBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem zDegree_coreBits_toNat (C : G.LocalConfiguration)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hZP : ∀ i j : Nat, (hi : i < 4) → (hj : j < 7) →
      (G.Adj (z ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 ↔
        exceptionalZToP missing (coreBits G.Adj (fun k ↦ (p k).1) h a
          (fun k ↦ (z k).1) (fun k ↦ (w k).1)) i j = true))
    (source : Nat) (hs : source < 4) :
    (FourZExactSeven.zDegree missing (coreBits G.Adj (fun j ↦ (p j).1) h a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source).toNat =
      G.outdegree (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  have hZ := zArcOut_toNat G C (fun j ↦ (p j).1) h a z
    (fun j ↦ (w j).1) source hs
  have hW := zWOut_toNat G C (fun j ↦ (p j).1) h a z w source hs
  have hP : (bitCount (exceptionalZToP missing bits source 0)).toNat =
      directCount G C.P (z ⟨source, hs⟩).1 := by
    rw [directCount_eq_sum_fin G C.P p]
    simp only [Fin.sum_univ_succ]
    have h0 := hZP source 0 hs (by omega)
    have h1 := hZP source 1 hs (by omega)
    have h2 := hZP source 2 hs (by omega)
    have h3 := hZP source 3 hs (by omega)
    have h4 := hZP source 4 hs (by omega)
    have h5 := hZP source 5 hs (by omega)
    have h6 := hZP source 6 hs (by omega)
    have hn1 : ¬G.Adj (z ⟨source, hs⟩).1 (p 1).1 := by
      intro ha; have := h1.mp ha; simp [exceptionalZToP] at this
    have hn2 : ¬G.Adj (z ⟨source, hs⟩).1 (p 2).1 := by
      intro ha; have := h2.mp ha; simp [exceptionalZToP] at this
    have hn3 : ¬G.Adj (z ⟨source, hs⟩).1 (p 3).1 := by
      intro ha; have := h3.mp ha; simp [exceptionalZToP] at this
    have hn4 : ¬G.Adj (z ⟨source, hs⟩).1 (p 4).1 := by
      intro ha; have := h4.mp ha; simp [exceptionalZToP] at this
    have hn5 : ¬G.Adj (z ⟨source, hs⟩).1 (p 5).1 := by
      intro ha; have := h5.mp ha; simp [exceptionalZToP] at this
    have hn6 : ¬G.Adj (z ⟨source, hs⟩).1 (p 6).1 := by
      intro ha; have := h6.mp ha; simp [exceptionalZToP] at this
    by_cases hb : exceptionalZToP missing bits source 0 = true
    · have ha0 := h0.mpr hb
      have ha0' : G.Adj (z ⟨source, hs⟩).1 (p 0).1 := by simpa using ha0
      simp [bitCount, hb, ha0', hn1, hn2, hn3, hn4, hn5, hn6]
    · have hn0 : ¬G.Adj (z ⟨source, hs⟩).1 (p 0).1 :=
        fun ha ↦ hb (h0.mp ha)
      have hb0 := Bool.eq_false_of_not_eq_true hb
      simp [bitCount, hb0, hn0, hn1, hn2, hn3, hn4, hn5, hn6]
  have hZLe : directCount G C.Z (z ⟨source, hs⟩).1 ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr z).symm)
  have hWLe : directCount G (FourZExactSevenGraphBridge.zExternalUnion G C)
      (z ⟨source, hs⟩).1 ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr w).symm)
  have hPLe : directCount G C.P (z ⟨source, hs⟩).1 ≤ 1 := by
    rw [← hP]
    cases exceptionalZToP missing bits source 0 <;> decide
  rw [FourZExactSeven.zDegree, BitVec.toNat_add, BitVec.toNat_add, hZ, hW, hP,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact (z_outdegree_eq_retainedCounts G C
    (z ⟨source, hs⟩).1 (z ⟨source, hs⟩).2).symm

theorem secondZFromZ_true_mem (C : G.LocalConfiguration)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 → V) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z}) (w : Fin 7 → V)
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (source target : Nat) (hs : source < 4) (ht : target < 4)
    (hSecond : FourZExactSeven.secondZFromZ missing
      (coreBits G.Adj (fun j ↦ (p j).1) h a (fun j ↦ (z j).1) w)
      source target = true) :
    (z ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h a
    (fun j ↦ (z j).1) w
  simp only [FourZExactSeven.secondZFromZ, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hReach⟩, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (z ⟨target, ht⟩).1 := by
    rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h a
      (fun j ↦ (z j).1) w source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (z ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 4) = ⟨source, hs⟩ := by
      apply z.injective
      exact Subtype.ext hEq
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (z ⟨target, ht⟩).1 := by
    simp only [FourZExactSeven.reachesZFromZ, Bool.or_eq_true] at hReach
    rcases hReach with hViaZ | hViaP
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 4 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h a
          (fun j ↦ (z j).1) w source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (z ⟨target, ht⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h a
          (fun j ↦ (z j).1) w middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨⟨⟨hm, hs0⟩, ht0⟩, hFirstBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (p 0).1 := by
        subst source
        rw [z0ToP0_coreBits G.Adj (fun j ↦ (p j).1) h a
          (fun j ↦ (z j).1) w] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hPZBool : FourZExactSeven.pToZ missing 0 target = true := by
        simp [FourZExactSeven.pToZ, hm, ht0]
      have hSecond' : G.Adj (p 0).1 (z ⟨target, ht⟩).1 :=
        (hPZ 0 target (by omega) ht).mpr hPZBool
      exact ⟨(p 0).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondWFromZ_true_mem (C : G.LocalConfiguration)
    (missing : Nat) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (overlap : OverlapType)
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (source target : Nat) (hs : source < 4) (ht : target < 7)
    (hSecond : FourZExactSeven.secondWFromZ missing overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source target = true) :
    (w ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  simp only [FourZExactSeven.secondWFromZ, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (w ⟨target, ht⟩).1 := by
    rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) source target hs ht]
      at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (w ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (FiveZExactGraphBridge.disjoint_Z_zExternalUnion G C))
      (z ⟨source, hs⟩).2 (hEq ▸ (w ⟨target, ht⟩).2)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (w ⟨target, ht⟩).1 := by
    simp only [FourZExactSeven.reachesWFromZ, Bool.or_eq_true] at hReach
    rcases hReach with hViaZ | hViaP
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 4 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmSource, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) source middle hs hm]
          at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (w ⟨target, ht⟩).1 := by
        rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) middle target hm ht]
          at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨⟨⟨hm, hs0⟩, hFirstBool⟩, hAny⟩
      obtain ⟨hi, hhi, hPath⟩ := (any_eq_true_iff 4 _).mp hAny
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hMatch, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (p 0).1 := by
        subst source
        rw [z0ToP0_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1)] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecondH : G.Adj (p 0).1 (h ⟨hi, hhi⟩).1 := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) 0 hi (by omega) hhi]
          at hSecondBool
        exact of_decide_eq_true hSecondBool
      have hEq := (hWH target hi ht hhi).mp hMatch
      exact ⟨(p 0).1, hFirst, hEq.symm ▸ hSecondH⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondPFromZ_true_mem (C : G.LocalConfiguration)
    (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hZP : ∀ i j : Nat, (hi : i < 4) → (hj : j < 7) →
      (G.Adj (z ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 ↔
        exceptionalZToP missing (coreBits G.Adj (fun k ↦ (p k).1)
          (fun k ↦ (h k).1) a (fun k ↦ (z k).1)
          (fun k ↦ (w k).1)) i j = true))
    (source target : Nat) (hs : source < 4) (ht : target < 7)
    (hSecond : FourZExactSeven.secondPFromZ missing overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source target = true) :
    (p ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  simp only [FourZExactSeven.secondPFromZ, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    have hNotEncoded : exceptionalZToP missing bits source target ≠ true := by
      simpa using hNotArcBool
    exact fun hArc ↦ hNotEncoded ((hZP source target hs ht).mp hArc)
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
      (z ⟨source, hs⟩).2 (hEq ▸ (p ⟨target, ht⟩).2)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [FourZExactSeven.reachesPFromZ, Bool.or_eq_true] at hReach
    rcases hReach with (hViaH | hViaP) | hViaZ
    · obtain ⟨wi, hwi, hAny⟩ := (any_eq_true_iff 7 _).mp hViaH
      obtain ⟨hi, hhi, hPath⟩ := (any_eq_true_iff 4 _).mp hAny
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨⟨hMatch, hFirstBool⟩, hSecondBool⟩
      have hFirstW : G.Adj (z ⟨source, hs⟩).1 (w ⟨wi, hwi⟩).1 := by
        rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) source wi hs hwi]
          at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hEq := (hWH wi hi hwi hhi).mp hMatch
      have hSecond' : G.Adj (h ⟨hi, hhi⟩).1 (p ⟨target, ht⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) hi target hhi ht]
          at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(w ⟨wi, hwi⟩).1, hFirstW, hEq ▸ hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨⟨⟨⟨hm, hs0⟩, _ht0⟩, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (p 0).1 := by
        subst source
        rw [z0ToP0_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1)] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p 0).1 (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) 0 target (by omega) ht]
          at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p 0).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaZ
      rcases hViaZ with ⟨⟨⟨⟨hm, _hs0⟩, ht0⟩, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (z 0).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) source 0 hs (by omega)]
          at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z 0).1 (p ⟨target, ht⟩).1 := by
        subst target
        rw [z0ToP0_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1)] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z 0).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem reachesOutsideHFromZ_true_mem (C : G.LocalConfiguration)
    (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (source target : Nat) (hs : source < 4) (ht : target < 4)
    (hReach : FourZExactSeven.reachesOutsideHFromZ missing overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source target = true) :
    (h ⟨target, ht⟩).1 ∈ G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  simp only [FourZExactSeven.reachesOutsideHFromZ, Bool.and_eq_true,
    decide_eq_true_eq] at hReach
  rcases hReach with ⟨⟨⟨⟨hm, hs0⟩, hNotInW⟩, hFirstBool⟩, hSecondBool⟩
  have hFirst : G.Adj (z ⟨source, hs⟩).1 (p 0).1 := by
    subst source
    rw [z0ToP0_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond : G.Adj (p 0).1 (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) 0 target (by omega) ht]
      at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (h ⟨target, ht⟩).1 := by
    intro hDirect
    have hNotP : (h ⟨target, ht⟩).1 ∉ C.P := by
      intro hP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (h ⟨target, ht⟩).2 hP
    have hNotZ : (h ⟨target, ht⟩).1 ∉ C.Z := by
      intro hZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
        hZ (h ⟨target, ht⟩).2
    have hTargetW : (h ⟨target, ht⟩).1 ∈
        FourZExactSevenGraphBridge.zExternalUnion G C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, by simp [hNotP, hNotZ]⟩
      apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨(z ⟨source, hs⟩).1, (z ⟨source, hs⟩).2, hDirect⟩
    have hNotInW' : hInW overlap target ≠ true := by simpa using hNotInW
    exact hNotInW' ((hHInW target ht).mp hTargetW)
  have hTargetVertexNe : (h ⟨target, ht⟩).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
      (z ⟨source, hs⟩).2 (hEq ▸ (h ⟨target, ht⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p 0).1, hFirst, hSecond⟩, hNotArc, hTargetVertexNe⟩

/-- The four pairwise-disjoint represented target blocks are bounded by the
actual strict second neighborhood of the labelled `Z` source. -/
theorem zSecondCount_coreBits_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hZP : ∀ i j : Nat, (hi : i < 4) → (hj : j < 7) →
      (G.Adj (z ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 ↔
        exceptionalZToP missing (coreBits G.Adj (fun k ↦ (p k).1)
          (fun k ↦ (h k).1) a (fun k ↦ (z k).1)
          (fun k ↦ (w k).1)) i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (source : Nat) (hs : source < 4) :
    (FourZExactSeven.zSecondCount missing overlap
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
        (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  let u := (z ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  let QOutside : V → Prop := fun v ↦
    v ∉ FourZExactSevenGraphBridge.zExternalUnion G C ∧
      v ∈ G.secondOutNeighborFinset u
  have hZBound : (count 4 (secondZFromZ missing bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact secondZFromZ_true_mem G C missing p (fun j ↦ (h j).1) a z
      (fun j ↦ (w j).1) hPZ source j hs j.isLt hBit
  have hWBound : (count 7 (secondWFromZ missing overlap bits source)).toNat ≤
      ((FourZExactSevenGraphBridge.zExternalUnion G C).filter Q).card := by
    apply count_le_filterCard
      (FourZExactSevenGraphBridge.zExternalUnion G C) w _ Q (by omega)
    intro j hBit
    exact secondWFromZ_true_mem G C missing p h a z w overlap hWH
      source j hs j.isLt hBit
  have hPBound : (count 7 (secondPFromZ missing overlap bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPFromZ_true_mem G C missing overlap p h a z w hWH hZP
      source j hs j.isLt hBit
  have hHBound :
      (count 4 (reachesOutsideHFromZ missing overlap bits source)).toNat ≤
        (C.H.filter QOutside).card := by
    apply count_le_filterCard C.H h _ QOutside (by omega)
    intro j hBit
    have hMem := reachesOutsideHFromZ_true_mem G C missing overlap p h a z w
      hHInW source j hs j.isLt hBit
    have hNotWBool : hInW overlap j ≠ true := by
      simp only [bits, FourZExactSeven.reachesOutsideHFromZ,
        Bool.and_eq_true, decide_eq_true_eq] at hBit
      simpa using hBit.1.1.2
    have hNotW : (h j).1 ∉ FourZExactSevenGraphBridge.zExternalUnion G C := by
      intro hjW
      exact hNotWBool ((hHInW j j.isLt).mp hjW)
    exact ⟨hNotW, hMem⟩
  have hZCard : (C.Z.filter Q).card ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr z).symm)
  have hWCard :
      ((FourZExactSevenGraphBridge.zExternalUnion G C).filter Q).card ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr w).symm)
  have hPCard : (C.P.filter Q).card ≤ 7 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr p).symm)
  have hHCard : (C.H.filter QOutside).card ≤ 4 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by simpa using (Fintype.card_congr h).symm)
  have hCountNat : (FourZExactSeven.zSecondCount missing overlap bits source).toNat =
      (count 4 (secondZFromZ missing bits source)).toNat +
        (count 7 (secondWFromZ missing overlap bits source)).toNat +
          (count 7 (secondPFromZ missing overlap bits source)).toNat +
            (count 4
              (reachesOutsideHFromZ missing overlap bits source)).toNat := by
    rw [FourZExactSeven.zSecondCount, BitVec.toNat_add, BitVec.toNat_add,
      BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  let SZ := C.Z.filter Q
  let SW := (FourZExactSevenGraphBridge.zExternalUnion G C).filter Q
  let SP := C.P.filter Q
  let SH := C.H.filter QOutside
  have hZ_W : Disjoint SZ SW := by
    rw [Finset.disjoint_left]
    intro v hvZ hvW
    exact (Finset.disjoint_left.mp
      (FiveZExactGraphBridge.disjoint_Z_zExternalUnion G C))
      (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvW).1
  have hZW_P : Disjoint (SZ ∪ SW) SP := by
    rw [Finset.disjoint_left]
    intro v hvZW hvP
    rcases Finset.mem_union.mp hvZW with hvZ | hvW
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
        (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
    · exact (Finset.disjoint_left.mp
        (FiveZExactGraphBridge.disjoint_P_zExternalUnion G C))
        (Finset.mem_filter.mp hvP).1 (Finset.mem_filter.mp hvW).1
  have hZWP_H : Disjoint (SZ ∪ SW ∪ SP) SH := by
    rw [Finset.disjoint_left]
    intro v hvZWP hvH
    rcases Finset.mem_union.mp hvZWP with hvZW | hvP
    · rcases Finset.mem_union.mp hvZW with hvZ | hvW
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
          (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvH).1
      · exact (Finset.mem_filter.mp hvH).2.1 (Finset.mem_filter.mp hvW).1
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (Finset.mem_filter.mp hvH).1 (Finset.mem_filter.mp hvP).1
  have hUnionSubset : SZ ∪ SW ∪ SP ∪ SH ⊆
      G.secondOutNeighborFinset u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvZWP | hvH
    · rcases Finset.mem_union.mp hvZWP with hvZW | hvP
      · rcases Finset.mem_union.mp hvZW with hvZ | hvW
        · exact (Finset.mem_filter.mp hvZ).2
        · exact (Finset.mem_filter.mp hvW).2
      · exact (Finset.mem_filter.mp hvP).2
    · exact (Finset.mem_filter.mp hvH).2.2
  have hUnionCard : (SZ ∪ SW ∪ SP ∪ SH).card =
      SZ.card + SW.card + SP.card + SH.card := by
    rw [Finset.card_union_of_disjoint hZWP_H,
      Finset.card_union_of_disjoint hZW_P,
      Finset.card_union_of_disjoint hZ_W]
  rw [hCountNat]
  calc
    (count 4 (secondZFromZ missing bits source)).toNat +
          (count 7 (secondWFromZ missing overlap bits source)).toNat +
        (count 7 (secondPFromZ missing overlap bits source)).toNat +
      (count 4 (reachesOutsideHFromZ missing overlap bits source)).toNat ≤
        SZ.card + SW.card + SP.card + SH.card := by
      dsimp only [SZ, SW, SP, SH]
      omega
    _ = (SZ ∪ SW ∪ SP ∪ SH).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card := Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (z ⟨source, hs⟩).1 := rfl

theorem zRow_coreBits_true (C : G.LocalConfiguration)
    (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hZP : ∀ i j : Nat, (hi : i < 4) → (hj : j < 7) →
      (G.Adj (z ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 ↔
        exceptionalZToP missing (coreBits G.Adj (fun k ↦ (p k).1)
          (fun k ↦ (h k).1) a (fun k ↦ (z k).1)
          (fun k ↦ (w k).1)) i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 4) :
    ((8 : BitVec 8).ule
        (zDegree missing (coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
          (fun j ↦ (w j).1)) source) &&
      FourZExactSeven.zNonSeymour missing overlap
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
          (fun j ↦ (z j).1) (fun j ↦ (w j).1)) source) = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) a
    (fun j ↦ (z j).1) (fun j ↦ (w j).1)
  let u := (z ⟨source, hs⟩).1
  have hDegree := zDegree_coreBits_toNat G C missing p (fun j ↦ (h j).1) a
    z w hZP source hs
  have hSecond := zSecondCount_coreBits_toNat_le_secondOutdegree G C missing
    overlap p h a z w hPZ hZP hWH hHInW source hs
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [Bool.and_eq_true]
  constructor
  · simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [hDegree]
    exact hMin u
  · simp only [FourZExactSeven.zNonSeymour, BitVec.ult_eq_decide,
      decide_eq_true_eq]
    rw [hDegree]
    exact hSecond.trans_lt (by simpa [u] using hStrict)

/-- Aggregate exactly matching the `zRows` field of `CompatibleRowData`. -/
theorem zRows_coreBits_true (C : G.LocalConfiguration)
    (missing : Nat) (overlap : OverlapType)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 4 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (z : Fin 4 ≃ {v : V // v ∈ C.Z})
    (w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C})
    (hPZ : ∀ i j : Nat, (hi : i < 7) → (hj : j < 4) →
      (G.Adj (p ⟨i, hi⟩).1 (z ⟨j, hj⟩).1 ↔
        FourZExactSeven.pToZ missing i j = true))
    (hZP : ∀ i j : Nat, (hi : i < 4) → (hj : j < 7) →
      (G.Adj (z ⟨i, hi⟩).1 (p ⟨j, hj⟩).1 ↔
        exceptionalZToP missing (coreBits G.Adj (fun k ↦ (p k).1)
          (fun k ↦ (h k).1) a (fun k ↦ (z k).1)
          (fun k ↦ (w k).1)) i j = true))
    (hWH : ∀ wi hi : Nat, (hwi : wi < 7) → (hhi : hi < 4) →
      (wMatchesH overlap wi hi = true ↔
        (w ⟨wi, hwi⟩).1 = (h ⟨hi, hhi⟩).1))
    (hHInW : ∀ hi : Nat, (hhi : hi < 4) →
      ((h ⟨hi, hhi⟩).1 ∈ FourZExactSevenGraphBridge.zExternalUnion G C ↔
        hInW overlap hi = true))
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) :
    all 4 (fun zi =>
      (8 : BitVec 8).ule (zDegree missing (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) zi) &&
      FourZExactSeven.zNonSeymour missing overlap (coreBits G.Adj
        (fun j ↦ (p j).1) (fun j ↦ (h j).1) a (fun j ↦ (z j).1)
        (fun j ↦ (w j).1)) zi) = true := by
  rw [all_eq_true_iff]
  intro source hs
  exact zRow_coreBits_true G C missing overlap p h a z w hPZ hZP hWH
    hHInW hMin hNoSeymour source hs

end SeymourEight.FourZExactSevenZBridge
