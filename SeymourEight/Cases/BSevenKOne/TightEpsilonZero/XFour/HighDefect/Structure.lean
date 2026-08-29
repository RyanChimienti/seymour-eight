import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Deletion

set_option linter.style.header false

namespace SeymourEight.ThreeZHighDefectGraphBridge

open ThreeZHighDefect ThreeZHighDefectBridge FiveZExactRisk
  FiveZExactGraphBridge FiveZExactGlobalBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem aOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 → V) (h : Fin 5 → V) (r : Fin 2 → V) (z : Fin 3 → V)
    (a : Fin 8 ≃ {v : V // v ∈ C.A}) (source : Nat) (hs : source < 8) :
    (ThreeZHighDefect.aOut
      (coreBits G.Adj p h r z (fun i ↦ (a i).1)) source).toNat =
      directCount G C.A (a ⟨source, hs⟩).1 := by
  classical
  rw [ThreeZHighDefect.aOut,
    FiveZExactGraphBridge.toNat_count_eq_fin_sum 8 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.A a
  intro j
  rw [aArc_coreBits G.Adj p h r z (fun i ↦ (a i).1)
    source j hs j.isLt]
  simp

theorem aPOut_coreBits_toNat (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 → V) (r : Fin 2 → V) (z : Fin 3 → V)
    (a : Fin 8 → V)
    (hA0P : ∀ i : Fin 7, G.Adj (a 0) (p i).1)
    (hAH : ∀ i : Fin 5, a ⟨i + 1, by omega⟩ = h i)
    (hAR : ∀ i : Fin 2, a ⟨i + 6, by omega⟩ = r i)
    (source : Nat) (hs : source < 8) :
    (aPOut (coreBits G.Adj (fun i ↦ (p i).1) h r z a) source).toNat =
      directCount G C.P (a ⟨source, hs⟩) := by
  rw [aPOut, FiveZExactGraphBridge.toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  by_cases hs0 : source = 0
  · subst source
    simp [aToP, hA0P]
  by_cases hs6 : source < 6
  · have hi : source - 1 < 5 := by omega
    rw [aToP, if_neg hs0, if_pos hs6,
      hToP_coreBits G.Adj (fun i ↦ (p i).1) h r z a
        (source - 1) j hi j.isLt]
    have heq := hAH ⟨source - 1, hi⟩
    have heq' : a ⟨source, hs⟩ = h ⟨source - 1, hi⟩ := by
      simpa [show source - 1 + 1 = source by omega] using heq
    rw [heq']
    simp
  · have hi : source - 6 < 2 := by omega
    rw [aToP, if_neg hs0, if_neg hs6,
      rToP_coreBits G.Adj (fun i ↦ (p i).1) h r z a
        (source - 6) j hi j.isLt]
    have heq := hAR ⟨source - 6, hi⟩
    have heq' : a ⟨source, hs⟩ = r ⟨source - 6, hi⟩ := by
      simpa [show source - 6 + 6 = source by omega] using heq
    rw [heq']
    simp

set_option linter.flexible false in
theorem fixedStructure_coreBits_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPivot : IsMinimalPivot G C)
    (hMin : ∀ v, 8 ≤ G.outdegree v) (_hRootDegree : G.outdegree C.s = 8)
    (hPB : C.P = C.B) (hk : C.k = 1) (_hx : C.x = 4)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (h : Fin 5 ≃ {v : V // v ∈ C.H})
    (r : Fin 2 ≃ {v : V // v ∈ C.R})
    (z : Fin 3 ≃ {v : V // v ∈ C.Z})
    (a : Fin 8 ≃ {v : V // v ∈ C.A})
    (hA0 : (a 0).1 = C.a1)
    (hAH : ∀ i : Fin 5, (a ⟨i + 1, by omega⟩).1 = (h i).1)
    (hH0A1 : (h 0).1 ∈ C.A1)
    (hH1X : (h 1).1 ∈ C.X) (hH2X : (h 2).1 ∈ C.X)
    (hH3X : (h 3).1 ∈ C.X) (hH4X : (h 4).1 ∈ C.X)
    (hAR : ∀ i : Fin 2, (a ⟨i + 6, by omega⟩).1 = (r i).1) :
    fixedStructure (coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)) = true := by
  let bits := coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
    (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
  have hA0P : ∀ i : Fin 7, G.Adj (a 0).1 (p i).1 := by
    intro i
    rw [hA0]
    exact (Finset.mem_filter.mp (p i).2).2
  have hP0 : ∀ i : Fin 7, ¬G.Adj (p i).1 (a 0).1 := by
    intro i
    exact hG.2 (hA0P i)
  have hPR : ∀ i : Fin 7, ∀ j : Fin 2, ¬G.Adj (p i).1 (r j).1 := by
    intro i j
    exact P_not_adj_R G C (p i).1 (r j).1 (p i).2 (r j).2
  have hAZ : ∀ i : Fin 8, ∀ j : Fin 3, ¬G.Adj (a i).1 (z j).1 := by
    intro i j
    exact A_not_adj_Z G C hG (a i).1 (z j).1 (a i).2 (z j).2
  have hOrient := orientedSquare_coreBits_true G hG
    (fun i ↦ (p i).1) (fun i ↦ (h i).1) (fun i ↦ (r i).1)
    (fun i ↦ (z i).1) (fun i ↦ (a i).1)
    hA0P hP0 hAH hAR hPR hAZ
  have hA01Graph : G.Adj (a 0).1 (a 1).1 := by
    have : (a 1).1 = (h 0).1 := by simpa using hAH 0
    rw [hA0, this]
    exact (Finset.mem_filter.mp hH0A1).2
  have hA01 : aArc bits 0 1 = true := by
    rw [aArc_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      0 1 (by omega) (by omega)]
    simpa using hA01Graph
  have hA0Tail : all 6 (fun q => !aArc bits 0 (q + 2)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [aArc_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      0 (q + 2) (by omega) (by omega)]
    have hNot : ¬G.Adj (a 0).1 (a ⟨q + 2, by omega⟩).1 := by
      rw [hA0]
      intro hadj
      have hm : (a ⟨q + 2, by omega⟩).1 ∈ C.A1 :=
        Finset.mem_filter.mpr ⟨(a ⟨q + 2, by omega⟩).2, hadj⟩
      have hEq : (a ⟨q + 2, by omega⟩).1 = (h 0).1 := by
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hk
        have ht : (a ⟨q + 2, by omega⟩).1 = u := by simpa [hu] using hm
        have h0 : (h 0).1 = u := by simpa [hu] using hH0A1
        exact ht.trans h0.symm
      have hIndex : (⟨q + 2, by omega⟩ : Fin 8) = 1 := by
        apply a.injective
        apply Subtype.ext
        exact hEq.trans (by simpa using (hAH 0).symm)
      have hVal : q + 2 = 1 := congrArg Fin.val hIndex
      omega
    simpa using hNot
  have hA1R : all 2 (fun q => !aArc bits 1 (q + 6)) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [aArc_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      1 (q + 6) (by omega) (by omega)]
    have hSource : (a 1).1 = (h 0).1 := by simpa using hAH 0
    have hTarget : (a ⟨q + 6, by omega⟩).1 = (r ⟨q, hq⟩).1 := by
      simpa using hAR ⟨q, hq⟩
    simp [hSource, hTarget]
    intro hadj
    have hrX : (r ⟨q, hq⟩).1 ∈ C.X := by
      apply Finset.mem_inter.mpr
      exact ⟨(Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        ⟨(h 0).1, Finset.mem_union_left C.P hH0A1, hadj⟩,
        Finset.mem_sdiff.mpr ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C
          (r ⟨q, hq⟩).2, by
          intro hm
          exact (Finset.mem_sdiff.mp (r ⟨q, hq⟩).2).2 (by
            rcases Finset.mem_union.mp hm with hm | hm
            · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hm)
            · exact Finset.mem_union_right (C.A1 ∪ C.X) hm)⟩⟩
    exact (Finset.mem_sdiff.mp (r ⟨q, hq⟩).2).2
      (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hrX))
  have hXReach (target : Nat)
      (ht : target = 2 ∨ target = 3 ∨ target = 4 ∨ target = 5)
      (hTargetX : (a ⟨target, by omega⟩).1 ∈ C.X) :
      (aArc bits 1 target || any 7 (fun i => pToH bits i (target - 1))) = true := by
    rcases Finset.mem_inter.mp hTargetX with ⟨hReached, _⟩
    obtain ⟨u, huParts, huTarget⟩ :=
      (Digraph.mem_outNeighborFinsetOf (G := G)).mp hReached
    rcases Finset.mem_union.mp huParts with huA1 | huP
    · have huEq : u = (h 0).1 := by
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hk
        have := show u = v from by simpa [hv] using huA1
        exact this.trans (show (h 0).1 = v from by simpa [hv] using hH0A1).symm
      rw [Bool.or_eq_true]
      left
      rw [aArc_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
        (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
        1 target (by omega) (by omega)]
      have hs : (a 1).1 = (h 0).1 := by simpa using hAH 0
      simpa [hs, huEq] using huTarget
    · obtain ⟨i, hi⟩ := p.surjective ⟨u, huP⟩
      rw [Bool.or_eq_true]
      right
      rw [any_eq_true_iff]
      refine ⟨i, i.isLt, ?_⟩
      rw [pToH_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
        (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
        i (target - 1) i.isLt (by omega)]
      have htH : (a ⟨target, by omega⟩).1 = (h ⟨target - 1, by omega⟩).1 := by
        simpa [show target - 1 + 1 = target by omega] using hAH ⟨target - 1, by omega⟩
      simpa [congrArg Subtype.val hi, htH] using huTarget
  have hX1 : (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) = true := by
    apply hXReach 2 (Or.inl rfl)
    simpa [show (a 2).1 = (h 1).1 by simpa using hAH 1] using hH1X
  have hX2 : (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) = true := by
    apply hXReach 3 (Or.inr (Or.inl rfl))
    simpa [show (a 3).1 = (h 2).1 by simpa using hAH 2] using hH2X
  have hX3 : (aArc bits 1 4 || any 7 (fun i => pToH bits i 3)) = true := by
    apply hXReach 4 (Or.inr (Or.inr (Or.inl rfl)))
    simpa [show (a 4).1 = (h 3).1 by simpa using hAH 3] using hH3X
  have hX4 : (aArc bits 1 5 || any 7 (fun i => pToH bits i 4)) = true := by
    apply hXReach 5 (Or.inr (Or.inr (Or.inr rfl)))
    simpa [show (a 5).1 = (h 4).1 by simpa using hAH 4] using hH4X
  have hAOut : all 8 (fun ai => (1 : BitVec 8).ule (aOut bits ai)) = true := by
    rw [all_eq_true_iff]
    intro ai hai
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [aOut_coreBits_toNat G C (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      (fun i ↦ (r i).1) (fun i ↦ (z i).1) a ai hai]
    have := (hPivot (a ⟨ai, hai⟩).1 (a ⟨ai, hai⟩).2).1
    simpa [hk, directCount, CertificateBridge.internalFirstNeighbors] using this
  have hTie : all 7 (fun q =>
      !(aOut bits (q + 1) = 1) || (7 : BitVec 8).ule (aPOut bits (q + 1))) = true := by
    rw [all_eq_true_iff]
    intro q hq
    rw [Bool.or_eq_true]
    by_cases hInternal : aOut bits (q + 1) = 1
    · right
      simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
      rw [aPOut_coreBits_toNat G C p (fun i ↦ (h i).1) (fun i ↦ (r i).1)
        (fun i ↦ (z i).1) (fun i ↦ (a i).1) hA0P hAH hAR (q + 1) (by omega)]
      have hOut := aOut_coreBits_toNat G C (fun i ↦ (p i).1)
        (fun i ↦ (h i).1) (fun i ↦ (r i).1) (fun i ↦ (z i).1)
        a (q + 1) (by omega)
      rw [hInternal] at hOut
      have hPivotTie := (hPivot (a ⟨q + 1, by omega⟩).1
        (a ⟨q + 1, by omega⟩).2).2
      have hR : C.r = 7 := by
        change C.P.card = 7
        simpa using (Fintype.card_congr p).symm
      have hpt := hPivotTie (by
        rw [hk]
        simpa [directCount, CertificateBridge.internalFirstNeighbors] using hOut.symm)
      rw [hPB]
      simpa [hR, directCount, CertificateBridge.internalFirstNeighbors] using hpt
    · left
      simpa using hInternal
  have hDegrees : all 15 (fun u => (8 : BitVec 8).ule (coreOutdegree bits u)) = true := by
    rw [all_eq_true_iff]
    intro u hu
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    rw [coreOutdegree_coreBits_toNat G C hG hPB hEpsilon p
      (fun i ↦ (h i).1) (fun i ↦ (r i).1) z a hA0P hP0 hAH hAR hPR hAZ u hu]
    exact hMin _
  have hZReach : all 3 (fun zi => any 7 (fun i => pToZ bits i zi)) = true := by
    rw [all_eq_true_iff]
    intro zi hzi
    obtain ⟨pv, hpv, hpz⟩ := every_Z_reached_from_P G C (z ⟨zi, hzi⟩).1
      (z ⟨zi, hzi⟩).2
    obtain ⟨pi, hpi⟩ := p.surjective ⟨pv, hpv⟩
    rw [any_eq_true_iff]
    refine ⟨pi, pi.isLt, ?_⟩
    rw [pToZ_coreBits G.Adj (fun i ↦ (p i).1) (fun i ↦ (h i).1)
      (fun i ↦ (r i).1) (fun i ↦ (z i).1) (fun i ↦ (a i).1)
      pi zi pi.isLt hzi]
    simpa [congrArg Subtype.val hpi] using hpz
  rw [fixedStructure]
  simpa only [Bool.and_eq_true] using
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hOrient, hA01⟩, hA0Tail⟩, hA1R⟩, hX1⟩, hX2⟩,
      hX3⟩, hX4⟩, hAOut⟩, hTie⟩, hDegrees⟩, hZReach⟩

end SeymourEight.ThreeZHighDefectGraphBridge
