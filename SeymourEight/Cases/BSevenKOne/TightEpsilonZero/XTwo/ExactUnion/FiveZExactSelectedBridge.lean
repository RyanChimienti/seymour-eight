import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactLabels

set_option linter.style.header false

/-!
# Selected-union bridge for all exact five-`Z` overlaps

For a seven-vertex external union, the master certificate retains a
six-vertex subset containing the entire intersection with `H`.  Omitting its
one anonymous vertex can lower a retained `Z` degree by at most one.
-/

namespace SeymourEight.FiveZExactSelectedBridge

open FiveZExactRisk FiveZExactCoreBridge FiveZExactGraphBridge
  FiveZExactGlobalBridge FiveZExactLabels Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem zToSelectedCount_toNat (_C : G.LocalConfiguration) (S : Finset V)
    (p : Fin 7 → V) (z : Fin 5 → V)
    (w : Fin 6 ≃ {v : V // v ∈ S}) (h : Fin 3 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 5) :
    (count 6 (zToW (coreBits G.Adj p h z (fun j ↦ (w j).1) a) source)).toNat =
      directCount G S (z ⟨source, hs⟩) := by
  classical
  rw [toNat_count_eq_fin_sum 6 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G S w
  intro j
  rw [zToW_coreBits G.Adj p h z (fun j ↦ (w j).1) a
    source j hs j.isLt]
  simp

theorem zArcSelectedCount_toNat (C : G.LocalConfiguration) (S : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S}) (h : Fin 3 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 5) :
    (count 5 (zArc (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source)).toNat =
      directCount G C.Z (z ⟨source, hs⟩).1 := by
  rw [toNat_count_eq_fin_sum 5 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.Z z
  intro j
  rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a source j hs j.isLt]
  simp

theorem zToPSelectedCount_toNat (C : G.LocalConfiguration) (S : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S}) (h : Fin 3 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 5) :
    (zPOut (coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).toNat =
      directCount G C.P (z ⟨source, hs⟩).1 := by
  rw [zPOut, toNat_count_eq_fin_sum 7 _ (by omega)]
  symm
  apply directCount_eq_sum_bool G C.P p
  intro j
  rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a source j hs j.isLt]
  simp

theorem zDegree_selected_toNat (C : G.LocalConfiguration) (S : Finset V)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 → V) (a : Fin 8 → V)
    (source : Nat) (hs : source < 5) :
    (zDegree (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
      (fun j ↦ (w j).1) a) source).toNat =
      directCount G C.Z (z ⟨source, hs⟩).1 +
        directCount G S (z ⟨source, hs⟩).1 +
          directCount G C.P (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
    (fun j ↦ (w j).1) a
  have hZ := zArcSelectedCount_toNat G C S p z w h a source hs
  have hW := zToSelectedCount_toNat G C S (fun j ↦ (p j).1)
    (fun j ↦ (z j).1) w h a source hs
  have hP := zToPSelectedCount_toNat G C S p z w h a source hs
  have hZLe : directCount G C.Z (z ⟨source, hs⟩).1 ≤ 5 := by
    calc
      _ ≤ C.Z.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hSLe : directCount G S (z ⟨source, hs⟩).1 ≤ 6 := by
    calc
      _ ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by simpa using (Fintype.card_congr w).symm
  have hPLe : directCount G C.P (z ⟨source, hs⟩).1 ≤ 7 := by
    calc
      _ ≤ C.P.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  rw [zDegree, BitVec.toNat_add, BitVec.toNat_add, hZ, hW, hP,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem directCount_union_le_selected_add_one (C : G.LocalConfiguration)
    (S : Finset V) (hS : S ⊆ zExternalUnion G C) (hSCard : S.card = 6)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7) (u : V) :
    directCount G (zExternalUnion G C) u ≤ directCount G S u + 1 := by
  let W := zExternalUnion G C
  let T := W \ S
  have hWDecomp : W = S ∪ T := by
    ext v
    simp only [T, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hv
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · exact Or.inr ⟨hv, hvS⟩
    · rintro (hvS | ⟨hvW, _⟩)
      · exact hS hvS
      · exact hvW
  have hDisjoint : Disjoint S T := Finset.disjoint_sdiff
  have hTCard : T.card ≤ 1 := by
    have hCard : T.card = W.card - S.card := by
      exact Finset.card_sdiff_of_subset hS
    rcases hWCard with hSix | hSeven
    · simp only [W, hSix, hSCard] at hCard
      omega
    · simp only [W, hSeven, hSCard] at hCard
      omega
  unfold directCount CertificateBridge.internalFirstNeighbors
  change (W.filter (G.Adj u)).card ≤ (S.filter (G.Adj u)).card + 1
  rw [hWDecomp, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hDisjoint)]
  have hFilter : (T.filter (G.Adj u)).card ≤ T.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

theorem zDegree_selected_ge_seven (C : G.LocalConfiguration) (S : Finset V)
    (hS : S ⊆ zExternalUnion G C) (hSCard : S.card = 6)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 → V) (a : Fin 8 → V)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (source : Nat) (hs : source < 5) :
    (7 : BitVec 8).ule
      (zDegree (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) source) = true := by
  have hRetained := zDegree_selected_toNat G C S p z w h a source hs
  have hActual := z_outdegree_eq_retainedCounts G C
    (z ⟨source, hs⟩).1 (z ⟨source, hs⟩).2
  have hUnion := directCount_union_le_selected_add_one G C S hS hSCard
    hWCard (z ⟨source, hs⟩).1
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  change 7 ≤ (zDegree _ source).toNat
  rw [hRetained]
  have := hMin (z ⟨source, hs⟩).1
  omega

theorem selectedWCoverage_coreBits_true (C : G.LocalConfiguration)
    (S : Finset V) (hS : S ⊆ zExternalUnion G C)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 → V) (a : Fin 8 → V) :
    all 6 (fun wi => any 5 fun zi =>
      zToW (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1)
        (fun j ↦ (w j).1) a) zi wi) = true := by
  rw [all_eq_true_iff]
  intro wi hwi
  have hwUnion := (Finset.mem_sdiff.mp (hS (w ⟨wi, hwi⟩).2)).1
  obtain ⟨zv, hz, hAdj⟩ :=
    (Digraph.mem_outNeighborFinsetOf (G := G)).mp hwUnion
  obtain ⟨zi, hzi⟩ := z.surjective ⟨zv, hz⟩
  rw [any_eq_true_iff]
  refine ⟨zi, zi.isLt, ?_⟩
  rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) h
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a zi wi zi.isLt hwi]
  have : (z zi).1 = zv := congrArg Subtype.val hzi
  simpa [this] using hAdj

theorem pDegree_selected_toNat (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V) (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (source : Nat) (hs : source < 7) :
    (pDegree (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a) source).toNat =
      G.outdegree (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) w a
  have hZ : (pZOut bits source).toNat =
      directCount G C.Z (p ⟨source, hs⟩).1 := by
    rw [pZOut, toNat_count_eq_fin_sum 5 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.Z z
    intro j
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a source j hs j.isLt]
    simp
  have hH : (pHOut bits source).toNat =
      directCount G C.H (p ⟨source, hs⟩).1 := by
    rw [pHOut, toNat_count_eq_fin_sum 3 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.H h
    intro j
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a source j hs j.isLt]
    simp
  have hP : (pOut bits source).toNat =
      directCount G C.P (p ⟨source, hs⟩).1 := by
    rw [pOut, toNat_count_eq_fin_sum 7 _ (by omega)]
    symm
    apply directCount_eq_sum_bool G C.P p
    intro j
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a source j hs j.isLt]
    simp
  have hZLe : directCount G C.Z (p ⟨source, hs⟩).1 ≤ 5 := by
    calc
      _ ≤ C.Z.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hHLe : directCount G C.H (p ⟨source, hs⟩).1 ≤ 3 := by
    calc
      _ ≤ C.H.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := by simpa using (Fintype.card_congr h).symm
  have hPLe : directCount G C.P (p ⟨source, hs⟩).1 ≤ 7 := by
    calc
      _ ≤ C.P.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  rw [pDegree, BitVec.toNat_add, BitVec.toNat_add, hZ, hH, hP,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact (FiveZExactPBridge.P_outdegree_eq_Z_add_H_add_P G C hG hPB
    hEpsilon (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2).symm

theorem secondPViaPOrH_selected_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 → V) (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 7)
    (hSecond : secondPViaPOrH
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) z w a)
        source target = true) :
    (p ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondPViaPOrH, Bool.and_eq_true,
    decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hNotArcBool⟩, hReach⟩
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (p ⟨target, ht⟩).1 := by
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 7) = ⟨source, hs⟩ := by
      apply p.injective
      exact Subtype.ext hEq
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V,
      G.Adj (p ⟨source, hs⟩).1 middle ∧
        G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [reachedPViaPOrH, Bool.or_eq_true] at hReach
    rcases hReach with hViaP | hViaH
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (p ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          z w a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1
          (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          z w a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 3 _).mp hViaH
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (p ⟨source, hs⟩).1 (h ⟨middle, hm⟩).1 := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          z w a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (h ⟨middle, hm⟩).1
          (p ⟨target, ht⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          z w a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(h ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondOutsideHOverlap_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P}) (z : Fin 5 → V)
    (w : Fin 6 → V) (h : Fin 3 ≃ {v : V // v ∈ C.H})
    (a : Fin 8 → V) (overlap a1In source target : Nat)
    (hs : source < 7) (ht : target < 3)
    (hSecond : secondOutsideHOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1) z w a)
        source target = true) :
    (h ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondOutsideHOverlap, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨⟨_hOutside, hReach⟩, hNotArcBool⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
    rw [pArc_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj (p ⟨middle, hm⟩).1
      (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1
      (h ⟨target, ht⟩).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      z w a source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (h ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
      (h ⟨target, ht⟩).2 (hEq ▸ (p ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem secondMissingZ_selected_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z}) (w : Fin 6 → V)
    (h : Fin 3 → V) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 7) (ht : target < 5)
    (hSecond : secondMissingZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1) w a)
        source target = true) :
    (z ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  simp only [secondMissingZ, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨_hmTarget, hFirstBool⟩, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj (z ⟨middle, hm⟩).1
      (z ⟨target, ht⟩).1 := by
    rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1
      (z ⟨target, ht⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (z ⟨target, ht⟩).1 ≠
      (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
      (z ⟨target, ht⟩).2 (hEq ▸ (p ⟨source, hs⟩).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem secondWOverlap_true_mem (C : G.LocalConfiguration)
    (S : Finset V) (hS : S ⊆ zExternalUnion G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hRange : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi < 3 ∨
        overlapWToH overlap a1In wi = 3)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hOutside : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi = 3 → (w wi).1 ∉ C.H)
    (source target : Nat) (hs : source < 7) (ht : target < 6)
    (hSecond : secondWOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (w ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (p ⟨source, hs⟩).1 := by
  let wi : Fin 6 := ⟨target, ht⟩
  let hi := overlapWToH overlap a1In target
  simp only [secondWOverlap, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotDirectData⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hReach
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (p ⟨source, hs⟩).1 (z ⟨middle, hm⟩).1 := by
    rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (w wi).1 := by
    rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (p ⟨source, hs⟩).1 (w wi).1 := by
    rcases hRange wi with hiLt | hiEq
    · simp only [Bool.or_eq_true] at hNotDirectData
      have hiLt' : hi < 3 := by simpa [hi, wi] using hiLt
      rcases hNotDirectData with hImpossible | hNotDirect
      · have : hi ≠ 3 := by omega
        exact (this (of_decide_eq_true hImpossible)).elim
      · rw [pToH_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a source hi hs hiLt'] at hNotDirect
        simpa [wi, hi, hMapped wi hiLt] using hNotDirect
    · intro hDirect
      have hvCaptured := outgoingCaptured_of_p_eq_B
        G C hG hPB (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2
        ((Digraph.mem_outNeighborFinset (G := G)).mpr hDirect)
      simp only [Finset.mem_union, Finset.mem_singleton] at hvCaptured
      have hwUnion : (w wi).1 ∈ zExternalUnion G C := hS (w wi).2
      rcases hvCaptured with ((hvZ | hvs) | hvH) | hvP
      · exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
          hvZ hwUnion
      · have hDirectS : G.Adj (p ⟨source, hs⟩).1 C.s := by
          simpa [hvs] using hDirect
        exact FiveZExactPBridge.no_P_to_s_of_epsilonS_zero G C hEpsilon
          (p ⟨source, hs⟩).1 (p ⟨source, hs⟩).2 hDirectS
      · exact hOutside wi (by simpa [hi] using hiEq) hvH
      · exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
          hvP hwUnion
  have hTargetVertexNe : (w wi).1 ≠ (p ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
      (p ⟨source, hs⟩).2 (hEq ▸ hS (w wi).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩,
    hNotArc, hTargetVertexNe⟩

theorem pSecondCountOverlap_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (S : Finset V)
    (hS : S ⊆ zExternalUnion G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hRange : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi < 3 ∨
        overlapWToH overlap a1In wi = 3)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hOutside : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi = 3 → (w wi).1 ∉ C.H)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
    (source : Nat) (hs : source < 7) :
    (secondPCount
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source +
      count 6 (secondWOverlap overlap a1In
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source) +
      count 3 (secondOutsideHOverlap overlap a1In
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source) +
      secondMissingZCount
        (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
          (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).toNat ≤
      G.secondOutdegree (p ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (p ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  let QOutside : V → Prop := fun v ↦ v ∉ S ∧ Q v
  have hPBound : (count 7 (secondPViaPOrH bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPViaPOrH_selected_true_mem G C p (fun i ↦ (z i).1)
      (fun i ↦ (w i).1) h a source j hs j.isLt hBit
  have hWBound : (count 6
      (secondWOverlap overlap a1In bits source)).toNat ≤
      (S.filter Q).card := by
    apply count_le_filterCard S w _ Q (by omega)
    intro j hBit
    exact secondWOverlap_true_mem G C S hS hG hPB hEpsilon p z w h a
      overlap a1In hRange hMapped hOutside source j hs j.isLt hBit
  have hHBound : (count 3
      (secondOutsideHOverlap overlap a1In bits source)).toNat ≤
      (C.H.filter QOutside).card := by
    apply count_le_filterCard C.H h _ QOutside (by omega)
    intro j hBit
    have hMem := secondOutsideHOverlap_true_mem G C p
      (fun i ↦ (z i).1) (fun i ↦ (w i).1) h a overlap a1In
      source j hs j.isLt hBit
    have hNotS : (h j).1 ∉ S := by
      intro hjS
      have hBool : overlapHInW overlap a1In j = true :=
        (hHSelected j).2 hjS
      simp only [bits, secondOutsideHOverlap, Bool.and_eq_true] at hBit
      have hImpossible := hBit.1.1
      simp [hBool] at hImpossible
    exact ⟨hNotS, hMem⟩
  have hZBound : (count 5 (secondMissingZ bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact secondMissingZ_selected_true_mem G C p z
      (fun i ↦ (w i).1) (fun i ↦ (h i).1) a
      source j hs j.isLt hBit
  have hPCard : (C.P.filter Q).card ≤ 7 := by
    calc
      _ ≤ C.P.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  have hWCard : (S.filter Q).card ≤ 6 := by
    calc
      _ ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by simpa using (Fintype.card_congr w).symm
  have hHCard : (C.H.filter QOutside).card ≤ 3 := by
    calc
      _ ≤ C.H.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := by simpa using (Fintype.card_congr h).symm
  have hZCard : (C.Z.filter Q).card ≤ 5 := by
    calc
      _ ≤ C.Z.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hCountNat :
      (secondPCount bits source +
        count 6 (secondWOverlap overlap a1In bits source) +
        count 3 (secondOutsideHOverlap overlap a1In bits source) +
        secondMissingZCount bits source).toNat =
      (count 7 (secondPViaPOrH bits source)).toNat +
        (count 6 (secondWOverlap overlap a1In bits source)).toNat +
        (count 3 (secondOutsideHOverlap overlap a1In bits source)).toNat +
        (count 5 (secondMissingZ bits source)).toNat := by
    rw [secondPCount, secondMissingZCount, BitVec.toNat_add,
      BitVec.toNat_add, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  let SP := C.P.filter Q
  let SW := S.filter Q
  let SH := C.H.filter QOutside
  let SZ := C.Z.filter Q
  have hP_W : Disjoint SP SW := by
    rw [Finset.disjoint_left]
    intro v hvP hvW
    exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
      (Finset.mem_filter.mp hvP).1 (hS (Finset.mem_filter.mp hvW).1)
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
      · exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
          (Finset.mem_filter.mp hvZ).1 (hS (Finset.mem_filter.mp hvW).1)
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
    _ ≤ SP.card + SW.card + SH.card + SZ.card := by
      dsimp only [SP, SW, SH, SZ]
      omega
    _ = (SP ∪ SW ∪ SH ∪ SZ).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card :=
      Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (p ⟨source, hs⟩).1 := rfl

theorem pNonSeymourOverlap_coreBits_true
    (C : G.LocalConfiguration) (S : Finset V)
    (hS : S ⊆ zExternalUnion G C)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hEpsilon : epsilonS G C = 0)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hRange : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi < 3 ∨
        overlapWToH overlap a1In wi = 3)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hOutside : ∀ wi : Fin 6,
      overlapWToH overlap a1In wi = 3 → (w wi).1 ∉ C.H)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 7) :
    pNonSeymourOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (p ⟨source, hs⟩).1
  have hDegree := pDegree_selected_toNat G C hG hPB hEpsilon p z
    (fun j ↦ (w j).1) h a source hs
  have hSecond := pSecondCountOverlap_toNat_le_secondOutdegree G C S hS
    hG hPB hEpsilon p z w h a overlap a1In hRange hMapped hOutside
    hHSelected source hs
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [pNonSeymourOverlap, BitVec.ult_eq_decide,
    decide_eq_true_eq]
  rw [hDegree]
  exact hSecond.trans_lt (by simpa [u] using hStrict)

theorem secondZFromZ_selected_true_mem (C : G.LocalConfiguration)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 → V) (h : Fin 3 → V) (a : Fin 8 → V)
    (source target : Nat) (hs : source < 5) (ht : target < 5)
    (hSecond : secondZFromZ
      (coreBits G.Adj (fun j ↦ (p j).1) h (fun j ↦ (z j).1) w a)
        source target = true) :
    (z ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  simp only [secondZFromZ, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hTargetNe, hReach⟩, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (z ⟨target, ht⟩).1 := by
    rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
      (fun j ↦ (z j).1) w a source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (z ⟨target, ht⟩).1 ≠
      (z ⟨source, hs⟩).1 := by
    intro hEq
    have hFinEq : (⟨target, ht⟩ : Fin 5) = ⟨source, hs⟩ := by
      apply z.injective
      exact Subtype.ext hEq
    exact hTargetNe (Fin.ext_iff.mp hFinEq)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (z ⟨target, ht⟩).1 := by
    simp only [reachesZFromZ, Bool.or_eq_true] at hReach
    rcases hReach with hViaZ | hViaP
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨⟨_hmSource, _hmTarget⟩, hFirstBool⟩,
        hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1
          (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) w a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1
          (z ⟨target, ht⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) w a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1
          (p ⟨middle, hm⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) w a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1
          (z ⟨target, ht⟩).1 := by
        rw [pToZ_coreBits G.Adj (fun j ↦ (p j).1) h
          (fun j ↦ (z j).1) w a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondWFromZOverlap_true_mem (C : G.LocalConfiguration)
    (S : Finset V) (hS : S ⊆ zExternalUnion G C)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (source target : Nat) (hs : source < 5) (ht : target < 6)
    (hSecond : secondWFromZOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (w ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  let wi : Fin 6 := ⟨target, ht⟩
  let hi := overlapWToH overlap a1In target
  simp only [secondWFromZOverlap, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (w wi).1 := by
    rw [zToW_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa [wi] using hNotArcBool
  have hTargetVertexNe : (w wi).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
      (z ⟨source, hs⟩).2 (hEq ▸ hS (w wi).2)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧ G.Adj middle (w wi).1 := by
    simp only [reachesWFromZOverlap, Bool.or_eq_true] at hReach
    rcases hReach with hViaZ | hViaP
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmSource, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1
          (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1 (w wi).1 := by
        rw [zToW_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hViaP
      rcases hViaP with ⟨hiLt, hAny⟩
      obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hAny
      simp only [Bool.and_eq_true] at hPath
      rcases hPath with ⟨hFirstBool, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1
          (p ⟨middle, hm⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecondH : G.Adj (p ⟨middle, hm⟩).1 (h ⟨hi, hiLt⟩).1 := by
        rw [pToH_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a middle hi hm hiLt] at hSecondBool
        exact of_decide_eq_true hSecondBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1 (w wi).1 := by
        simpa [wi, hi, hMapped wi (by simpa [wi, hi] using hiLt)]
          using hSecondH
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem secondPFromZOverlap_true_mem (C : G.LocalConfiguration)
    (S : Finset V) (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (source target : Nat) (hs : source < 5) (ht : target < 7)
    (hSecond : secondPFromZOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source target = true) :
    (p ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  simp only [secondPFromZOverlap, Bool.and_eq_true] at hSecond
  rcases hSecond with ⟨hReach, hNotArcBool⟩
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1
      (p ⟨target, ht⟩).1 := by
    rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
      source target hs ht] at hNotArcBool
    simpa using hNotArcBool
  have hTargetVertexNe : (p ⟨target, ht⟩).1 ≠
      (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
      (z ⟨source, hs⟩).2 (hEq ▸ (p ⟨target, ht⟩).2)
  have hTwoStep : ∃ middle : V,
      G.Adj (z ⟨source, hs⟩).1 middle ∧
        G.Adj middle (p ⟨target, ht⟩).1 := by
    simp only [reachesPFromZOverlap, Bool.or_eq_true] at hReach
    rcases hReach with (hViaH | hViaP) | hViaZ
    · obtain ⟨wi, hwi, hPath⟩ := (any_eq_true_iff 6 _).mp hViaH
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨hiLt, hFirstBool⟩, hSecondBool⟩
      let wf : Fin 6 := ⟨wi, hwi⟩
      let hi := overlapWToH overlap a1In wi
      have hFirstW : G.Adj (z ⟨source, hs⟩).1 (w wf).1 := by
        rw [zToW_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a source wi hs hwi] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hFirst : G.Adj (z ⟨source, hs⟩).1 (h ⟨hi, hiLt⟩).1 := by
        simpa [wf, hi, hMapped wf (by simpa [wf, hi] using hiLt)]
          using hFirstW
      have hSecond' : G.Adj (h ⟨hi, hiLt⟩).1
          (p ⟨target, ht⟩).1 := by
        rw [hToP_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a hi target hiLt ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(h ⟨hi, hiLt⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hViaP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmTarget, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1
          (p ⟨middle, hm⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (p ⟨middle, hm⟩).1
          (p ⟨target, ht⟩).1 := by
        rw [pArc_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(p ⟨middle, hm⟩).1, hFirst, hSecond'⟩
    · obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 5 _).mp hViaZ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
      rcases hPath with ⟨⟨_hmSource, hFirstBool⟩, hSecondBool⟩
      have hFirst : G.Adj (z ⟨source, hs⟩).1
          (z ⟨middle, hm⟩).1 := by
        rw [zArc_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a source middle hs hm] at hFirstBool
        exact of_decide_eq_true hFirstBool
      have hSecond' : G.Adj (z ⟨middle, hm⟩).1
          (p ⟨target, ht⟩).1 := by
        rw [zToP_coreBits G.Adj (fun j ↦ (p j).1)
          (fun j ↦ (h j).1) (fun j ↦ (z j).1)
          (fun j ↦ (w j).1) a middle target hm ht] at hSecondBool
        exact of_decide_eq_true hSecondBool
      exact ⟨(z ⟨middle, hm⟩).1, hFirst, hSecond'⟩
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨hTwoStep, hNotArc, hTargetVertexNe⟩

theorem reachesOutsideHFromZOverlap_true_mem (C : G.LocalConfiguration)
    (S : Finset V) (hRetains : zExternalUnion G C ∩ C.H ⊆ S)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z}) (w : Fin 6 → V)
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
    (source target : Nat) (hs : source < 5) (ht : target < 3)
    (hReach : reachesOutsideHFromZOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) w a) source target = true) :
    (h ⟨target, ht⟩).1 ∈
      G.secondOutNeighborFinset (z ⟨source, hs⟩).1 := by
  let hi : Fin 3 := ⟨target, ht⟩
  simp only [reachesOutsideHFromZOverlap, Bool.and_eq_true] at hReach
  rcases hReach with ⟨hOutsideBool, hAny⟩
  have hNotS : (h hi).1 ∉ S := by
    intro hS
    have hBool : overlapHInW overlap a1In hi = true :=
      (hHSelected hi).2 hS
    have hImpossible := hOutsideBool
    simp [hi, hBool] at hImpossible
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 7 _).mp hAny
  simp only [Bool.and_eq_true] at hPath
  rcases hPath with ⟨hFirstBool, hSecondBool⟩
  have hFirst : G.Adj (z ⟨source, hs⟩).1 (p ⟨middle, hm⟩).1 := by
    rw [zToP_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a source middle hs hm] at hFirstBool
    exact of_decide_eq_true hFirstBool
  have hSecond : G.Adj (p ⟨middle, hm⟩).1 (h hi).1 := by
    rw [pToH_coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
      (fun j ↦ (z j).1) w a middle target hm ht] at hSecondBool
    exact of_decide_eq_true hSecondBool
  have hNotArc : ¬G.Adj (z ⟨source, hs⟩).1 (h hi).1 := by
    intro hDirect
    have hNotP : (h hi).1 ∉ C.P := by
      intro hP
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (h hi).2 hP
    have hNotZ : (h hi).1 ∉ C.Z := by
      intro hZ
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
        hZ (h hi).2
    have hTargetW : (h hi).1 ∈ zExternalUnion G C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, by simp [hNotP, hNotZ]⟩
      apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
      exact ⟨(z ⟨source, hs⟩).1, (z ⟨source, hs⟩).2, hDirect⟩
    exact hNotS (hRetains (Finset.mem_inter.mpr ⟨hTargetW, (h hi).2⟩))
  have hTargetVertexNe : (h hi).1 ≠ (z ⟨source, hs⟩).1 := by
    intro hEq
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C))
      (z ⟨source, hs⟩).2 (hEq ▸ (h hi).2)
  rw [Digraph.mem_secondOutNeighborFinset,
    Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨(p ⟨middle, hm⟩).1, hFirst, hSecond⟩,
    hNotArc, hTargetVertexNe⟩

theorem zSecondCountOverlap_toNat_le_secondOutdegree
    (C : G.LocalConfiguration) (S : Finset V)
    (hS : S ⊆ zExternalUnion G C)
    (hRetains : zExternalUnion G C ∩ C.H ⊆ S)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
    (source : Nat) (hs : source < 5) :
    (zSecondCountOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source).toNat ≤
      G.secondOutdegree (z ⟨source, hs⟩).1 := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (z ⟨source, hs⟩).1
  let Q : V → Prop := fun v ↦ v ∈ G.secondOutNeighborFinset u
  let QOutside : V → Prop := fun v ↦ v ∉ S ∧ Q v
  have hZBound : (count 5 (secondZFromZ bits source)).toNat ≤
      (C.Z.filter Q).card := by
    apply count_le_filterCard C.Z z _ Q (by omega)
    intro j hBit
    exact secondZFromZ_selected_true_mem G C p z (fun i ↦ (w i).1)
      (fun i ↦ (h i).1) a source j hs j.isLt hBit
  have hWBound : (count 6
      (secondWFromZOverlap overlap a1In bits source)).toNat ≤
      (S.filter Q).card := by
    apply count_le_filterCard S w _ Q (by omega)
    intro j hBit
    exact secondWFromZOverlap_true_mem G C S hS p z w h a overlap a1In
      hMapped source j hs j.isLt hBit
  have hPBound : (count 7
      (secondPFromZOverlap overlap a1In bits source)).toNat ≤
      (C.P.filter Q).card := by
    apply count_le_filterCard C.P p _ Q (by omega)
    intro j hBit
    exact secondPFromZOverlap_true_mem G C S p z w h a overlap a1In
      hMapped source j hs j.isLt hBit
  have hHBound : (count 3
      (reachesOutsideHFromZOverlap overlap a1In bits source)).toNat ≤
      (C.H.filter QOutside).card := by
    apply count_le_filterCard C.H h _ QOutside (by omega)
    intro j hBit
    have hMem := reachesOutsideHFromZOverlap_true_mem G C S hRetains p z
      (fun i ↦ (w i).1) h a overlap a1In hHSelected
      source j hs j.isLt hBit
    have hNotS : (h j).1 ∉ S := by
      intro hjS
      have hBool : overlapHInW overlap a1In j = true :=
        (hHSelected j).2 hjS
      simp only [bits, reachesOutsideHFromZOverlap,
        Bool.and_eq_true] at hBit
      have hImpossible := hBit.1
      simp [hBool] at hImpossible
    exact ⟨hNotS, hMem⟩
  have hZCard : (C.Z.filter Q).card ≤ 5 := by
    calc
      _ ≤ C.Z.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 5 := by simpa using (Fintype.card_congr z).symm
  have hWCard : (S.filter Q).card ≤ 6 := by
    calc
      _ ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := by simpa using (Fintype.card_congr w).symm
  have hPCard : (C.P.filter Q).card ≤ 7 := by
    calc
      _ ≤ C.P.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simpa using (Fintype.card_congr p).symm
  have hHCard : (C.H.filter QOutside).card ≤ 3 := by
    calc
      _ ≤ C.H.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := by simpa using (Fintype.card_congr h).symm
  have hCountNat : (zSecondCountOverlap overlap a1In bits source).toNat =
      (count 5 (secondZFromZ bits source)).toNat +
        (count 6 (secondWFromZOverlap overlap a1In bits source)).toNat +
        (count 7 (secondPFromZOverlap overlap a1In bits source)).toNat +
        (count 3 (reachesOutsideHFromZOverlap overlap a1In bits source)).toNat := by
    rw [zSecondCountOverlap, BitVec.toNat_add, BitVec.toNat_add,
      BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  let SZ := C.Z.filter Q
  let SW := S.filter Q
  let SP := C.P.filter Q
  let SH := C.H.filter QOutside
  have hZ_W : Disjoint SZ SW := by
    rw [Finset.disjoint_left]
    intro v hvZ hvW
    exact (Finset.disjoint_left.mp (disjoint_Z_zExternalUnion G C))
      (Finset.mem_filter.mp hvZ).1 (hS (Finset.mem_filter.mp hvW).1)
  have hZW_P : Disjoint (SZ ∪ SW) SP := by
    rw [Finset.disjoint_left]
    intro v hvZW hvP
    rcases Finset.mem_union.mp hvZW with hvZ | hvW
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C))
        (Finset.mem_filter.mp hvZ).1 (Finset.mem_filter.mp hvP).1
    · exact (Finset.disjoint_left.mp (disjoint_P_zExternalUnion G C))
        (Finset.mem_filter.mp hvP).1 (hS (Finset.mem_filter.mp hvW).1)
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
    _ ≤ SZ.card + SW.card + SP.card + SH.card := by
      dsimp only [SZ, SW, SP, SH]
      omega
    _ = (SZ ∪ SW ∪ SP ∪ SH).card := hUnionCard.symm
    _ ≤ (G.secondOutNeighborFinset u).card :=
      Finset.card_le_card hUnionSubset
    _ = G.secondOutdegree (z ⟨source, hs⟩).1 := rfl

theorem zNonSeymourOverlap_coreBits_true
    (C : G.LocalConfiguration) (S : Finset V)
    (hS : S ⊆ zExternalUnion G C) (hSCard : S.card = 6)
    (hWCard : (zExternalUnion G C).card = 6 ∨
      (zExternalUnion G C).card = 7)
    (hRetains : zExternalUnion G C ∩ C.H ⊆ S)
    (p : Fin 7 ≃ {v : V // v ∈ C.P})
    (z : Fin 5 ≃ {v : V // v ∈ C.Z})
    (w : Fin 6 ≃ {v : V // v ∈ S})
    (h : Fin 3 ≃ {v : V // v ∈ C.H}) (a : Fin 8 → V)
    (overlap a1In : Nat)
    (hMapped : ∀ (wi : Fin 6)
      (hm : overlapWToH overlap a1In wi < 3),
      (w wi).1 = (h ⟨overlapWToH overlap a1In wi, hm⟩).1)
    (hHSelected : ∀ hi : Fin 3,
      overlapHInW overlap a1In hi = true ↔ (h hi).1 ∈ S)
    (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 5) :
    zNonSeymourOverlap overlap a1In
      (coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
        (fun j ↦ (z j).1) (fun j ↦ (w j).1) a) source = true := by
  let bits := coreBits G.Adj (fun j ↦ (p j).1) (fun j ↦ (h j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1) a
  let u := (z ⟨source, hs⟩).1
  have hDegree := zDegree_selected_toNat G C S p z w
    (fun j ↦ (h j).1) a source hs
  have hActual := z_outdegree_eq_retainedCounts G C u
    (z ⟨source, hs⟩).2
  have hUnion := directCount_union_le_selected_add_one G C S hS hSCard
    hWCard u
  have hSecond := zSecondCountOverlap_toNat_le_secondOutdegree G C S hS
    hRetains p z w h a overlap a1In hMapped hHSelected source hs
  have hStrict : G.secondOutdegree u < G.outdegree u := by
    have hNot : ¬G.IsSeymourVertex u := by
      intro hu
      exact hNoSeymour ⟨u, hu⟩
    unfold Digraph.IsSeymourVertex at hNot
    omega
  simp only [zNonSeymourOverlap, BitVec.ule_eq_decide,
    decide_eq_true_eq]
  rw [hDegree]
  have hActual' := hActual
  dsimp only [u] at hActual' hUnion hStrict
  omega

end SeymourEight.FiveZExactSelectedBridge
