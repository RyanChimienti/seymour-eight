import SeymourEight.Cases.BSixKTwo.CoreGraphBridge

/-!
# Closure of the `(|B|, k) = (6, 2)` case
-/

namespace SeymourEight.BSixKTwo

open BSixKTwoCore BSixKTwoCoreBridge BSixKTwoCoreGraphBridge
  CertificateBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem externalTargets_mem_cases (C : G.LocalConfiguration) {v : V}
    (hv : v ∈ externalTargets G C) : v ∈ C.Z ∨ v = C.s := by
  rcases Finset.mem_union.mp hv with hvZ | hvRoot
  · exact Or.inl hvZ
  · by_cases hReach : ∃ p ∈ C.P, G.Adj p C.s
    · right
      simpa [rootSecondFinset, hReach] using hvRoot
    · simp [rootSecondFinset, hReach] at hvRoot

theorem protectedTargets_subset_A (C : G.LocalConfiguration) :
    protectedTargets G C ⊆ C.A := by
  intro v hv
  have hUnion := H_union_protectedTargets_eq_A G C
  rw [← hUnion]
  exact Finset.mem_union_right C.H hv

/-- The prescribed `A₁`-then-`X` labeling is an equivalence with `H`. -/
noncomputable def hLabelEquiv {x : Nat} (C : G.LocalConfiguration)
    (eA : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X}) :
    Fin (hSize x) ≃ {v : V // v ∈ C.H} := by
  let f : Fin (hSize x) → {v : V // v ∈ C.H} := fun i ↦ ⟨
    hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) i, by
      induction i using Fin.addCases with
      | left j =>
          simp [hLabel, Digraph.LocalConfiguration.H]
      | right j =>
          simp [hLabel, Digraph.LocalConfiguration.H]⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply hLabel_injective
      (a := fun j ↦ (eA j).1) (y := fun j ↦ (eX j).1)
      (fun a b hab ↦ eA.injective (Subtype.ext hab))
      (fun a b hab ↦ eX.injective (Subtype.ext hab))
      (fun a b hab ↦ (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
          (eA a).2 (hab ▸ (eX b).2))
    exact congrArg Subtype.val hij
  · intro v
    rcases Finset.mem_union.mp v.2 with hvA | hvX
    · obtain ⟨i, hi⟩ := eA.surjective ⟨v, hvA⟩
      refine ⟨Fin.castAdd x i, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi
    · obtain ⟨i, hi⟩ := eX.surjective ⟨v, hvX⟩
      refine ⟨Fin.natAdd 2 i, ?_⟩
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hi

@[simp]
theorem hLabelEquiv_apply {x : Nat} (C : G.LocalConfiguration)
    (eA : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X}) (i : Fin (hSize x)) :
    (hLabelEquiv G C eA eX i).1 =
      hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) i := rfl

/-- The core, protected, and external label families enumerate distinct
vertices of the local configuration. -/
theorem localLabels_injective {x : Nat} (C : G.LocalConfiguration)
    (hG : G.IsOriented)
    (eA : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eP : Fin 6 ≃ {v : V // v ∈ C.P})
    (eT : Fin (tSize x) ≃ {v : V // v ∈ protectedTargets G C})
    (eW : Fin (wSize x) ≃ {v : V // v ∈ externalTargets G C}) :
    Function.Injective (Sum.elim
      (fun i : Fin (coreSize x) ↦ coreAt
        (hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1))
        (fun j ↦ (eP j).1) i)
      (Sum.elim (fun j ↦ (eT j).1) (fun j ↦ (eW j).1)) :
        Fin (coreSize x) ⊕ (Fin (tSize x) ⊕ Fin (wSize x)) → V) := by
  let h := hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1)
  let p := fun j ↦ (eP j).1
  let t := fun j ↦ (eT j).1
  let w := fun j ↦ (eW j).1
  have hH : ∀ i, h i ∈ C.H := by
    intro i
    induction i using Fin.addCases with
    | left i =>
        change h (Fin.castAdd x i) ∈ C.A1 ∪ C.X
        simp [h, hLabel]
    | right i =>
        change h (Fin.natAdd 2 i) ∈ C.A1 ∪ C.X
        simp [h, hLabel]
  have hpP : ∀ i, p i ∈ C.P := fun i ↦ (eP i).2
  have htT : ∀ i, t i ∈ protectedTargets G C := fun i ↦ (eT i).2
  have hwW : ∀ i, w i ∈ externalTargets G C := fun i ↦ (eW i).2
  have hh : Function.Injective h := by
    apply hLabel_injective
    · intro i j hij
      exact eA.injective (Subtype.ext hij)
    · intro i j hij
      exact eX.injective (Subtype.ext hij)
    · intro i j hij
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
          (eA i).2 (hij ▸ (eX j).2)
  have hp : Function.Injective p := by
    intro i j hij
    exact eP.injective (Subtype.ext hij)
  have ht : Function.Injective t := by
    intro i j hij
    exact eT.injective (Subtype.ext hij)
  have hw : Function.Injective w := by
    intro i j hij
    exact eW.injective (Subtype.ext hij)
  have hhp : ∀ i j, h i ≠ p j := by
    intro i j hij
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_H_P (G := G) C))
        (hH i) (hij ▸ hpP j)
  have hc := coreAt_injective h p hh hp hhp
  apply threeBlockLabels_injective
      (core := fun i : Fin (coreSize x) ↦ coreAt h p i)
      (t := t) (w := w) hc ht hw
  · intro i j hij
    by_cases hi : i.val < hSize x
    · have hvH : coreAt h p i ∈ C.H := by
        simpa [coreAt, hi, hAt, Nat.mod_eq_of_lt hi] using hH ⟨i, hi⟩
      exact (Finset.disjoint_left.mp (disjoint_H_protectedTargets G C hG))
        hvH (hij ▸ htT j)
    · have hi6 : i.val - hSize x < 6 := by
        have := i.isLt
        simp [coreSize, hSize] at this ⊢
        omega
      have hvP : coreAt h p i ∈ C.P := by
        simpa [coreAt, hi, pAt, Nat.mod_eq_of_lt hi6] using hpP ⟨i.val - hSize x, hi6⟩
      exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
          (protectedTargets_subset_A G C (hij ▸ htT j))
          (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  · intro i j hij
    have hwCases := externalTargets_mem_cases G C (hij ▸ hwW j)
    by_cases hi : i.val < hSize x
    · have hvH : coreAt h p i ∈ C.H := by
        simpa [coreAt, hi, hAt, Nat.mod_eq_of_lt hi] using hH ⟨i, hi⟩
      rcases hwCases with hvZ | hvs
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
      · exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1
          (hvs ▸ hvH)
    · have hi6 : i.val - hSize x < 6 := by
        have := i.isLt
        simp [coreSize, hSize] at this ⊢
        omega
      have hvP : coreAt h p i ∈ C.P := by
        simpa [coreAt, hi, pAt, Nat.mod_eq_of_lt hi6] using hpP ⟨i.val - hSize x, hi6⟩
      rcases hwCases with hvZ | hvs
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
      · exact Digraph.LocalConfiguration.s_notMem_P (G := G) C (hvs ▸ hvP)
  · intro i j hij
    have htA := protectedTargets_subset_A G C (htT i)
    rcases externalTargets_mem_cases G C (hij ▸ hwW j) with hvZ | hvs
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hvZ
          (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} htA))
    · exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 (hvs ▸ htA)

omit [Fintype V] [DecidableEq V] in
theorem not_adj_of_directCount_eq_zero (S : Finset V) (u v : V)
    (hv : v ∈ S) (hzero : directCount G S u = 0) : ¬G.Adj u v := by
  classical
  intro huv
  have hvFilter : v ∈ S.filter (G.Adj u) := Finset.mem_filter.mpr ⟨hv, huv⟩
  have hpos : 0 < (S.filter (G.Adj u)).card := Finset.card_pos.mpr ⟨v, hvFilter⟩
  change (S.filter (G.Adj u)).card = 0 at hzero
  omega

/-- A counterexample in one of the three surviving parameter rows produces a
Boolean core satisfying all common constraints. -/
theorem baseCore_of_graphData {x : Nat} (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hNoSeymour : ¬G.HasSeymourVertex) (hPivot : IsMinimalPivot G C)
    (_hBCard : C.B.card = 6) (hPB : C.P = C.B) (hk : C.k = 2) (_hx : C.x = x)
    (hxPos : 0 < x) (hxLe : x ≤ 5)
    (_hTCard : (protectedTargets G C).card = tSize x)
    (_hWCard : (externalTargets G C).card = wSize x)
    (eA : Fin 2 ≃ {v : V // v ∈ C.A1})
    (eX : Fin x ≃ {v : V // v ∈ C.X})
    (eP : Fin 6 ≃ {v : V // v ∈ C.P})
    (eT : Fin (tSize x) ≃ {v : V // v ∈ protectedTargets G C})
    (eW : Fin (wSize x) ≃ {v : V // v ∈ externalTargets G C}) :
    let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
    let p := fun i ↦ (eP i).1
    let t := fun i ↦ (eT i).1
    let w := fun i ↦ (eW i).1
    baseCore (coreBits G.Adj hxLe h p t w) = true := by
  classical
  let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
  let p := fun i ↦ (eP i).1
  let t := fun i ↦ (eT i).1
  let w := fun i ↦ (eW i).1
  let bits := coreBits G.Adj hxLe h p t w
  have hHmem : ∀ i, h i ∈ C.H := by
    intro i
    induction i using Fin.addCases with
    | left i =>
        change h (Fin.castAdd x i) ∈ C.A1 ∪ C.X
        simp [h, hLabel]
    | right i =>
        change h (Fin.natAdd 2 i) ∈ C.A1 ∪ C.X
        simp [h, hLabel]
  have hLabels : Function.Injective (Sum.elim
      (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w) :
      Fin (coreSize x) ⊕ (Fin (tSize x) ⊕ Fin (wSize x)) → V) := by
    simpa [h, p, t, w] using
      localLabels_injective G C hG eA eX eP eT eW
  apply baseCore_true_of
  · exact oriented_coreBits G.Adj hxLe h p t w hG.1 hG.2
  · intro i hi
    rw [toNat_hDegree_coreBits G.Adj hxLe h p t w i hi]
    have hCore := trueCount_core_hLabel G hxPos hxLe C.A1 C.X C.P
      eA eX eP (h ⟨i, hi⟩)
    have hCore' : trueCount (coreSize x)
        (fun j ↦ decide (G.Adj (h ⟨i, hi⟩) (coreAt h p j))) =
        directCount G C.A1 (h ⟨i, hi⟩) + directCount G C.X (h ⟨i, hi⟩) +
          directCount G C.P (h ⟨i, hi⟩) := by
      simpa [h, p] using hCore
    rw [hCore']
    have hT := trueCount_labelled G (protectedTargets G C) eT (h ⟨i, hi⟩)
      (by simp [tSize]; omega) (by simp [tSize]; omega)
    have hTDecode : trueCount (tSize x)
        (fun j ↦ decide (G.Adj (h ⟨i, hi⟩) (tAt hxLe t j))) =
        directCount G (protectedTargets G C) (h ⟨i, hi⟩) := by
      rw [← hT]
      apply trueCount_congr
      intro j hj
      rw [tAt_of_lt hxLe t j hj]
      simp [t, Nat.mod_eq_of_lt hj]
    rw [hTDecode]
    have hDegree := outdegree_H_eq_blocks G C hG hPB (h ⟨i, hi⟩) (hHmem ⟨i, hi⟩)
    by_cases hi2 : 2 ≤ i
    · simp [hi2]
      have := hMin (h ⟨i, hi⟩)
      omega
    · have hiA : i < 2 := by omega
      have huA1 : h ⟨i, hi⟩ ∈ C.A1 := by
        have hv := (eA ⟨i, hiA⟩).2
        change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨i, hi⟩ ∈ C.A1
        have hIndex : (⟨i, hi⟩ : Fin (hSize x)) = Fin.castAdd x ⟨i, hiA⟩ := by
          apply Fin.ext
          rfl
        rw [hIndex, hLabel_castAdd]
        exact hv
      have hzero := directCount_protected_eq_zero_of_mem_A1 G C hG _ huA1
      simp [hi2]
      have := hMin (h ⟨i, hi⟩)
      omega
  · intro i hi
    rw [toNat_pDegree_coreBits G.Adj hxLe h p t w i hi]
    have hCore := trueCount_core_hLabel G hxPos hxLe C.A1 C.X C.P
      eA eX eP (p ⟨i, hi⟩)
    have hCore' : trueCount (coreSize x)
        (fun j ↦ decide (G.Adj (p ⟨i, hi⟩) (coreAt h p j))) =
        directCount G C.A1 (p ⟨i, hi⟩) + directCount G C.X (p ⟨i, hi⟩) +
          directCount G C.P (p ⟨i, hi⟩) := by
      simpa [h, p] using hCore
    rw [hCore']
    have hW := trueCount_labelled G (externalTargets G C) eW (p ⟨i, hi⟩)
      (by simp [wSize]; omega) (by simp [wSize]; omega)
    have hWDecode : trueCount (wSize x)
        (fun j ↦ decide (G.Adj (p ⟨i, hi⟩) (wAt hxLe w j))) =
        directCount G (externalTargets G C) (p ⟨i, hi⟩) := by
      rw [← hW]
      apply trueCount_congr
      intro j hj
      rw [wAt_of_lt hxLe w j hj]
      simp [w, Nat.mod_eq_of_lt hj]
    rw [hWDecode]
    have hpMem : p ⟨i, hi⟩ ∈ C.P := (eP ⟨i, hi⟩).2
    have hDegree := outdegree_P_eq_blocks G C hG hPB _ hpMem
    have := hMin (p ⟨i, hi⟩)
    omega
  · intro u hu
    have huH : u < hSize x := by simp [hSize]; omega
    have huA1 : h ⟨u, huH⟩ ∈ C.A1 := by
      have hv := (eA ⟨u, hu⟩).2
      have hIndex : (⟨u, huH⟩ : Fin (hSize x)) = Fin.castAdd x ⟨u, hu⟩ := by
        apply Fin.ext
        rfl
      change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨u, huH⟩ ∈ C.A1
      rw [hIndex, hLabel_castAdd]
      exact hv
    rw [toNat_hInternal_coreBits G hxPos hxLe C.A1 C.X eA eX p t w u huH]
    have hA := (hPivot (h ⟨u, huH⟩)
      (Digraph.LocalConfiguration.A1_subset_A (G := G) C huA1)).1
    rw [hk] at hA
    change 2 ≤ directCount G C.A (h ⟨u, huH⟩) at hA
    have hzero := directCount_protected_eq_zero_of_mem_A1 G C hG _ huA1
    rw [← H_union_protectedTargets_eq_A G C,
      Shared.directCount_union_of_disjoint G C.H (protectedTargets G C)
        _ (disjoint_H_protectedTargets G C hG), hzero,
      Digraph.LocalConfiguration.H,
      Shared.directCount_union_of_disjoint G C.A1 C.X _
        (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C)] at hA
    omega
  · intro u hu
    have huH : u < hSize x := by simp [hSize]; omega
    have huA1 : h ⟨u, huH⟩ ∈ C.A1 := by
      have hv := (eA ⟨u, hu⟩).2
      have hIndex : (⟨u, huH⟩ : Fin (hSize x)) = Fin.castAdd x ⟨u, hu⟩ := by
        apply Fin.ext
        rfl
      change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨u, huH⟩ ∈ C.A1
      rw [hIndex, hLabel_castAdd]
      exact hv
    have hzero := directCount_protected_eq_zero_of_mem_A1 G C hG _ huA1
    have hNoT : ∀ j : Fin (tSize x), ¬G.Adj (h ⟨u, huH⟩) (t j) := by
      intro j
      exact not_adj_of_directCount_eq_zero G _ _ _ (eT j).2 hzero
    have hCaptured := Shared.H_outgoingCaptured G C hG hPB
      (h ⟨u, huH⟩) (hHmem ⟨u, huH⟩)
    have hNoW : ∀ j : Fin (wSize x), ¬G.Adj (h ⟨u, huH⟩) (w j) := by
      intro j huwj
      have hwMem : w j ∈ externalTargets G C := (eW j).2
      have hwCaptured := hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huwj)
      rcases externalTargets_mem_cases G C hwMem with hwZ | hws
      · rcases Finset.mem_union.mp hwCaptured with hwA | hwP
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hwZ
              (Finset.mem_union_left C.B (Finset.mem_union_right {C.s} hwA))
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
      · rcases Finset.mem_union.mp hwCaptured with hwA | hwP
        · exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1 (hws ▸ hwA)
        · exact Digraph.LocalConfiguration.s_notMem_P (G := G) C (hws ▸ hwP)
    have hRepresented := representedSecondCount_le_secondOutdegree G hxLe h p t w
      u hu hLabels hNoT hNoW
    have hNotSeymour : ¬G.IsSeymourVertex (h ⟨u, huH⟩) := by
      intro hS
      exact hNoSeymour ⟨_, hS⟩
    have hStrict := Digraph.secondOutdegree_lt_outdegree_of_not_seymour G hNotSeymour
    have hInternal : (internalOut bits u).toNat =
        directCount G C.A1 (h ⟨u, huH⟩) +
          directCount G C.X (h ⟨u, huH⟩) +
            directCount G C.P (h ⟨u, huH⟩) := by
      rw [toNat_internalOut hxLe bits u]
      have hCore := trueCount_core_hLabel G hxPos hxLe C.A1 C.X C.P
        eA eX eP (h ⟨u, huH⟩)
      have hArc : trueCount (coreSize x) (arc bits u) =
          trueCount (coreSize x)
            (fun j ↦ decide (G.Adj (h ⟨u, huH⟩) (coreAt h p j))) := by
        apply trueCount_congr
        intro j hj
        rw [arc_coreBits G.Adj hxLe h p t w u j
          (by unfold coreSize; omega) hj,
          coreAt_h h p u huH]
      rw [hArc]
      simpa [h, p] using hCore
    have hDegree := outdegree_H_eq_blocks G C hG hPB _ (hHmem ⟨u, huH⟩)
    have hDegree' : G.outdegree (h ⟨u, huH⟩) =
        directCount G C.A1 (h ⟨u, huH⟩) +
          directCount G C.X (h ⟨u, huH⟩) +
            directCount G C.P (h ⟨u, huH⟩) := by
      rw [hzero] at hDegree
      omega
    rw [hInternal, ← hDegree']
    exact lt_of_le_of_lt hRepresented hStrict

theorem protectedTargets_card (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 2)
    {x : Nat} (hx : C.x = x) :
    (protectedTargets G C).card = tSize x := by
  have hUnion := H_union_protectedTargets_eq_A G C
  have hDisjoint := disjoint_H_protectedTargets G C hG
  have hSum : C.H.card + (protectedTargets G C).card = C.A.card := by
    rw [← hUnion, Finset.card_union_of_disjoint hDisjoint]
  have hH := h_card_eq_x_add_two G C hk
  have hA : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  rw [hH, hx, hA] at hSum
  simp [tSize]
  omega

/-- The fully checked `(6,2)` leaf. -/
theorem bSixKTwoCase : BSixKTwoCase := by
  intro V _ _ _hBound G _ C hG hMin hRoot hPivot hBCard hk
  by_contra hNoSeymour
  have hPB := p_eq_B G C hG hMin hBCard hk
  rcases parameterRows G C hG hMin hNoSeymour hRoot hPivot hBCard hk with
    ⟨hx, hwCard⟩ | ⟨hx, hwCard⟩ | ⟨hx, hwCard⟩
  · let eA := finsetEquivFin C.A1 (by simpa [Digraph.LocalConfiguration.k] using hk)
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eP := finsetEquivFin C.P (by simpa [hPB] using hBCard)
    have hTCard := protectedTargets_card G C hG hRoot hk hx
    have hWCard : (externalTargets G C).card = wSize 1 := by
      rw [card_externalTargets G C, hwCard]
      decide
    let eT := finsetEquivFin (protectedTargets G C) hTCard
    let eW := finsetEquivFin (externalTargets G C) hWCard
    let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
    let p := fun i ↦ (eP i).1
    let t := fun i ↦ (eT i).1
    let w := fun i ↦ (eW i).1
    let bits := coreBits G.Adj (x := 1) (by omega) h p t w
    have hBase : baseCore bits = true := by
      simpa [bits, h, p, t, w] using baseCore_of_graphData G C hG hMin hNoSeymour
        hPivot hBCard hPB hk hx (by omega) (by omega) hTCard hWCard eA eX eP eT eW
    have hTrue : xOneCore bits = true := by simpa [xOneCore] using hBase
    have hFalse := xOneCore_unsat bits
    rw [hFalse] at hTrue
    contradiction
  · let eA := finsetEquivFin C.A1 (by simpa [Digraph.LocalConfiguration.k] using hk)
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eP := finsetEquivFin C.P (by simpa [hPB] using hBCard)
    have hTCard := protectedTargets_card G C hG hRoot hk hx
    have hWCard : (externalTargets G C).card = wSize 2 := by
      rw [card_externalTargets G C, hwCard]
      decide
    let eT := finsetEquivFin (protectedTargets G C) hTCard
    let eW := finsetEquivFin (externalTargets G C) hWCard
    let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
    let p := fun i ↦ (eP i).1
    let t := fun i ↦ (eT i).1
    let w := fun i ↦ (eW i).1
    let bits := coreBits G.Adj (x := 2) (by omega) h p t w
    have hBase : baseCore bits = true := by
      simpa [bits, h, p, t, w] using baseCore_of_graphData G C hG hMin hNoSeymour
        hPivot hBCard hPB hk hx (by omega) (by omega) hTCard hWCard eA eX eP eT eW
    have hTrue : xTwoCore bits = true := by simpa [xTwoCore] using hBase
    have hFalse := xTwoCore_unsat bits
    rw [hFalse] at hTrue
    contradiction
  · let eA := finsetEquivFin C.A1 (by simpa [Digraph.LocalConfiguration.k] using hk)
    let eX := finsetEquivFin C.X (by simpa [Digraph.LocalConfiguration.x] using hx)
    let eP := finsetEquivFin C.P (by simpa [hPB] using hBCard)
    have hTCard := protectedTargets_card G C hG hRoot hk hx
    have hWCard : (externalTargets G C).card = wSize 3 := by
      rw [card_externalTargets G C, hwCard]
      decide
    let eT := finsetEquivFin (protectedTargets G C) hTCard
    let eW := finsetEquivFin (externalTargets G C) hWCard
    let eH := hLabelEquiv G C eA eX
    let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
    let p := fun i ↦ (eP i).1
    let t := fun i ↦ (eT i).1
    let w := fun i ↦ (eW i).1
    let bits := coreBits G.Adj (x := 3) (by omega) h p t w
    have hBase : baseCore bits = true := by
      simpa [bits, h, p, t, w] using baseCore_of_graphData G C hG hMin hNoSeymour
        hPivot hBCard hPB hk hx (by omega) (by omega) hTCard hWCard eA eX eP eT eW
    have hCounts := x_three_tight_counts G C hG hMin hRoot hBCard hk hx hwCard
    have hHPNat : (totalHToP bits).toNat = 21 := by
      have hDecode := toNat_totalHToP_coreBits G (x := 3) (by omega) C.H C.P eH eP t w
      simpa [bits, h, p, eH] using hDecode.trans hCounts.1
    have hPHNat : (totalPToH bits).toNat = 9 := by
      have hDecode := toNat_totalPToH_coreBits G (x := 3) (by omega) C.H C.P eH eP t w
      simpa [bits, h, p, eH] using hDecode.trans hCounts.2
    have hHP : totalHToP bits = (21 : BitVec 8) := BitVec.eq_of_toNat_eq hHPNat
    have hPH : totalPToH bits = (9 : BitVec 8) := BitVec.eq_of_toNat_eq hPHNat
    have hTrue : xThreeCore bits = true := by
      simp [xThreeCore, hBase, hHP, hPH]
    have hFalse := xThreeCore_unsat bits
    rw [hFalse] at hTrue
    contradiction

end SeymourEight.BSixKTwo
