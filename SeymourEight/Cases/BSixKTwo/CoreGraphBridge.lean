import SeymourEight.Cases.BSixKTwo.Counting
import SeymourEight.Certificates.BSixKTwo.CoreBridge
import SeymourEight.Shared.FinsetBridge

/-!
# Soundness bridge from a `(6,2)` graph to the finite cores
-/

namespace SeymourEight.BSixKTwoCoreGraphBridge

open BSixKTwo BSixKTwoCore BSixKTwoCoreBridge CertificateBridge Shared

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Label `H=A₁∪X` with the two `A₁` vertices first. -/
def hLabel {x : Nat} (a : Fin 2 → V) (y : Fin x → V) : Fin (hSize x) → V :=
  Fin.append a y

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem hLabel_castAdd {x : Nat} (a : Fin 2 → V) (y : Fin x → V) (i : Fin 2) :
    hLabel a y (Fin.castAdd x i) = a i := by
  classical
  simp [hLabel]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem hLabel_natAdd {x : Nat} (a : Fin 2 → V) (y : Fin x → V) (i : Fin x) :
    hLabel a y (Fin.natAdd 2 i) = y i := by
  classical
  simp [hLabel]

omit [Fintype V] [DecidableEq V] in
theorem hLabel_injective {x : Nat} (a : Fin 2 → V) (y : Fin x → V)
    (ha : Function.Injective a) (hy : Function.Injective y)
    (hay : ∀ i j, a i ≠ y j) : Function.Injective (hLabel a y) := by
  rw [hLabel, Fin.append_injective_iff]
  exact ⟨ha, hy, hay⟩

omit [Fintype V] [DecidableEq V] in
theorem coreAt_injective {x : Nat} (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (hh : Function.Injective h) (hp : Function.Injective p)
    (hhp : ∀ i j, h i ≠ p j) :
    Function.Injective (fun i : Fin (coreSize x) ↦ coreAt h p i) := by
  intro i j hij
  by_cases hi : i.val < hSize x <;> by_cases hj : j.val < hSize x
  · have hv : h ⟨i, hi⟩ = h ⟨j, hj⟩ := by
      simpa [coreAt, hi, hj, hAt, Nat.mod_eq_of_lt hi,
        Nat.mod_eq_of_lt hj] using hij
    have hidx : (⟨i.val, hi⟩ : Fin (hSize x)) = ⟨j.val, hj⟩ := hh hv
    have hval : i.val = j.val :=
      congrArg (fun q : Fin (hSize x) ↦ q.val) hidx
    exact Fin.ext hval
  · have hj6 : j.val - hSize x < 6 := by
      have := j.isLt
      simp [coreSize, hSize] at this ⊢
      omega
    have hv : h ⟨i, hi⟩ = p ⟨j.val - hSize x, hj6⟩ := by
      simpa [coreAt, hi, hj, hAt, pAt, Nat.mod_eq_of_lt hi,
        Nat.mod_eq_of_lt hj6] using hij
    exact (hhp _ _ hv).elim
  · have hi6 : i.val - hSize x < 6 := by
      have := i.isLt
      simp [coreSize, hSize] at this ⊢
      omega
    have hv : p ⟨i.val - hSize x, hi6⟩ = h ⟨j, hj⟩ := by
      simpa [coreAt, hi, hj, hAt, pAt, Nat.mod_eq_of_lt hj,
        Nat.mod_eq_of_lt hi6] using hij
    exact (hhp _ _ hv.symm).elim
  · have hi6 : i.val - hSize x < 6 := by
      have := i.isLt
      simp [coreSize, hSize] at this ⊢
      omega
    have hj6 : j.val - hSize x < 6 := by
      have := j.isLt
      simp [coreSize, hSize] at this ⊢
      omega
    have hv : p ⟨i.val - hSize x, hi6⟩ =
        p ⟨j.val - hSize x, hj6⟩ := by
      simpa [coreAt, hi, hj, pAt, Nat.mod_eq_of_lt hi6,
        Nat.mod_eq_of_lt hj6] using hij
    have hdiff : i.val - hSize x = j.val - hSize x :=
      Fin.ext_iff.mp (hp hv)
    have hiLower : hSize x ≤ i.val := Nat.le_of_not_gt hi
    have hjLower : hSize x ≤ j.val := Nat.le_of_not_gt hj
    apply Fin.ext
    omega

omit [Fintype V] [DecidableEq V] in
theorem threeBlockLabels_injective {x : Nat}
    (core : Fin (coreSize x) → V) (t : Fin (tSize x) → V)
    (w : Fin (wSize x) → V)
    (hc : Function.Injective core) (ht : Function.Injective t)
    (hw : Function.Injective w)
    (hct : ∀ i j, core i ≠ t j) (hcw : ∀ i j, core i ≠ w j)
    (htw : ∀ i j, t i ≠ w j) :
    Function.Injective (Sum.elim core (Sum.elim t w) :
      Fin (coreSize x) ⊕ (Fin (tSize x) ⊕ Fin (wSize x)) → V) := by
  apply Sum.elim_injective.mpr
  refine ⟨hc, Sum.elim_injective.mpr ⟨ht, hw, htw⟩, ?_⟩
  intro i j
  rcases j with j | j
  · exact hct i j
  · exact hcw i j

omit [Fintype V] [DecidableEq V] in
/-- A byte sum over an equivalence is the corresponding direct-neighbor count. -/
theorem toNat_sumN_equiv {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (u : V) (hnPos : 0 < n) (hn : n < 256) :
    (sumN n (fun i ↦ decide (G.Adj u (e ⟨i % n,
      Nat.mod_lt _ hnPos⟩).1))).toNat = directCount G S u := by
  rw [toNat_sumN n _ hn]
  have hDirect := Shared.directCount_eq_sum_fin G S e u
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : Nat ↦ (bitCount (decide
      (G.Adj u (e ⟨i % n, Nat.mod_lt _ hnPos⟩).1))).toNat) n]
  rw [hDirect]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ⟨i.val % n, Nat.mod_lt i.val hnPos⟩ = i by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt]
  by_cases hAdj : G.Adj u (e i).1 <;> simp [bitCount, hAdj]

omit [Fintype V] [DecidableEq V] in
theorem trueCount_equiv {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (u : V)
    (hnPos : 0 < n) (hn : n < 256) :
    trueCount n (fun i ↦ decide (G.Adj u (e ⟨i % n,
      Nat.mod_lt _ hnPos⟩).1)) = directCount G S u := by
  rw [← toNat_sumN_eq_trueCount n _ hn]
  exact toNat_sumN_equiv G S e u hnPos hn

omit [Fintype V] [DecidableEq V] in
/-- The square block enumerates `A₁`, then `X`, then `P`. -/
theorem trueCount_core_hLabel {x : Nat} (hxPos : 0 < x) (hxLe : x ≤ 5)
    (A1 X P : Finset V)
    (eA : Fin 2 ≃ {v : V // v ∈ A1})
    (eX : Fin x ≃ {v : V // v ∈ X})
    (eP : Fin 6 ≃ {v : V // v ∈ P}) (u : V) :
    trueCount (coreSize x) (fun j ↦ decide
      (G.Adj u (coreAt (hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1))
        (fun i ↦ (eP i).1) j))) =
      directCount G A1 u + directCount G X u + directCount G P u := by
  classical
  let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
  let p := fun i ↦ (eP i).1
  rw [trueCount_eq_sum _ _ (by unfold coreSize; omega)]
  have hCore : coreSize x = (2 + x) + 6 := by
    unfold coreSize
    omega
  rw [hCore, Finset.sum_range_add, Finset.sum_range_add]
  have hA := toNat_sumN_equiv G A1 eA u (by omega) (by omega)
  have hX := toNat_sumN_equiv G X eX u (by omega)
    (by omega)
  have hP := toNat_sumN_equiv G P eP u (by omega) (by omega)
  rw [toNat_sumN _ _ (by omega)] at hA hP
  rw [toNat_sumN _ _ (by omega)] at hX
  rw [← hA, ← hX, ← hP]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      have hi2 : i < 2 := Finset.mem_range.mp hi
      have hhi : i < hSize x := by unfold hSize; omega
      have hValue : h ⟨i, hhi⟩ = (eA ⟨i, hi2⟩).1 := by
        calc
          h ⟨i, hhi⟩ = h (Fin.castAdd x ⟨i, hi2⟩) := by
            apply congrArg h
            apply Fin.ext
            rfl
          _ = (eA ⟨i, hi2⟩).1 := by
            change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1)
              (Fin.castAdd x ⟨i, hi2⟩) = _
            exact hLabel_castAdd _ _ _
      rw [coreAt_h h p i hhi]
      simp [hValue, Nat.mod_eq_of_lt hi2]
    · apply Finset.sum_congr rfl
      intro i hi
      have hix : i < x := Finset.mem_range.mp hi
      have hhi : 2 + i < hSize x := by unfold hSize; omega
      have hValue : h ⟨2 + i, hhi⟩ = (eX ⟨i, hix⟩).1 := by
        calc
          h ⟨2 + i, hhi⟩ = h (Fin.natAdd 2 ⟨i, hix⟩) := by
            apply congrArg h
            apply Fin.ext
            rfl
          _ = (eX ⟨i, hix⟩).1 := by
            change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1)
              (Fin.natAdd 2 ⟨i, hix⟩) = _
            exact hLabel_natAdd _ _ _
      rw [coreAt_h h p (2 + i) hhi]
      simp [hValue, Nat.mod_eq_of_lt hix]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi6 : i < 6 := Finset.mem_range.mp hi
    simp [coreAt, hSize, hi6, Nat.mod_eq_of_lt hi6, bitCount]

omit [Fintype V] [DecidableEq V] in
/-- The initial square columns enumerate precisely `A₁∪X=H`. -/
theorem toNat_h_row_hLabel {x : Nat} (hxPos : 0 < x) (hxLe : x ≤ 5)
    (A1 X : Finset V)
    (eA : Fin 2 ≃ {v : V // v ∈ A1})
    (eX : Fin x ≃ {v : V // v ∈ X})
    (u : V) :
    (sumN (hSize x) (fun j ↦ decide
      (G.Adj u (hAt (hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)) j)))).toNat =
      directCount G A1 u + directCount G X u := by
  classical
  let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
  rw [toNat_sumN _ _ (by simp [hSize]; omega)]
  change (∑ i ∈ Finset.range (2 + x), _) = _
  rw [Finset.sum_range_add]
  have hA := toNat_sumN_equiv G A1 eA u (by omega) (by omega)
  have hX := toNat_sumN_equiv G X eX u (by omega) (by omega)
  rw [toNat_sumN _ _ (by omega)] at hA hX
  rw [← hA, ← hX]
  apply congrArg₂ (fun a b : Nat ↦ a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    have hi2 : i < 2 := Finset.mem_range.mp hi
    have hhi : i < hSize x := by simp [hSize]; omega
    have hValue : h ⟨i, hhi⟩ = (eA ⟨i, hi2⟩).1 := by
      change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨i, hhi⟩ = _
      simpa using hLabel_castAdd
        (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨i, hi2⟩
    rw [hAt_of_lt h i hhi, hValue]
    by_cases hAdj : G.Adj u (eA ⟨i, hi2⟩).1 <;>
      simp [bitCount, hAdj, Nat.mod_eq_of_lt hi2]
  · apply Finset.sum_congr rfl
    intro i hi
    have hix : i < x := Finset.mem_range.mp hi
    have hhi : 2 + i < hSize x := by simp [hSize]; omega
    have hValue : h ⟨2 + i, hhi⟩ = (eX ⟨i, hix⟩).1 := by
      change hLabel (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨2 + i, hhi⟩ = _
      simpa using hLabel_natAdd
        (fun j ↦ (eA j).1) (fun j ↦ (eX j).1) ⟨i, hix⟩
    rw [hAt_of_lt h (2 + i) hhi, hValue]
    by_cases hAdj : G.Adj u (eX ⟨i, hix⟩).1 <;>
      simp [bitCount, hAdj, Nat.mod_eq_of_lt hix]

omit [Fintype V] [DecidableEq V] in
/-- Decode the `H`-columns of an encoded core row. -/
theorem toNat_hInternal_coreBits {x : Nat} (hxPos : 0 < x) (hxLe : x ≤ 5)
    (A1 X : Finset V)
    (eA : Fin 2 ≃ {v : V // v ∈ A1})
    (eX : Fin x ≃ {v : V // v ∈ X})
    (p : Fin 6 → V) (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (u : Nat) (hu : u < hSize x) :
    (sumN (hSize x) (arc (coreBits G.Adj hxLe
      (hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)) p t w) u)).toNat =
      directCount G A1
        (hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1) ⟨u, hu⟩) +
      directCount G X
        (hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1) ⟨u, hu⟩) := by
  classical
  let h := hLabel (fun i ↦ (eA i).1) (fun i ↦ (eX i).1)
  rw [toNat_sumN _ _ (by simp [hSize]; omega)]
  rw [← toNat_h_row_hLabel G hxPos hxLe A1 X eA eX (h ⟨u, hu⟩),
    toNat_sumN _ _ (by simp [hSize]; omega)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjH : j < hSize x := Finset.mem_range.mp hj
  rw [arc_coreBits G.Adj hxLe h p t w u j
      (by unfold coreSize; simp [hSize] at hu ⊢; omega)
      (by unfold coreSize; simp [hSize] at hjH ⊢; omega),
    coreAt_h h p u hu, coreAt_h h p j hjH,
    hAt_of_lt h j hjH]

omit [Fintype V] [DecidableEq V] in
theorem trueCount_labelled {n : Nat} (S : Finset V)
    (e : Fin n ≃ {v : V // v ∈ S}) (u : V)
    (hnPos : 0 < n) (hn : n < 256) :
    trueCount n (fun j ↦ decide
      (G.Adj u (e ⟨j % n, Nat.mod_lt _ hnPos⟩).1)) = directCount G S u :=
  trueCount_equiv G S e u hnPos hn

def protectedTargets (C : G.LocalConfiguration) : Finset V := {C.a1} ∪ C.R

theorem disjoint_H_protectedTargets (C : G.LocalConfiguration)
    (hG : G.IsOriented) : Disjoint C.H (protectedTargets G C) := by
  rw [Finset.disjoint_left]
  intro v hvH hvT
  rcases Finset.mem_union.mp hvT with hva1 | hvR
  · have hv : v = C.a1 := Finset.mem_singleton.mp hva1
    subst v
    rcases Finset.mem_union.mp hvH with hvA1 | hvX
    · exact Digraph.LocalConfiguration.a1_notMem_A1 (G := G) C hG.1 hvA1
    · exact Digraph.LocalConfiguration.a1_notMem_X (G := G) C hvX
  · exact (Finset.mem_sdiff.mp hvR).2 (by
      simpa [Digraph.LocalConfiguration.H] using
        Finset.mem_union_left ({C.a1} : Finset V) hvH)

theorem H_union_protectedTargets_eq_A (C : G.LocalConfiguration) :
    C.H ∪ protectedTargets G C = C.A := by
  simpa [Digraph.LocalConfiguration.H, protectedTargets, Finset.union_assoc] using
    Digraph.LocalConfiguration.local_parts_union_R (G := G) C

omit [DecidableEq V] in
theorem outdegree_eq_directCount_of_captured (u : V) (S : Finset V)
    (hCaptured : G.outNeighborFinset u ⊆ S) :
    G.outdegree u = directCount G S u := by
  classical
  unfold Digraph.outdegree directCount CertificateBridge.internalFirstNeighbors
  apply congrArg Finset.card
  ext v
  simp only [Digraph.mem_outNeighborFinset, Finset.mem_filter]
  constructor
  · intro huv
    exact ⟨hCaptured ((Digraph.mem_outNeighborFinset (G := G)).mpr huv), huv⟩
  · exact fun h ↦ h.2

/-- Exact local degree accounting for a vertex of `H`. -/
theorem outdegree_H_eq_blocks (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPB : C.P = C.B) (u : V) (huH : u ∈ C.H) :
    G.outdegree u = directCount G C.A1 u + directCount G C.X u +
      directCount G (protectedTargets G C) u + directCount G C.P u := by
  have hCaptured := Shared.H_outgoingCaptured G C hG hPB u huH
  have hAP : Disjoint C.A C.P := by
    rw [Finset.disjoint_left]
    intro v hvA hvP
    exact (Finset.disjoint_left.mp
      (Digraph.LocalConfiguration.disjoint_A_B (G := G) C)) hvA
        (Digraph.LocalConfiguration.P_subset_B (G := G) C hvP)
  have hA := H_union_protectedTargets_eq_A G C
  have hHX := Digraph.LocalConfiguration.disjoint_A1_X (G := G) C
  rw [outdegree_eq_directCount_of_captured G u (C.A ∪ C.P) hCaptured,
    Shared.directCount_union_of_disjoint G C.A C.P u hAP,
    ← hA,
    Shared.directCount_union_of_disjoint G C.H (protectedTargets G C) u
      (disjoint_H_protectedTargets G C hG),
    Digraph.LocalConfiguration.H,
    Shared.directCount_union_of_disjoint G C.A1 C.X u hHX]

/-- An `A₁` vertex sends no arc to `{a₁}∪R`. -/
theorem directCount_protected_eq_zero_of_mem_A1 (C : G.LocalConfiguration)
    (hG : G.IsOriented) (u : V) (huA1 : u ∈ C.A1) :
    directCount G (protectedTargets G C) u = 0 := by
  apply Nat.eq_zero_of_le_zero
  change (CertificateBridge.internalFirstNeighbors G (protectedTargets G C) u).card ≤ 0
  rw [Nat.le_zero]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨hvT, huv⟩
  rcases Finset.mem_union.mp hvT with hva1 | hvR
  · have hv : v = C.a1 := Finset.mem_singleton.mp hva1
    subst v
    have ha1u : G.Adj C.a1 u := (Finset.mem_filter.mp huA1).2
    exact hG.2 ha1u huv
  · have hvX : v ∈ C.X := by
      apply Finset.mem_inter.mpr
      constructor
      · apply (Digraph.mem_outNeighborFinsetOf (G := G)).mpr
        exact ⟨u, Finset.mem_union_left C.P huA1, huv⟩
      · apply Finset.mem_sdiff.mpr
        refine ⟨Digraph.LocalConfiguration.R_subset_A (G := G) C hvR, ?_⟩
        intro hvParts
        exact (Finset.mem_sdiff.mp hvR).2 (by
          rcases Finset.mem_union.mp hvParts with hvA1 | hva1
          · exact Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hvA1)
          · exact Finset.mem_union_right (C.A1 ∪ C.X) hva1)
    exact (Finset.mem_sdiff.mp hvR).2
      (Finset.mem_union_left {C.a1} (Finset.mem_union_right C.A1 hvX))

/-- Pointwise form of the external-target/root split. -/
theorem directCount_externalTargets (C : G.LocalConfiguration)
    (p : V) (hp : p ∈ C.P) :
    directCount G (externalTargets G C) p =
      directCount G C.Z p + epsilonAt G p C.s := by
  by_cases hReach : ∃ q ∈ C.P, G.Adj q C.s
  · have hDisjoint : Disjoint C.Z {C.s} := by
      rw [Finset.disjoint_left]
      intro v hvZ hvs
      exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C
        (Finset.mem_singleton.mp hvs ▸ hvZ)
    rw [externalTargets, rootSecondFinset, if_pos hReach,
      Shared.directCount_union_of_disjoint G C.Z {C.s} p hDisjoint,
      Shared.directCount_singleton]
  · have hps : ¬G.Adj p C.s := fun h ↦ hReach ⟨p, hp, h⟩
    rw [externalTargets, rootSecondFinset, if_neg hReach, Finset.union_empty]
    simp [epsilonAt, hps]

/-- Exact local degree accounting for a vertex of `P`. -/
theorem outdegree_P_eq_blocks (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hPB : C.P = C.B) (p : V) (hp : p ∈ C.P) :
    G.outdegree p = directCount G (externalTargets G C) p +
      directCount G C.A1 p + directCount G C.X p + directCount G C.P p := by
  have hCaptured := Shared.outgoingCaptured_of_p_eq_B G C hG hPB p hp
  have hZs : Disjoint C.Z {C.s} := by
    rw [Finset.disjoint_left]
    intro v hvZ hvs
    exact Digraph.LocalConfiguration.s_notMem_Z (G := G) C
      (Finset.mem_singleton.mp hvs ▸ hvZ)
  have hZsH : Disjoint (C.Z ∪ {C.s}) C.H := by
    rw [Finset.disjoint_left]
    intro v hvZs hvH
    rcases Finset.mem_union.mp hvZs with hvZ | hvs
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hvZ hvH
    · have : v = C.s := Finset.mem_singleton.mp hvs
      subst v
      exact Digraph.LocalConfiguration.s_notMem_H (G := G) C hG.1 hvH
  have hAllP : Disjoint (C.Z ∪ {C.s} ∪ C.H) C.P := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvP
    rcases Finset.mem_union.mp hvLeft with hvZs | hvH
    · rcases Finset.mem_union.mp hvZs with hvZ | hvs
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hvZ hvP
      · have : v = C.s := Finset.mem_singleton.mp hvs
        subst v
        exact Digraph.LocalConfiguration.s_notMem_P (G := G) C hvP
    · exact (Finset.disjoint_left.mp
        (Digraph.LocalConfiguration.disjoint_H_P (G := G) C)) hvH hvP
  have hHX := Digraph.LocalConfiguration.disjoint_A1_X (G := G) C
  rw [outdegree_eq_directCount_of_captured G p _ hCaptured,
    Shared.directCount_union_of_disjoint G _ C.P p hAllP,
    Shared.directCount_union_of_disjoint G _ C.H p hZsH,
    Shared.directCount_union_of_disjoint G C.Z {C.s} p hZs,
    Shared.directCount_singleton,
    ← directCount_externalTargets G C p hp,
    Digraph.LocalConfiguration.H,
    Shared.directCount_union_of_disjoint G C.A1 C.X p hHX]
  omega

omit [Fintype V] in
omit [DecidableEq V] in
/-- Three disjoint labelled blocks inject into any finset containing their selected targets. -/
theorem three_trueCounts_le_card {n₁ n₂ n₃ : Nat}
    (f₁ f₂ f₃ : Nat → Bool)
    (label₁ : Fin n₁ → V) (label₂ : Fin n₂ → V) (label₃ : Fin n₃ → V)
    (S : Finset V)
    (hInjective : Function.Injective (Sum.elim label₁
      (Sum.elim label₂ label₃) : Fin n₁ ⊕ (Fin n₂ ⊕ Fin n₃) → V))
    (hMem₁ : ∀ i : Fin n₁, f₁ i = true → label₁ i ∈ S)
    (hMem₂ : ∀ i : Fin n₂, f₂ i = true → label₂ i ∈ S)
    (hMem₃ : ∀ i : Fin n₃, f₃ i = true → label₃ i ∈ S) :
    trueCount n₁ f₁ + trueCount n₂ f₂ + trueCount n₃ f₃ ≤ S.card := by
  classical
  let label : Fin n₁ ⊕ (Fin n₂ ⊕ Fin n₃) → V :=
    Sum.elim label₁ (Sum.elim label₂ label₃)
  let selected : Finset (Fin n₁ ⊕ (Fin n₂ ⊕ Fin n₃)) :=
    (Finset.univ.filter fun q ↦ match q with
      | Sum.inl i => f₁ i = true
      | Sum.inr (Sum.inl i) => f₂ i = true
      | Sum.inr (Sum.inr i) => f₃ i = true)
  have hCard : selected.card =
      trueCount n₁ f₁ + trueCount n₂ f₂ + trueCount n₃ f₃ := by
    rw [trueCount_eq_filter_fin, trueCount_eq_filter_fin,
      trueCount_eq_filter_fin]
    dsimp [selected]
    simp only [Finset.card_filter]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [add_assoc]
    apply congrArg₂ (fun a b : Nat ↦ a + b)
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hfi : f₁ i = true <;> simp [hfi]
    · apply congrArg₂ (fun a b : Nat ↦ a + b)
      · apply Finset.sum_congr rfl
        intro i hi
        by_cases hfi : f₂ i = true <;> simp [hfi]
      · apply Finset.sum_congr rfl
        intro i hi
        by_cases hfi : f₃ i = true <;> simp [hfi]
  have hImageCard : (selected.image label).card = selected.card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hInjective hab
  have hImageSubset : selected.image label ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨q, hq, rfl⟩
    have hSelected := (Finset.mem_filter.mp hq).2
    rcases q with i | (i | i)
    · exact hMem₁ i hSelected
    · exact hMem₂ i hSelected
    · exact hMem₃ i hSelected
  rw [← hCard, ← hImageCard]
  exact Finset.card_le_card hImageSubset

omit [Fintype V] [DecidableEq V] in
/-- The core square row counts arcs into `H∪P`. -/
theorem toNat_core_row {x : Nat} (hxLe : x ≤ 5)
    (H : Finset V) (P : Finset V)
    (eH : Fin (hSize x) ≃ {v : V // v ∈ H})
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (u : V) :
    (sumN (coreSize x) (fun j ↦ decide
      (G.Adj u (coreAt (fun i ↦ (eH i).1) (fun i ↦ (eP i).1) j)))).toNat =
      directCount G H u + directCount G P u := by
  rw [toNat_sumN _ _ (by simp [coreSize]; omega)]
  have hSizeEq : coreSize x = hSize x + 6 := by
    simp [coreSize, hSize]
    omega
  rw [hSizeEq, Finset.sum_range_add]
  have hH := toNat_sumN_equiv G H eH u (by simp [hSize])
    (by simp [hSize]; omega)
  rw [toNat_sumN _ _ (by simp [hSize]; omega)] at hH
  have hP := toNat_sumN_equiv G P eP u (by omega) (by omega)
  rw [toNat_sumN _ _ (by omega)] at hP
  rw [← hH, ← hP]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < hSize x := Finset.mem_range.mp hi
    simp [coreAt, hi', hAt, Nat.mod_eq_of_lt hi', bitCount]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < 6 := Finset.mem_range.mp hi
    simp [coreAt, hSize, pAt, Nat.mod_eq_of_lt hi', bitCount]

omit [Fintype V] [DecidableEq V] in
/-- Decode the two cross-block totals used by the tight `x=3` certificate. -/
theorem toNat_totalHToP_coreBits {x : Nat} (hxLe : x ≤ 5)
    (H P : Finset V)
    (eH : Fin (hSize x) ≃ {v : V // v ∈ H})
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V) :
    (totalHToP (coreBits G.Adj hxLe (fun i ↦ (eH i).1)
      (fun i ↦ (eP i).1) t w)).toNat = edgeCount G H P := by
  classical
  let bits := coreBits G.Adj hxLe (fun i ↦ (eH i).1) (fun i ↦ (eP i).1) t w
  have hRow : ∀ (i : Nat) (hi : i < hSize x),
      (sumN 6 (fun j ↦ arc bits i (hSize x + j))).toNat =
        directCount G P (eH ⟨i, hi⟩).1 := by
    intro i hi
    rw [toNat_sumN _ _ (by omega), ← toNat_sumN_equiv G P eP (eH ⟨i, hi⟩).1
      (by omega) (by omega), toNat_sumN _ _ (by omega)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj6 := Finset.mem_range.mp hj
    rw [arc_coreBits G.Adj hxLe (fun q ↦ (eH q).1) (fun q ↦ (eP q).1)
      t w i (hSize x + j) (by unfold coreSize; simp [hSize] at hi ⊢; omega)
      (by unfold coreSize; simp [hSize] at hj6 ⊢; omega),
      coreAt_h (fun q ↦ (eH q).1) (fun q ↦ (eP q).1) i hi,
      coreAt_p (fun q ↦ (eH q).1) (fun q ↦ (eP q).1) j hj6]
    simp [bitCount, Nat.mod_eq_of_lt hj6]
  have hEdge := edgeCount_eq_sum_fin G H P eH
  have hRowsEq : (∑ i ∈ Finset.range (hSize x),
      (sumN 6 (fun j ↦ arc bits i (hSize x + j))).toNat) = edgeCount G H P := by
    rw [hEdge, ← Fin.sum_univ_eq_sum_range
      (fun i ↦ (sumN 6 (fun j ↦ arc bits i (hSize x + j))).toNat) (hSize x)]
    apply Fintype.sum_congr
    intro i
    exact hRow i.val i.isLt
  have hTotalLt : (∑ i ∈ Finset.range (hSize x),
      (sumN 6 (fun j ↦ arc bits i (hSize x + j))).toNat) < 256 := by
    rw [hRowsEq]
    have hCap := Shared.edgeCount_le_card_mul_card G H P
    have hHCard : H.card = hSize x := by
      simpa using (Fintype.card_congr eH).symm
    have hPCard : P.card = 6 := by
      simpa using (Fintype.card_congr eP).symm
    calc
      edgeCount G H P ≤ H.card * P.card := hCap
      _ = hSize x * 6 := by rw [hHCard, hPCard]
      _ < 256 := by simp [hSize]; omega
  rw [totalHToP, toNat_sumCountsN _ _ hTotalLt]
  exact hRowsEq

omit [Fintype V] [DecidableEq V] in
theorem toNat_totalPToH_coreBits {x : Nat} (hxLe : x ≤ 5)
    (H P : Finset V)
    (eH : Fin (hSize x) ≃ {v : V // v ∈ H})
    (eP : Fin 6 ≃ {v : V // v ∈ P})
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V) :
    (totalPToH (coreBits G.Adj hxLe (fun i ↦ (eH i).1)
      (fun i ↦ (eP i).1) t w)).toNat = edgeCount G P H := by
  classical
  let bits := coreBits G.Adj hxLe (fun i ↦ (eH i).1) (fun i ↦ (eP i).1) t w
  have hRow : ∀ (i : Nat) (hi : i < 6),
      (sumN (hSize x) (fun j ↦ arc bits (hSize x + i) j)).toNat =
        directCount G H (eP ⟨i, hi⟩).1 := by
    intro i hi
    rw [toNat_sumN _ _ (by simp [hSize]; omega),
      ← toNat_sumN_equiv G H eH (eP ⟨i, hi⟩).1 (by simp [hSize])
        (by simp [hSize]; omega), toNat_sumN _ _ (by simp [hSize]; omega)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjH := Finset.mem_range.mp hj
    rw [arc_coreBits G.Adj hxLe (fun q ↦ (eH q).1) (fun q ↦ (eP q).1)
      t w (hSize x + i) j (by unfold coreSize; simp [hSize] at hi ⊢; omega)
      (by unfold coreSize; simp [hSize] at hjH ⊢; omega),
      coreAt_p (fun q ↦ (eH q).1) (fun q ↦ (eP q).1) i hi,
      coreAt_h (fun q ↦ (eH q).1) (fun q ↦ (eP q).1) j hjH]
    simp [bitCount, Nat.mod_eq_of_lt hjH]
  have hEdge := edgeCount_eq_sum_fin G P H eP
  have hRowsEq : (∑ i ∈ Finset.range 6,
      (sumN (hSize x) (fun j ↦ arc bits (hSize x + i) j)).toNat) = edgeCount G P H := by
    rw [hEdge, ← Fin.sum_univ_eq_sum_range
      (fun i ↦ (sumN (hSize x) (fun j ↦ arc bits (hSize x + i) j)).toNat) 6]
    apply Fintype.sum_congr
    intro i
    exact hRow i.val i.isLt
  have hTotalLt : (∑ i ∈ Finset.range 6,
      (sumN (hSize x) (fun j ↦ arc bits (hSize x + i) j)).toNat) < 256 := by
    rw [hRowsEq]
    have hCap := Shared.edgeCount_le_card_mul_card G P H
    have hHCard : H.card = hSize x := by
      simpa using (Fintype.card_congr eH).symm
    have hPCard : P.card = 6 := by
      simpa using (Fintype.card_congr eP).symm
    calc
      edgeCount G P H ≤ P.card * H.card := hCap
      _ = 6 * hSize x := by rw [hHCard, hPCard]
      _ < 256 := by simp [hSize]; omega
  rw [totalPToH, toNat_sumCountsN _ _ hTotalLt]
  exact hRowsEq

/-- Every target counted by the three retained reachability blocks is a
genuine strict second outneighbor. -/
theorem representedSecondCount_le_secondOutdegree {x : Nat}
    (hxLe : x ≤ 5)
    (h : Fin (hSize x) → V) (p : Fin 6 → V)
    (t : Fin (tSize x) → V) (w : Fin (wSize x) → V)
    (u : Nat) (hu : u < 2)
    (hLabels : Function.Injective (Sum.elim
      (fun i : Fin (coreSize x) ↦ coreAt h p i)
      (Sum.elim t w) :
        Fin (coreSize x) ⊕ (Fin (tSize x) ⊕ Fin (wSize x)) → V))
    (hNoDirectT : ∀ j : Fin (tSize x),
      ¬G.Adj (h ⟨u, by simp [hSize]; omega⟩) (t j))
    (hNoDirectW : ∀ j : Fin (wSize x),
      ¬G.Adj (h ⟨u, by simp [hSize]; omega⟩) (w j)) :
    (representedSecondCount (coreBits G.Adj hxLe h p t w) u).toNat ≤
      G.secondOutdegree (h ⟨u, by simp [hSize]; omega⟩) := by
  let bits := coreBits G.Adj hxLe h p t w
  let source : V := h ⟨u, by simp [hSize]; omega⟩
  have huCore : u < coreSize x := by unfold coreSize; omega
  have hSource : coreAt h p u = source := by
    simp [source, coreAt_h h p u (by simp [hSize]; omega)]
  rw [toNat_representedSecondCount hxLe bits u]
  change _ ≤ (G.secondOutNeighborFinset source).card
  apply three_trueCounts_le_card
    (label₁ := fun i : Fin (coreSize x) ↦ coreAt h p i)
    (label₂ := t) (label₃ := w) (hInjective := hLabels)
  · intro target hSelected
    have htCore : target.val < coreSize x := target.isLt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hSelected
    rcases hSelected with ⟨⟨hTargetNe, hNotArc⟩, hReached⟩
    change (!arc (coreBits G.Adj hxLe h p t w) u target) = true at hNotArc
    change reachedInCore (coreBits G.Adj hxLe h p t w) u target = true at hReached
    rw [reachedInCore, anyN_eq_true_iff] at hReached
    rcases hReached with ⟨middle, hmCore, hm⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    have hArcs : G.Adj source (coreAt h p middle) ∧
        G.Adj (coreAt h p middle) (coreAt h p target) := by
      rcases hm with ⟨⟨⟨_, _⟩, hum⟩, hmv⟩
      rw [arc_coreBits G.Adj hxLe h p t w u middle huCore hmCore,
        decide_eq_true_eq, hSource] at hum
      rw [arc_coreBits G.Adj hxLe h p t w middle target hmCore htCore,
        decide_eq_true_eq] at hmv
      exact ⟨hum, hmv⟩
    have hNotDirect : ¬G.Adj source (coreAt h p target) := by
      intro hAdj
      have : arc bits u target = true := by
        rw [arc_coreBits G.Adj hxLe h p t w u target huCore htCore,
          decide_eq_true_eq, hSource]
        exact hAdj
      change arc (coreBits G.Adj hxLe h p t w) u target = true at this
      simp [this] at hNotArc
    have hTargetSource : coreAt h p target ≠ source := by
      intro hEq
      have hIndex := hLabels (show
        Sum.elim (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w)
            (Sum.inl target) =
          Sum.elim (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w)
            (Sum.inl ⟨u, huCore⟩) by
          simpa [hSource] using hEq)
      exact hTargetNe (Fin.ext_iff.mp (Sum.inl.inj hIndex))
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨coreAt h p middle, hArcs⟩, hNotDirect, hTargetSource⟩
  · intro target hReached
    change reachedT (coreBits G.Adj hxLe h p t w) u target = true at hReached
    rw [reachedT, anyN_eq_true_iff] at hReached
    rcases hReached with ⟨middle, hmX, hm⟩
    simp only [Bool.and_eq_true] at hm
    have hArcs : G.Adj source (h ⟨2 + middle, by simp [hSize]; omega⟩) ∧
        G.Adj (h ⟨2 + middle, by simp [hSize]; omega⟩) (t target) := by
      rcases hm with ⟨hum, hmv⟩
      rw [arc_coreBits G.Adj hxLe h p t w u (2 + middle)
          huCore (by unfold coreSize; omega),
        decide_eq_true_eq, hSource,
        coreAt_h h p (2 + middle) (by simp [hSize]; omega)] at hum
      rw [xToT_coreBits G.Adj hxLe h p t w middle target hmX target.isLt,
        decide_eq_true_eq] at hmv
      exact ⟨hum, hmv⟩
    have hTargetSource : t target ≠ source := by
      intro hEq
      have hIndex := hLabels (show
        Sum.elim (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w)
            (Sum.inr (Sum.inl target)) =
          Sum.elim (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w)
            (Sum.inl ⟨u, huCore⟩) by
          simpa [hSource] using hEq)
      exact Sum.inr_ne_inl hIndex
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨_, hArcs⟩, hNoDirectT target, hTargetSource⟩
  · intro target hReached
    change reachedW (coreBits G.Adj hxLe h p t w) u target = true at hReached
    rw [reachedW, anyN_eq_true_iff] at hReached
    rcases hReached with ⟨middle, hmP, hm⟩
    simp only [Bool.and_eq_true] at hm
    have hArcs : G.Adj source (p ⟨middle, hmP⟩) ∧
        G.Adj (p ⟨middle, hmP⟩) (w target) := by
      rcases hm with ⟨hum, hmv⟩
      rw [arc_coreBits G.Adj hxLe h p t w u (hSize x + middle)
          huCore (by unfold coreSize; unfold hSize; omega),
        decide_eq_true_eq, hSource, coreAt_p h p middle hmP] at hum
      rw [pToW_coreBits G.Adj hxLe h p t w middle target hmP target.isLt,
        decide_eq_true_eq] at hmv
      exact ⟨hum, hmv⟩
    have hTargetSource : w target ≠ source := by
      intro hEq
      have hIndex := hLabels (show
        Sum.elim (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w)
            (Sum.inr (Sum.inr target)) =
          Sum.elim (fun i : Fin (coreSize x) ↦ coreAt h p i) (Sum.elim t w)
            (Sum.inl ⟨u, huCore⟩) by
          simpa [hSource] using hEq)
      exact Sum.inr_ne_inl hIndex
    rw [Digraph.mem_secondOutNeighborFinset,
      Digraph.mem_secondOutNeighborSet]
    exact ⟨⟨_, hArcs⟩, hNoDirectW target, hTargetSource⟩

end SeymourEight.BSixKTwoCoreGraphBridge
