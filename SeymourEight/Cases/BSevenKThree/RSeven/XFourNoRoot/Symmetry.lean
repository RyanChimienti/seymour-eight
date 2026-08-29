import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.Assembly
import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.SymmetryDefs

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Symmetry

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts
open SeymourEight.BSevenKThree.RSeven.XFourNoRoot.SymmetricCore

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem incomingCount_le_card (S : Finset V) (v : V) :
    Labels.incomingCount G S v ≤ S.card := by
  classical
  simp only [Labels.incomingCount]
  calc
    (∑ u ∈ S, if G.Adj u v then 1 else 0) ≤ ∑ _u ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro u hu
      split <;> omega
    _ = S.card := by simp

set_option linter.flexible false in
theorem pIn_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (p : Nat) (hp : p < 7) :
    (pIn (graphBits G L) p).toNat =
      Labels.incomingCount G C.P (L.p ⟨p, hp⟩).1 := by
  rw [pIn, toNat_count_eq_fin_sum 7 _ (by omega), Labels.incomingCount,
    sum_finset_eq_sum_fin C.P L.p]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pArc_coreBits
    G.Adj _ _ _ q p q.isLt hp]
  by_cases heq : q.val = p
  · have hFin : q = ⟨p, hp⟩ := Fin.ext heq
    subst q
    simp
    exact hG.1 _
  · simp [heq]

theorem hToPIn_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hHCard : C.H.card = 7) (p : Nat) (hp : p < 7) :
    (hToPIn (graphBits G L) p).toNat =
      Labels.incomingCount G C.H (L.p ⟨p, hp⟩).1 := by
  rw [hToPIn, toNat_count_eq_fin_sum 7 _ (by omega), Labels.incomingCount,
    sum_finset_eq_sum_fin C.H (hLabelEquiv G C L hHCard)]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [hLabelEquiv_val]
  rw [SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.hToP_coreBits
    G.Adj _ _ _ h p h.isLt hp]
  simp

set_option linter.flexible false in
theorem pInvariantKey_toNat (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (p : Nat) (hp : p < 7) :
    (SymmetricCore.pInvariantKey (graphBits G L) p).toNat =
      Labels.pInvariantKey G C (L.p ⟨p, hp⟩).1 := by
  have hP := pOut_toNat G C L hG p hp
  have hH := pHOut_toNat G C L hG hHCard p hp
  have hZ := pZOut_toNat G C L hG (by omega) p hp
  have hPI := pIn_toNat G C L hG p hp
  have hHI := hToPIn_toNat G C L hHCard p hp
  simp [SymmetricCore.pInvariantKey, Labels.pInvariantKey,
    BitVec.toNat_add, BitVec.toNat_mul]
  rw [hP, hH, hZ, hPI, hHI]
  have hPCard : C.P.card = 7 := by
    simpa using (Fintype.card_congr L.p).symm
  have hZCard : (externalTargets G C).card = 5 := by
    simpa using (Fintype.card_congr L.z).symm
  have hpLe : Shared.directCount G C.P (L.p ⟨p, hp⟩).1 ≤ C.P.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hhLe : Shared.directCount G C.H (L.p ⟨p, hp⟩).1 ≤ C.H.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hzLe : Shared.directCount G (externalTargets G C)
      (L.p ⟨p, hp⟩).1 ≤ (externalTargets G C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hipLe := incomingCount_le_card G C.P (L.p ⟨p, hp⟩).1
  have hihLe := incomingCount_le_card G C.H (L.p ⟨p, hp⟩).1
  omega

@[simp] theorem hToP_graphBits (C : G.LocalConfiguration) (L : Labels G 5 C)
    (h p : Nat) (hh : h < 7) (hp : p < 7) :
    hToP (graphBits G L) h p =
      decide (G.Adj (L.a ⟨h + 1, by omega⟩).1 (L.p ⟨p, hp⟩).1) := by
  exact SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.hToP_coreBits
    G.Adj _ _ _ h p hh hp

@[simp] theorem pToH_graphBits (C : G.LocalConfiguration) (L : Labels G 5 C)
    (p h : Nat) (hp : p < 7) (hh : h < 7) :
    pToH (graphBits G L) p h =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨h + 1, by omega⟩).1) := by
  exact SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToH_coreBits
    G.Adj _ _ _ p h hp hh

@[simp] theorem pToZ_graphBits (C : G.LocalConfiguration) (L : Labels G 5 C)
    (p z : Nat) (hp : p < 7) (hz : z < 5) :
    pToZ (graphBits G L) p z =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  exact SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Encoding.pToZ_coreBits
    G.Adj _ _ _ p z hp hz hz

theorem hIncidenceCode_eq (C : G.LocalConfiguration) (L : Labels G 5 C)
    (h : Nat) (hh : h < 7) :
    SymmetricCore.hIncidenceCode (graphBits G L) h =
      Labels.hIncidenceCode G (fun i => (L.p i).1)
        (L.a ⟨h + 1, by omega⟩).1 := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  simp only [SymmetricCore.hIncidenceCode, Labels.hIncidenceCode,
    BitVec.getLsbD_ofFnLE, hi, ↓reduceDIte]
  by_cases hi7 : i < 7
  · simp only [hi7, ↓reduceDIte]
    exact hToP_graphBits G C L h i hh hi7
  · simp only [hi7, ↓reduceDIte]
    exact pToH_graphBits G C L (i - 7) h (by omega) hh

theorem zIncidenceCode_eq (C : G.LocalConfiguration) (L : Labels G 5 C)
    (z : Nat) (hz : z < 5) :
    SymmetricCore.zIncidenceCode (graphBits G L) z =
      Labels.zIncidenceCode G (fun i => (L.p i).1) (L.z ⟨z, hz⟩).1 := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  simp only [SymmetricCore.zIncidenceCode, Labels.zIncidenceCode,
    BitVec.getLsbD_ofFnLE, hi, ↓reduceDIte]
  exact pToZ_graphBits G C L i z hi hz

theorem hInvariantKey_eq (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (h : Nat) (hh : h < 7) :
    SymmetricCore.hInvariantKey (graphBits G L) h =
      Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨h + 1, by omega⟩).1 := by
  have hP := aPOut_toNat G C L hG (by omega) (h + 1) (by omega)
  have hA := aOut_toNat G C L hG (by omega) (h + 1) (by omega)
  have hPLe : Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1 ≤ C.P.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hALe : Shared.directCount G C.A (L.a ⟨h + 1, by omega⟩).1 ≤ C.A.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hPCard : C.P.card = 7 := by simpa using (Fintype.card_congr L.p).symm
  have hACard : C.A.card = 8 := by simpa using (Fintype.card_congr L.a).symm
  have hPBV : aPOut (graphBits G L) (h + 1) =
      BitVec.ofNat 8 (Shared.directCount G C.P (L.a ⟨h + 1, by omega⟩).1) := by
    apply BitVec.eq_of_toNat_eq
    simp [hP]
    omega
  have hABV : aOut (graphBits G L) (h + 1) =
      BitVec.ofNat 8 (Shared.directCount G C.A (L.a ⟨h + 1, by omega⟩).1) := by
    apply BitVec.eq_of_toNat_eq
    simp [hA]
    omega
  simp [SymmetricCore.hInvariantKey, Labels.hInvariantKey, hPBV, hABV,
    hIncidenceCode_eq G C L h hh]

theorem orderedP_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hOrder : ∀ q : Fin 6,
      Labels.pInvariantKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pInvariantKey G C (L.p ⟨q.val, by omega⟩).1) :
    SymmetricCore.orderedP (graphBits G L) = true := by
  rw [SymmetricCore.orderedP, all_eq_true_iff]
  intro p hp
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [pInvariantKey_toNat G C L hG hHCard (p + 1) (by omega),
    pInvariantKey_toNat G C L hG hHCard p (by omega)]
  exact hOrder ⟨p, hp⟩

theorem orderedStructuralClasses_true (C : G.LocalConfiguration)
    (L : Labels G 5 C) (hG : G.IsOriented)
    (hAOneOrder : ∀ q : Fin 2,
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 2, by omega⟩).1).toNat ≤
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 1, by omega⟩).1).toNat)
    (hXOrder : ∀ q : Fin 3,
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 5, by omega⟩).1).toNat ≤
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 4, by omega⟩).1).toNat) :
    SymmetricCore.orderedStructuralClasses (graphBits G L) = true := by
  simp only [SymmetricCore.orderedStructuralClasses, Bool.and_eq_true, all_eq_true_iff,
    BitVec.ule_eq_decide, decide_eq_true_eq]
  constructor
  · intro h hh
    rw [hInvariantKey_eq G C L hG (h + 1) (by omega),
      hInvariantKey_eq G C L hG h (by omega)]
    exact hAOneOrder ⟨h, hh⟩
  · intro h hh
    rw [hInvariantKey_eq G C L hG (h + 4) (by omega),
      hInvariantKey_eq G C L hG (h + 3) (by omega)]
    exact hXOrder ⟨h, hh⟩

theorem orderedZ_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hOrder : ∀ q : Fin 4,
      (Labels.zIncidenceCode G (fun i => (L.p i).1)
        (L.z ⟨q.val + 1, by omega⟩).1).toNat ≤
      (Labels.zIncidenceCode G (fun i => (L.p i).1)
        (L.z ⟨q.val, by omega⟩).1).toNat) :
    SymmetricCore.orderedZ (graphBits G L) = true := by
  rw [SymmetricCore.orderedZ, all_eq_true_iff]
  intro z hz
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
  rw [zIncidenceCode_eq G C L (z + 1) (by omega),
    zIncidenceCode_eq G C L z (by omega)]
  exact hOrder ⟨z, hz⟩

theorem ordered_true (C : G.LocalConfiguration) (L : Labels G 5 C)
    (hG : G.IsOriented) (hHCard : C.H.card = 7)
    (hPOrder : ∀ q : Fin 6,
      Labels.pInvariantKey G C (L.p ⟨q.val + 1, by omega⟩).1 ≤
        Labels.pInvariantKey G C (L.p ⟨q.val, by omega⟩).1)
    (hAOneOrder : ∀ q : Fin 2,
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 2, by omega⟩).1).toNat ≤
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 1, by omega⟩).1).toNat)
    (hXOrder : ∀ q : Fin 3,
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 5, by omega⟩).1).toNat ≤
      (Labels.hInvariantKey G C (fun i => (L.p i).1)
        (L.a ⟨q.val + 4, by omega⟩).1).toNat)
    (hZOrder : ∀ q : Fin 4,
      (Labels.zIncidenceCode G (fun i => (L.p i).1)
        (L.z ⟨q.val + 1, by omega⟩).1).toNat ≤
      (Labels.zIncidenceCode G (fun i => (L.p i).1)
        (L.z ⟨q.val, by omega⟩).1).toNat) :
    SymmetricCore.ordered (graphBits G L) = true := by
  simp only [SymmetricCore.ordered, Bool.and_eq_true]
  exact ⟨⟨orderedP_true G C L hG hHCard hPOrder,
    orderedStructuralClasses_true G C L hG hAOneOrder hXOrder⟩,
    orderedZ_true G C L hZOrder⟩

theorem canonical_ordered_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0)
    (hZCard : (externalTargets G C).card = 5)
    (hHCard : C.H.card = 7) :
    let L := Labels.canonicalLabels G 5 C hPCard hACard hA1Card hXCard hRCard hZCard
    SymmetricCore.ordered (graphBits G L) = true := by
  dsimp only
  apply ordered_true G C _ hG hHCard
  · exact Labels.canonicalLabels_p_order G 5 C hPCard hACard hA1Card hXCard
      hRCard hZCard
  · exact Labels.canonicalLabels_aOne_order G 5 C hPCard hACard hA1Card hXCard
      hRCard hZCard
  · exact Labels.canonicalLabels_x_order G 5 C hPCard hACard hA1Card hXCard
      hRCard hZCard
  · exact Labels.canonicalLabels_z_order G 5 C hPCard hACard hA1Card hXCard
      hRCard hZCard

theorem canonical_symmetricCore_true (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hPB : C.P = C.B)
    (hPivot : IsMinimalPivot G C) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hk : C.k = 3) (hNoSeymour : ¬G.HasSeymourVertex)
    (hRootDegree : G.outdegree C.s = 8)
    (hPCard : C.P.card = 7) (hACard : C.A.card = 8)
    (hA1Card : C.A1.card = 3) (hXCard : C.X.card = 4)
    (hRCard : C.R.card = 0)
    (hZCard : (externalTargets G C).card = 5)
    (hHCard : C.H.card = 7) :
    let L := Labels.canonicalLabels G 5 C hPCard hACard hA1Card hXCard hRCard hZCard
    SymmetricCore.symmetricCore (graphBits G L) = true := by
  dsimp only
  simp only [SymmetricCore.symmetricCore, Bool.and_eq_true]
  exact ⟨Assembly.commonCore_true G C _ hG hPB hPivot hMin hk hNoSeymour
      hRootDegree hA1Card hHCard,
    canonical_ordered_true G C hG hPCard hACard hA1Card hXCard hRCard
      hZCard hHCard⟩

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Symmetry
