import SeymourEight.Cases.BSevenKThree.RSeven.XFourNoRoot.Assembly

set_option linter.style.header false

/-!
# Graph bridge for the three-target no-root row

Padding the three actual `Z` columns by two zero columns makes at least
fourteen of the thirty-five padded `P → Z` incidences missing.  The aggregate
degree bound gives at most twelve, so this row needs no case certificate.
-/

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.ThreeBridge

open Shared Shared.FiniteCore Labels Encoding Core GraphFacts

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem pZOut_five_eq_three (bits : Encoding)
    (hInactive : inactiveZZero 3 bits = true) (p : Nat) (hp : p < 7) :
    pZOut 5 bits p = pZOut 3 bits p := by
  simp only [inactiveZZero, all_eq_true_iff] at hInactive
  have hThree : pToZ bits p 3 = false := by
    simpa using hInactive p hp 0 (by omega)
  have hFour : pToZ bits p 4 = false := by
    simpa using hInactive p hp 1 (by omega)
  simp [pZOut, count, hThree, hFour, bitCount]

theorem pMinimumDegree_five_of_three (bits : Encoding)
    (hInactive : inactiveZZero 3 bits = true)
    (hMin : pMinimumDegree 3 bits = true) :
    pMinimumDegree 5 bits = true := by
  simp only [pMinimumDegree, all_eq_true_iff] at hMin ⊢
  intro p hp
  rw [pZOut_five_eq_three bits hInactive p hp]
  exact hMin p hp

theorem externalMissing_ge_fourteen (bits : Encoding)
    (hInactive : inactiveZZero 3 bits = true) :
    14 ≤ (externalMissing 5 bits).toNat := by
  have hRow : ∀ p < 7, (pZOut 5 bits p).toNat ≤ 3 := by
    intro p hp
    rw [pZOut_five_eq_three bits hInactive p hp, pZOut,
      toNat_count 3 _ (by omega)]
    calc
      (∑ i ∈ Finset.range 3, (bitCount (pToZ bits p i)).toNat) ≤
          ∑ _i ∈ Finset.range 3, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases pToZ bits p i <;> decide
      _ = 3 := by simp
  have hSum : (∑ i ∈ Finset.range 7, (pZOut 5 bits i).toNat) ≤ 21 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range 7, 3 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hRow i (Finset.mem_range.mp hi)
      _ = 21 := by simp
  have hTotal : (totalPToZ 5 bits).toNat =
      ∑ i ∈ Finset.range 7, (pZOut 5 bits i).toNat := by
    rw [totalPToZ, Assembly.toNat_sumCount,
      Nat.mod_eq_of_lt (hSum.trans_lt (by omega))]
  rw [externalMissing, BitVec.toNat_sub, hTotal]
  norm_num [BitVec.toNat_ofNat]
  omega

theorem impossibleAt
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 4)
    (hZCard : (externalTargets G C).card = 3) : False := by
  have hPCard : C.P.card = 7 := by
    change C.P.card = 7 at hr
    exact hr
  have hPB : C.P = C.B := by
    apply Finset.eq_of_subset_of_card_le
      (Digraph.LocalConfiguration.P_subset_B (G := G) C)
    omega
  have hACard : C.A.card = 8 := by
    simpa [Digraph.LocalConfiguration.A, Digraph.outdegree] using hRootDegree
  have hA1Card : C.A1.card = 3 := by
    change C.A1.card = 3 at hk
    exact hk
  have hXCard : C.X.card = 4 := by
    change C.X.card = 4 at hx
    exact hx
  have hRCard : C.R.card = 0 := by
    have hR := BSixKThree.card_R_eq_four_sub_x G C hG hRootDegree hk
    omega
  have hHCard : C.H.card = 7 := by
    have hH := BSixKThree.H_card_eq_three_add_x G C hk
    omega
  let L := Labels.arbitraryLabels G 3 C hPCard hACard hA1Card hXCard hRCard hZCard
  let bits := graphBits G L
  have hOrA : orientedA bits = true :=
    Assembly.orientedA_true G C L hG (by omega)
  have hOrP : orientedP bits = true := Assembly.orientedP_true G C L hG
  have hOrPH : orientedPH bits = true := Assembly.orientedPH_true G C L hG
  have hInactive : inactiveZZero 3 bits = true :=
    Assembly.inactiveZZero_true G C L (by omega)
  have hAMin : aMinimumAndDegree bits = true :=
    Assembly.aMinimumAndDegree_true G C L hG hPB hPivot hMin hk (by omega)
  have hPMinThree : pMinimumDegree 3 bits = true :=
    Assembly.pMinimumDegree_true G C L hG hPB hHCard hMin (by omega)
  have hPMinFive : pMinimumDegree 5 bits = true :=
    pMinimumDegree_five_of_three bits hInactive hPMinThree
  have hDual : degreeAndDualConditions bits = true :=
    degreeAndDual_of_local bits hOrA hOrPH hAMin
  have hUpper : (externalMissing 5 bits).toNat ≤ 12 := by
    have h := externalMissing_le_twelve bits hOrA hOrP hAMin hPMinFive hDual
    simpa [BitVec.ule_eq_decide] using h
  have hLower : 14 ≤ (externalMissing 5 bits).toNat :=
    externalMissing_ge_fourteen bits hInactive
  omega

theorem impossible
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 4)
    (hNoRoot : epsilonS G C = 0) (hz : C.z = 3) : False := by
  apply impossibleAt G C hG hMin hRootDegree hPivot hBCard hk hr hx
  rw [card_externalTargets G C, hz, hNoRoot]

theorem impossibleRoot
    (C : G.LocalConfiguration) (hG : G.IsOriented)
    (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8)
    (hPivot : IsMinimalPivot G C)
    (hBCard : C.B.card = 7) (hk : C.k = 3)
    (hr : C.r = 7) (hx : C.x = 4)
    (hRoot : epsilonS G C = 1) (hz : C.z = 2) : False := by
  apply impossibleAt G C hG hMin hRootDegree hPivot hBCard hk hr hx
  rw [card_externalTargets G C, hz, hRoot]

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.ThreeBridge
