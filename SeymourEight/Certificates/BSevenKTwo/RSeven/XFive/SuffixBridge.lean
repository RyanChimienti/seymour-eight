import SeymourEight.Certificates.BSevenKTwo.RSeven.XFive.CoreDefs

namespace SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core

open Shared.FiniteCore

private def scalarKey (p h z : BitVec 8) : BitVec 16 :=
  (p + h + z).zeroExtend 16 * 4096 + z.zeroExtend 16 * 256 +
    h.zeroExtend 16 * 16 + p.zeroExtend 16

private theorem degree_upper_of_total
    (s d0 d1 d2 d3 d4 d5 d6 : BitVec 8)
    (hMin : (8 : BitVec 8).ule d0 && (8 : BitVec 8).ule d1 &&
      (8 : BitVec 8).ule d2 && (8 : BitVec 8).ule d3 &&
      (8 : BitVec 8).ule d4 && (8 : BitVec 8).ule d5 &&
      (8 : BitVec 8).ule d6 = true)
    (hCap : d0.ule 17 && d1.ule 17 && d2.ule 17 && d3.ule 17 &&
      d4.ule 17 && d5.ule 17 && d6.ule 17 = true)
    (hSum : d0 + d1 + d2 + d3 + d4 + d5 + d6 + s = 61)
    (hs : s.ule 5 = true) :
    d0.ule 13 && d1.ule 13 && d2.ule 13 && d3.ule 13 &&
      d4.ule 13 && d5.ule 13 && d6.ule 13 = true := by
  bv_decide (config := { acNf := true })

private theorem degree_cap (p h z : BitVec 8)
    (hp : p.ule 7 = true) (hh : h.ule 7 = true) (hz : z.ule 3 = true) :
    (p + h + z).ule 17 = true := by
  bv_decide (config := { acNf := true })

private theorem degree_order_of_key_order
    (p0 h0 z0 p1 h1 z1 : BitVec 8)
    (hCaps : p0.ule 7 && h0.ule 7 && z0.ule 3 &&
      p1.ule 7 && h1.ule 7 && z1.ule 3 = true)
    (hUpper : (p0 + h0 + z0).ule 13 && (p1 + h1 + z1).ule 13 = true)
    (hKey : (scalarKey p1 h1 z1).ule (scalarKey p0 h0 z0) = true) :
    (p1 + h1 + z1).ule (p0 + h0 + z0) = true := by
  simp only [scalarKey] at hKey
  bv_decide (config := { acNf := true })

private theorem suffix_of_ordered_degrees
    (s d0 d1 d2 d3 d4 d5 d6 : BitVec 8)
    (hMin : (8 : BitVec 8).ule d0 && (8 : BitVec 8).ule d1 &&
      (8 : BitVec 8).ule d2 && (8 : BitVec 8).ule d3 &&
      (8 : BitVec 8).ule d4 && (8 : BitVec 8).ule d5 &&
      (8 : BitVec 8).ule d6 = true)
    (hOrder : d1.ule d0 && d2.ule d1 && d3.ule d2 && d4.ule d3 &&
      d5.ule d4 && d6.ule d5 = true)
    (hUpper : d0.ule 13 && d1.ule 13 && d2.ule 13 && d3.ule 13 &&
      d4.ule 13 && d5.ule 13 && d6.ule 13 = true)
    (hSum : d0 + d1 + d2 + d3 + d4 + d5 + d6 + s = 61)
    (hs : s.ule 5 = true) :
    d5 == 8 && d6 == 8 &&
      (!(1 : BitVec 8).ule s || d4 == 8) &&
      (!(2 : BitVec 8).ule s || d3 == 8) &&
      (!(3 : BitVec 8).ule s || d2 == 8) &&
      (!(4 : BitVec 8).ule s || d1 == 8) &&
      (!(5 : BitVec 8).ule s || d0 == 8) = true := by
  bv_decide (config := { acNf := true })

private theorem count_seven_ule (f : Nat → Bool) :
    (count 7 f).ule 7 = true := by
  simp only [count, bitCount]
  bv_decide

private theorem count_three_ule (f : Nat → Bool) :
    (count 3 f).ule 3 = true := by
  simp only [count, bitCount]
  bv_decide

private theorem sumCount_add_three (n : Nat) (p h z : Nat → BitVec 8) :
    sumCount n (fun i => p i + h i + z i) =
      sumCount n p + sumCount n h + sumCount n z := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih =>
      simp only [sumCount, ih]
      ac_rfl

private theorem aggregate_accounting (p h z : BitVec 8) :
    (p + h + z) + ((21 - z) + (40 - h - p)) = 61 := by
  bv_decide (config := { acNf := true })

private theorem scalar_accounting (bits : Encoding) :
    sumCount 7 (fun i => pOut bits i + pHOut bits i + pZOut bits i) +
      (externalMissing bits + combinedDefect bits) = 61 := by
  rw [sumCount_add_three]
  simp only [externalMissing, combinedDefect]
  exact aggregate_accounting (totalPOut bits) (totalPToH bits) (totalPToZ bits)

set_option maxHeartbeats 4000000 in
/-- The scalar defect bound and descending P-row order force the exact
degree-eight suffix used by the combined certificate.  The expensive graph
predicates in `baseCore` are deliberately absent from the arithmetic kernel. -/
theorem degreeEightSuffix_of_baseCore (bits : Encoding)
    (hBase : baseCore bits = true) : degreeEightSuffix bits = true := by
  have hFacts : pMinimumDegree bits = true ∧ orderedP bits = true ∧
      (externalMissing bits + combinedDefect bits).ule 5 = true := by
    rw [baseCore] at hBase
    have h20 := (Bool.and_eq_true_iff.mp hBase).1
    have h19 := (Bool.and_eq_true_iff.mp h20).1
    have h18 := (Bool.and_eq_true_iff.mp h19).1
    have h17 := (Bool.and_eq_true_iff.mp h18).1
    have h16 := (Bool.and_eq_true_iff.mp h17).1
    have h15 := (Bool.and_eq_true_iff.mp h16).1
    have h14 := (Bool.and_eq_true_iff.mp h15).1
    have h13 := (Bool.and_eq_true_iff.mp h14).1
    have h12 := (Bool.and_eq_true_iff.mp h13).1
    have h11 := (Bool.and_eq_true_iff.mp h12).1
    have h10 := (Bool.and_eq_true_iff.mp h11).1
    exact ⟨(Bool.and_eq_true_iff.mp h10).2, (Bool.and_eq_true_iff.mp h15).2,
      (Bool.and_eq_true_iff.mp hBase).2⟩
  have hMin := hFacts.1
  have hOrder := hFacts.2.1
  have hDefect := hFacts.2.2
  let p := pOut bits
  let h := pHOut bits
  let z := pZOut bits
  let s := externalMissing bits + combinedDefect bits
  have hp : ∀ i, (p i).ule 7 = true := fun i => by
    exact count_seven_ule (pArc bits i)
  have hh : ∀ i, (h i).ule 7 = true := fun i => by
    exact count_seven_ule (pToH bits i)
  have hz : ∀ i, (z i).ule 3 = true := fun i => by
    exact count_three_ule (pToZ bits i)
  rw [pMinimumDegree, all_eq_true_iff] at hMin
  rw [orderedP, all_eq_true_iff] at hOrder
  have hMinimum (i : Nat) (hi : i < 7) :
      (8 : BitVec 8).ule (p i + h i + z i) = true := by
    simpa [p, h, z] using hMin i hi
  have hMin' : (8 : BitVec 8).ule (p 0 + h 0 + z 0) &&
      (8 : BitVec 8).ule (p 1 + h 1 + z 1) &&
      (8 : BitVec 8).ule (p 2 + h 2 + z 2) &&
      (8 : BitVec 8).ule (p 3 + h 3 + z 3) &&
      (8 : BitVec 8).ule (p 4 + h 4 + z 4) &&
      (8 : BitVec 8).ule (p 5 + h 5 + z 5) &&
      (8 : BitVec 8).ule (p 6 + h 6 + z 6) = true := by
    rw [hMinimum 0 (by omega), hMinimum 1 (by omega),
      hMinimum 2 (by omega), hMinimum 3 (by omega),
      hMinimum 4 (by omega), hMinimum 5 (by omega), hMinimum 6 (by omega)]
    decide
  have hSum : (p 0 + h 0 + z 0) + (p 1 + h 1 + z 1) +
      (p 2 + h 2 + z 2) + (p 3 + h 3 + z 3) +
      (p 4 + h 4 + z 4) + (p 5 + h 5 + z 5) +
      (p 6 + h 6 + z 6) + s = 61 := by
    simpa [sumCount, p, h, z, s] using scalar_accounting bits
  have hCap : (p 0 + h 0 + z 0).ule 17 &&
      (p 1 + h 1 + z 1).ule 17 && (p 2 + h 2 + z 2).ule 17 &&
      (p 3 + h 3 + z 3).ule 17 && (p 4 + h 4 + z 4).ule 17 &&
      (p 5 + h 5 + z 5).ule 17 && (p 6 + h 6 + z 6).ule 17 = true := by
    rw [degree_cap _ _ _ (hp 0) (hh 0) (hz 0),
      degree_cap _ _ _ (hp 1) (hh 1) (hz 1),
      degree_cap _ _ _ (hp 2) (hh 2) (hz 2),
      degree_cap _ _ _ (hp 3) (hh 3) (hz 3),
      degree_cap _ _ _ (hp 4) (hh 4) (hz 4),
      degree_cap _ _ _ (hp 5) (hh 5) (hz 5),
      degree_cap _ _ _ (hp 6) (hh 6) (hz 6)]
    decide
  have hUpper := degree_upper_of_total s
    (p 0 + h 0 + z 0) (p 1 + h 1 + z 1) (p 2 + h 2 + z 2)
    (p 3 + h 3 + z 3) (p 4 + h 4 + z 4) (p 5 + h 5 + z 5)
    (p 6 + h 6 + z 6) hMin' hCap hSum hDefect
  have hUpperFacts :
      (p 0 + h 0 + z 0).ule 13 = true ∧
      (p 1 + h 1 + z 1).ule 13 = true ∧
      (p 2 + h 2 + z 2).ule 13 = true ∧
      (p 3 + h 3 + z 3).ule 13 = true ∧
      (p 4 + h 4 + z 4).ule 13 = true ∧
      (p 5 + h 5 + z 5).ule 13 = true ∧
      (p 6 + h 6 + z 6).ule 13 = true := by
    have hu := hUpper
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
    exact ⟨hu.1.1.1.1.1.1, hu.1.1.1.1.1.2, hu.1.1.1.1.2,
      hu.1.1.1.2, hu.1.1.2, hu.1.2, hu.2⟩
  have keyOrder (i : Nat) (hi : i < 6) :
      (scalarKey (p (i + 1)) (h (i + 1)) (z (i + 1))).ule
        (scalarKey (p i) (h i) (z i)) = true := by
    simpa [scalarKey, pRowKey, p, h, z] using hOrder i hi
  have degreeOrder (i : Nat) (hi : i < 6)
      (hu0 : (p i + h i + z i).ule 13 = true)
      (hu1 : (p (i + 1) + h (i + 1) + z (i + 1)).ule 13 = true) :
      (p (i + 1) + h (i + 1) + z (i + 1)).ule
        (p i + h i + z i) = true := by
    apply degree_order_of_key_order (p i) (h i) (z i)
      (p (i + 1)) (h (i + 1)) (z (i + 1))
    · rw [hp i, hh i, hz i, hp (i + 1), hh (i + 1), hz (i + 1)]
      decide
    · rw [hu0, hu1]
      decide
    · exact keyOrder i hi
  have hDegreeOrder :
      (p 1 + h 1 + z 1).ule (p 0 + h 0 + z 0) &&
      (p 2 + h 2 + z 2).ule (p 1 + h 1 + z 1) &&
      (p 3 + h 3 + z 3).ule (p 2 + h 2 + z 2) &&
      (p 4 + h 4 + z 4).ule (p 3 + h 3 + z 3) &&
      (p 5 + h 5 + z 5).ule (p 4 + h 4 + z 4) &&
      (p 6 + h 6 + z 6).ule (p 5 + h 5 + z 5) = true := by
    rw [degreeOrder 0 (by omega) hUpperFacts.1 hUpperFacts.2.1,
      degreeOrder 1 (by omega) hUpperFacts.2.1 hUpperFacts.2.2.1,
      degreeOrder 2 (by omega) hUpperFacts.2.2.1 hUpperFacts.2.2.2.1,
      degreeOrder 3 (by omega) hUpperFacts.2.2.2.1 hUpperFacts.2.2.2.2.1,
      degreeOrder 4 (by omega) hUpperFacts.2.2.2.2.1 hUpperFacts.2.2.2.2.2.1,
      degreeOrder 5 (by omega) hUpperFacts.2.2.2.2.2.1 hUpperFacts.2.2.2.2.2.2]
    decide
  have hs := suffix_of_ordered_degrees s
    (p 0 + h 0 + z 0) (p 1 + h 1 + z 1) (p 2 + h 2 + z 2)
    (p 3 + h 3 + z 3) (p 4 + h 4 + z 4) (p 5 + h 5 + z 5)
    (p 6 + h 6 + z 6) hMin' hDegreeOrder hUpper hSum hDefect
  simpa [degreeEightSuffix, pExactEight, s, p, h, z] using hs

end SeymourEight.BSevenKTwo.RSeven.XFiveNoRoot.Core
