import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Compression
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Rows.M2A1B0
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Rows.M2A0B1

/-!
# Compression of the one-defect three-`Z` cores

The unique absent `P` or `P-H` pair is selected canonically by its first
upper-triangle/rectangular index and stored in the compact encoding.
-/

namespace SeymourEight.ThreeZNearCompression

open FiveZExactRisk ThreeZHighDefect ThreeZNearSaturated

def nearBitAt (bits : BitVec 218) (n : Nat) : Bool :=
  if n < 21 then ThreeZHighDefect.pArc bits
      (ThreeZHighDefect.upperPairI n) (ThreeZHighDefect.upperPairJ n)
  else if n < 26 then
    (ThreeZHighDefect.pMissingIndex bits).getLsbD (n - 21)
  else if n < 61 then bits.getLsbD (n + 23)
  else if n < 67 then
    (ThreeZHighDefect.phMissingIndex bits).getLsbD (n - 61)
  else bits.getLsbD (n + 52)

def nearBits (bits : BitVec 218) : ThreeZNearSaturated.Encoding :=
  BitVec.ofFnLE fun n : Fin 166 => nearBitAt bits n

theorem nearBits_get (bits : BitVec 218) (n : Nat) (hn : n < 166) :
    (nearBits bits).getLsbD n = nearBitAt bits n := by
  rw [nearBits, BitVec.getLsbD_ofFnLE]
  simp only [hn, ↓reduceDIte]

theorem pMissingCode_eq (bits : BitVec 218) :
    ThreeZNearSaturated.pMissingCode (nearBits bits) =
      ThreeZHighDefect.pMissingIndex bits := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  rw [ThreeZNearSaturated.pMissingCode, BitVec.getLsbD_extractLsb',
    nearBits_get]
  · simp only [nearBitAt, show ¬(21 + i < 21) by omega,
      show 21 + i < 26 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    simp [hi]
  · omega

theorem phMissingCode_eq (bits : BitVec 218) :
    ThreeZNearSaturated.phMissingCode (nearBits bits) =
      ThreeZHighDefect.phMissingIndex bits := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  rw [ThreeZNearSaturated.phMissingCode, BitVec.getLsbD_extractLsb',
    nearBits_get]
  · simp only [nearBitAt, show ¬(61 + i < 21) by omega,
      show ¬(61 + i < 26) by omega, show 61 + i < 67 by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
    simp [hi, show ¬(61 + i < 61) by omega]
  · omega

theorem upperPair_inverse (i j : Nat) (hi : i < 7) (hj : j < 7)
    (hij : i < j) :
    ThreeZHighDefect.upperPairI (ThreeZNearSaturated.upperIndex i j) = i ∧
      ThreeZHighDefect.upperPairJ (ThreeZNearSaturated.upperIndex i j) = j := by
  interval_cases i <;> interval_cases j <;>
    simp_all [ThreeZHighDefect.upperPairI, ThreeZHighDefect.upperPairJ,
      ThreeZNearSaturated.upperIndex]

theorem nearUpperBit (bits : BitVec 218) (i j : Nat)
    (hi : i < 7) (hj : j < 7) (hij : i < j) :
    (nearBits bits).getLsbD (ThreeZNearSaturated.upperIndex i j) =
      ThreeZHighDefect.pArc bits i j := by
  have hq : ThreeZNearSaturated.upperIndex i j < 21 := by
    interval_cases i <;> interval_cases j <;>
      simp_all [ThreeZNearSaturated.upperIndex]
  rw [nearBits_get bits _ (by omega)]
  simp only [nearBitAt, hq, ↓reduceIte]
  rw [(upperPair_inverse i j hi hj hij).1,
    (upperPair_inverse i j hi hj hij).2]

theorem pArc_false_eq (bits : BitVec 218)
    (hc : ThreeZHighDefect.pComplete bits = true)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    ThreeZNearSaturated.pArc false (nearBits bits) i j =
      ThreeZHighDefect.pArc bits i j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · simp [ThreeZNearSaturated.pArc, ThreeZNearSaturated.pPairMissing,
      show i ≠ j by omega, hij, nearUpperBit bits i j hi hj hij]
  · subst j
    simp [ThreeZNearSaturated.pArc]
    have hd := (Bool.and_eq_true_iff.mp
      ((ThreeZHighDefectCompression.all_eq_true_iff 7 _).mp hc i hi)).1
    simpa using hd
  · have hf := nearUpperBit bits j i hj hi hij
    rw [ThreeZHighDefectCompression.pArc_complement bits hc i j hi hj (by omega)]
    simp [ThreeZNearSaturated.pArc, ThreeZNearSaturated.pPairMissing,
      show i ≠ j by omega, show ¬i < j by omega, hf]

set_option maxHeartbeats 1000000 in
theorem pArc_true_eq (bits : BitVec 218)
    (hc : ThreeZHighDefect.pOneComplete bits = true)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    ThreeZNearSaturated.pArc true (nearBits bits) i j =
      ThreeZHighDefect.pArc bits i j := by
  have hall := (Bool.and_eq_true_iff.mp hc).2
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have hq : ThreeZNearSaturated.upperIndex i j < 21 := by
      interval_cases i <;> interval_cases j <;>
        simp_all [ThreeZNearSaturated.upperIndex]
    have hrow := (ThreeZHighDefectCompression.all_eq_true_iff 21 _).mp
      hall (ThreeZNearSaturated.upperIndex i j) hq
    rw [ThreeZNearSaturated.pArc, if_neg (by omega), if_pos hij,
      ThreeZNearSaturated.pPairMissing, pMissingCode_eq,
      nearUpperBit bits i j hi hj hij]
    rw [(upperPair_inverse i j hi hj hij).1,
      (upperPair_inverse i j hi hj hij).2] at hrow
    split at * <;> simp_all [beq_iff_eq]
  · subst j
    simp [ThreeZNearSaturated.pArc]
    have hdiag := (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hc).1).2
    simpa only [Bool.not_eq_true'] using
      (ThreeZHighDefectCompression.all_eq_true_iff 7 _).mp hdiag i hi
  · have hq : ThreeZNearSaturated.upperIndex j i < 21 := by
      interval_cases i <;> interval_cases j <;>
        simp_all [ThreeZNearSaturated.upperIndex]
    have hrow := (ThreeZHighDefectCompression.all_eq_true_iff 21 _).mp
      hall (ThreeZNearSaturated.upperIndex j i) hq
    rw [ThreeZNearSaturated.pArc, if_neg (by omega), if_neg (by omega),
      ThreeZNearSaturated.pPairMissing, pMissingCode_eq,
      nearUpperBit bits j i hj hi hij]
    rw [(upperPair_inverse j i hj hi hij).1,
      (upperPair_inverse j i hj hi hij).2] at hrow
    split at * <;> simp_all [beq_iff_eq]

theorem pHBit_eq (bits : BitVec 218) (i h : Nat) (hi : i < 7) (hh : h < 5) :
    (nearBits bits).getLsbD (26 + i * 5 + h) =
      ThreeZHighDefect.pToH bits i h := by
  rw [nearBits_get]
  · simp only [nearBitAt, show ¬(26 + i * 5 + h < 21) by omega,
      show ¬(26 + i * 5 + h < 26) by omega,
      show 26 + i * 5 + h < 61 by omega, ↓reduceIte,
      ThreeZHighDefect.pToH]
    congr 1 ; omega
  · omega

theorem pToH_false_eq (bits : BitVec 218) (i h : Nat)
    (hi : i < 7) (hh : h < 5) :
    ThreeZNearSaturated.pToH false (nearBits bits) i h =
      ThreeZHighDefect.pToH bits i h := by
  simp [ThreeZNearSaturated.pToH, ThreeZNearSaturated.phPairMissing,
    pHBit_eq bits i h hi hh]

theorem hToP_false_eq (bits : BitVec 218)
    (hc : ThreeZHighDefect.phComplete bits = true)
    (h i : Nat) (hh : h < 5) (hi : i < 7) :
    ThreeZNearSaturated.hToP false (nearBits bits) h i =
      ThreeZHighDefect.hToP bits h i := by
  have hci := (ThreeZHighDefectCompression.all_eq_true_iff 7 _).mp hc i hi
  have hcPair := (ThreeZHighDefectCompression.all_eq_true_iff 5 _).mp hci h hh
  simp only [beq_iff_eq] at hcPair
  simp [ThreeZNearSaturated.hToP, ThreeZNearSaturated.phPairMissing,
    pHBit_eq bits i h hi hh, hcPair]

set_option maxHeartbeats 1000000 in
theorem pToH_true_eq (bits : BitVec 218)
    (hc : ThreeZHighDefect.phOneComplete bits = true)
    (i h : Nat) (hi : i < 7) (hh : h < 5) :
    ThreeZNearSaturated.pToH true (nearBits bits) i h =
      ThreeZHighDefect.pToH bits i h := by
  have hall := (Bool.and_eq_true_iff.mp hc).2
  have hq : i * 5 + h < 35 := by omega
  have hrow := (ThreeZHighDefectCompression.all_eq_true_iff 35 _).mp
    hall (i * 5 + h) hq
  have hdiv : (i * 5 + h) / 5 = i := by omega
  have hmod : (i * 5 + h) % 5 = h := by omega
  simp only [hdiv, hmod] at hrow
  rw [ThreeZNearSaturated.pToH, ThreeZNearSaturated.phPairMissing,
    phMissingCode_eq, pHBit_eq bits i h hi hh]
  split at * <;> simp_all [beq_iff_eq]

set_option maxHeartbeats 1000000 in
theorem hToP_true_eq (bits : BitVec 218)
    (hc : ThreeZHighDefect.phOneComplete bits = true)
    (h i : Nat) (hh : h < 5) (hi : i < 7) :
    ThreeZNearSaturated.hToP true (nearBits bits) h i =
      ThreeZHighDefect.hToP bits h i := by
  have hall := (Bool.and_eq_true_iff.mp hc).2
  have hq : i * 5 + h < 35 := by omega
  have hrow := (ThreeZHighDefectCompression.all_eq_true_iff 35 _).mp
    hall (i * 5 + h) hq
  have hdiv : (i * 5 + h) / 5 = i := by omega
  have hmod : (i * 5 + h) % 5 = h := by omega
  simp only [hdiv, hmod] at hrow
  rw [ThreeZNearSaturated.hToP, ThreeZNearSaturated.phPairMissing,
    phMissingCode_eq, pHBit_eq bits i h hi hh]
  split at * <;> simp_all [beq_iff_eq]

theorem pToZ_eq (bits : BitVec 218) (i z : Nat) (hi : i < 7) (hz : z < 3) :
    ThreeZNearSaturated.pToZ (nearBits bits) i z =
      ThreeZHighDefect.pToZ bits i z := by
  rw [ThreeZNearSaturated.pToZ, nearBits_get]
  · simp only [nearBitAt, show ¬(67 + i * 3 + z < 21) by omega,
      show ¬(67 + i * 3 + z < 26) by omega,
      show ¬(67 + i * 3 + z < 61) by omega,
      show ¬(67 + i * 3 + z < 67) by omega, ↓reduceIte,
      ThreeZHighDefect.pToZ]
    congr 1 ; omega
  · omega

theorem rToP_eq (bits : BitVec 218) (r i : Nat) (hr : r < 2) (hi : i < 7) :
    ThreeZNearSaturated.rToP (nearBits bits) r i =
      ThreeZHighDefect.rToP bits r i := by
  rw [ThreeZNearSaturated.rToP, nearBits_get]
  · simp only [nearBitAt, show ¬(88 + r * 7 + i < 21) by omega,
      show ¬(88 + r * 7 + i < 26) by omega,
      show ¬(88 + r * 7 + i < 61) by omega,
      show ¬(88 + r * 7 + i < 67) by omega, ↓reduceIte,
      ThreeZHighDefect.rToP]
    congr 1 ; omega
  · omega

theorem aArc_eq (bits : BitVec 218) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    ThreeZNearSaturated.aArc (nearBits bits) i j =
      ThreeZHighDefect.aArc bits i j := by
  rw [ThreeZNearSaturated.aArc, nearBits_get]
  · simp only [nearBitAt, show ¬(102 + i * 8 + j < 21) by omega,
      show ¬(102 + i * 8 + j < 26) by omega,
      show ¬(102 + i * 8 + j < 61) by omega,
      show ¬(102 + i * 8 + j < 67) by omega, ↓reduceIte,
      ThreeZHighDefect.aArc]
    congr 1 ; omega
  · omega

theorem coreArc_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j =
        ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h =
        ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i =
        ThreeZHighDefect.hToP bits h i)
    (u v : Nat) :
    ThreeZNearSaturated.coreArc alphaOne betaOne (nearBits bits) u v =
      ThreeZHighDefect.coreArc bits u v := by
  by_cases hu8 : u < 8
  · by_cases hv8 : v < 8
    · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
        aArc_eq bits u v hu8 hv8]
    · by_cases hv15 : v < 15
      · have hvp : v - 8 < 7 := by omega
        by_cases hu0 : u = 0
        · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hv8,
            hv15, ThreeZNearSaturated.aToP, ThreeZHighDefect.aToP, hu0]
        · by_cases hu6 : u < 6
          · have huh : u - 1 < 5 := by omega
            simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
              hv15, ThreeZNearSaturated.aToP, ThreeZHighDefect.aToP, hu0, hu6,
              hpi (u - 1) (v - 8) huh hvp]
          · have hur : u - 6 < 2 := by omega
            simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
              hv15, ThreeZNearSaturated.aToP, ThreeZHighDefect.aToP, hu0, hu6,
              rToP_eq bits (u - 6) (v - 8) hur hvp]
      · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8, hv15]
  · by_cases hu15 : u < 15
    · have hup : u - 8 < 7 := by omega
      by_cases hv8 : v < 8
      · by_cases hv0 : 0 < v
        · by_cases hv6 : v < 6
          · have hvh : v - 1 < 5 := by omega
            simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8,
              hu15, hv8, ThreeZNearSaturated.pToA, ThreeZHighDefect.pToA,
              hv0, hv6, hpo (u - 8) (v - 1) hup hvh]
          · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8,
              hu15, hv8, ThreeZNearSaturated.pToA, ThreeZHighDefect.pToA,
              hv0, hv6]
        · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8,
            hu15, hv8, ThreeZNearSaturated.pToA, ThreeZHighDefect.pToA, hv0]
      · by_cases hv15 : v < 15
        · simpa [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8,
              hu15, hv8, hv15] using hp (u - 8) (v - 8) hup (by omega)
        · by_cases hv18 : v < 18
          · simpa [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8,
                hu15, hv8, hv15, hv18] using
              pToZ_eq bits (u - 8) (v - 15) hup (by omega)
          · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8,
              hu15, hv8, hv15, hv18]
    · simp [ThreeZNearSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15]

theorem coreArc_fun_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j =
        ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h =
        ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i =
        ThreeZHighDefect.hToP bits h i) :
    ThreeZNearSaturated.coreArc alphaOne betaOne (nearBits bits) =
      ThreeZHighDefect.coreArc bits := by
  funext u v
  exact coreArc_eq alphaOne betaOne bits hp hpo hpi u v

set_option maxHeartbeats 1000000 in
theorem fixedStructure_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j =
        ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h =
        ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i =
        ThreeZHighDefect.hToP bits h i) :
    ThreeZNearSaturated.fixedStructure alphaOne betaOne (nearBits bits) =
      ThreeZHighDefect.fixedStructure bits := by
  simp (config := { maxSteps := 1000000 }) only [
    ThreeZNearSaturated.fixedStructure, ThreeZHighDefect.fixedStructure,
    ThreeZNearSaturated.aOut, ThreeZHighDefect.aOut,
    ThreeZNearSaturated.aPOut, ThreeZHighDefect.aPOut,
    ThreeZNearSaturated.coreOutdegree, ThreeZHighDefect.coreOutdegree,
    ThreeZNearSaturated.aToP, ThreeZHighDefect.aToP,
    coreArc_fun_eq alphaOne betaOne bits hp hpo hpi,
    all, any, count, bitCount]
  simp [aArc_eq bits, hpo, hpi, rToP_eq bits, pToZ_eq bits]

theorem deletionReached_fun_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i = ThreeZHighDefect.hToP bits h i)
    (deleted : Nat) :
    ThreeZNearSaturated.deletionReached alphaOne betaOne (nearBits bits) deleted =
      ThreeZHighDefect.deletionReached bits deleted := by
  funext target
  simp only [ThreeZNearSaturated.deletionReached,
    ThreeZNearSaturated.retainedAfterDelete, ThreeZNearSaturated.aOneNeighbor,
    ThreeZHighDefect.deletionReached, ThreeZHighDefect.retainedAfterDelete,
    ThreeZHighDefect.aOneNeighbor,
    coreArc_fun_eq alphaOne betaOne bits hp hpo hpi]
  rfl

theorem deletionExpands_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i = ThreeZHighDefect.hToP bits h i) :
    ThreeZNearSaturated.aOneDeletionExpands alphaOne betaOne (nearBits bits) =
      ThreeZHighDefect.aOneDeletionExpands bits := by
  simp only [ThreeZNearSaturated.aOneDeletionExpands,
    ThreeZNearSaturated.deletionExpansionCount,
    ThreeZHighDefect.aOneDeletionExpands,
    ThreeZHighDefect.deletionExpansionCount,
    deletionReached_fun_eq alphaOne betaOne bits hp hpo hpi]

theorem secondFromA_fun_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i = ThreeZHighDefect.hToP bits h i)
    (source : Nat) :
    ThreeZNearSaturated.secondFromA alphaOne betaOne (nearBits bits) source =
      ThreeZHighDefect.secondFromA bits source := by
  funext target
  simp only [ThreeZNearSaturated.secondFromA, ThreeZNearSaturated.reachedFromA,
    ThreeZHighDefect.secondFromA, ThreeZHighDefect.reachedFromA,
    coreArc_fun_eq alphaOne betaOne bits hp hpo hpi]

theorem nonSeymour_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i = ThreeZHighDefect.hToP bits h i)
    (u : Nat) :
    ThreeZNearSaturated.aNonSeymour alphaOne betaOne (nearBits bits) u =
      ThreeZHighDefect.aNonSeymour bits u := by
  simp only [ThreeZNearSaturated.aNonSeymour, ThreeZNearSaturated.aSecondCount,
    ThreeZNearSaturated.coreOutdegree, ThreeZHighDefect.aNonSeymour,
    ThreeZHighDefect.aSecondCount, ThreeZHighDefect.coreOutdegree,
    coreArc_fun_eq alphaOne betaOne bits hp hpo hpi,
    secondFromA_fun_eq alphaOne betaOne bits hp hpo hpi]

set_option maxHeartbeats 1000000 in
theorem totalPToH_eq (alphaOne : Bool) (bits : BitVec 218)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h) :
    ThreeZNearSaturated.totalPToH alphaOne (nearBits bits) =
      ThreeZHighDefect.totalPToH bits := by
  simp only [ThreeZNearSaturated.totalPToH, ThreeZHighDefect.totalPToH, count, bitCount]
  simp [hpo]

set_option maxHeartbeats 1000000 in
theorem totalPOut_eq (betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j) :
    ThreeZNearSaturated.totalPOut betaOne (nearBits bits) =
      ThreeZHighDefect.totalPOut bits := by
  simp only [ThreeZNearSaturated.totalPOut, ThreeZHighDefect.totalPOut, count, bitCount]
  simp [hp]

set_option maxHeartbeats 1000000 in
theorem totalMissingPZ_eq (bits : BitVec 218) :
    ThreeZNearSaturated.totalMissingPZ (nearBits bits) =
      ThreeZHighDefect.totalMissingPZ bits := by
  simp only [ThreeZNearSaturated.totalMissingPZ, ThreeZHighDefect.totalMissingPZ, count, bitCount]
  simp [pToZ_eq bits]

theorem pDegree_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h)
    (p : Nat) (hpLt : p < 7) :
    ThreeZNearSaturated.pDegree alphaOne betaOne (nearBits bits) p =
      ThreeZHighDefect.pDegree bits p := by
  simp only [ThreeZNearSaturated.pDegree, ThreeZHighDefect.pDegree, count, bitCount]
  simp [hp, hpo, pToZ_eq bits, hpLt]

set_option maxHeartbeats 1000000 in
theorem orderedP_eq (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h) :
    ThreeZNearSaturated.orderedP alphaOne betaOne (nearBits bits) =
      ThreeZHighDefect.orderedP bits := by
  simp (config := { maxSteps := 1000000 }) only [ThreeZNearSaturated.orderedP,
    ThreeZNearSaturated.pDegree, ThreeZHighDefect.orderedP,
    ThreeZHighDefect.pDegree, all, count, bitCount]
  simp [hp, hpo, pToZ_eq bits]

set_option maxHeartbeats 1000000 in
theorem orderedZ_eq (bits : BitVec 218) :
    ThreeZNearSaturated.orderedZ (nearBits bits) = ThreeZHighDefect.orderedZ bits := by
  simp (config := { maxSteps := 1000000 }) only [ThreeZNearSaturated.orderedZ,
    ThreeZNearSaturated.zCode, ThreeZHighDefect.orderedZ,
    ThreeZHighDefect.zCode, all, count16, bitCount16]
  simp [pToZ_eq bits]

theorem nearCore_of_fields (alphaOne betaOne : Bool) (bits : BitVec 218)
    (hp : ∀ i j, i < 7 → j < 7 →
      ThreeZNearSaturated.pArc betaOne (nearBits bits) i j = ThreeZHighDefect.pArc bits i j)
    (hpo : ∀ i h, i < 7 → h < 5 →
      ThreeZNearSaturated.pToH alphaOne (nearBits bits) i h = ThreeZHighDefect.pToH bits i h)
    (hpi : ∀ h i, h < 5 → i < 7 →
      ThreeZNearSaturated.hToP alphaOne (nearBits bits) h i = ThreeZHighDefect.hToP bits h i)
    (hPhCode : (!alphaOne || (ThreeZNearSaturated.phMissingCode (nearBits bits)).ult 35) = true)
    (hPCode : (!betaOne || (ThreeZNearSaturated.pMissingCode (nearBits bits)).ult 21) = true)
    (hfixed : ThreeZHighDefect.fixedStructure bits = true)
    (hdelete : ThreeZHighDefect.aOneDeletionExpands bits = true)
    (htoH : ThreeZHighDefect.totalPToH bits + bitCount alphaOne = 17)
    (htoP : ThreeZHighDefect.totalPOut bits + bitCount betaOne = 21)
    (hm : ThreeZHighDefect.totalMissingPZ bits = 2)
    (hnA : all 7 (fun q => ThreeZHighDefect.aNonSeymour bits (q + 1)) = true)
    (hnP : all 7 (fun q => ThreeZHighDefect.aNonSeymour bits (q + 8)) = true)
    (hordP : ThreeZHighDefect.orderedP bits = true)
    (hordZ : ThreeZHighDefect.orderedZ bits = true) :
    ThreeZNearSaturated.nearSaturatedCore alphaOne betaOne (nearBits bits) = true := by
  rw [ThreeZNearSaturated.nearSaturatedCore,
    fixedStructure_eq alphaOne betaOne bits hp hpo hpi,
    deletionExpands_eq alphaOne betaOne bits hp hpo hpi,
    totalPToH_eq alphaOne bits hpo, totalPOut_eq betaOne bits hp,
    totalMissingPZ_eq bits, orderedP_eq alphaOne betaOne bits hp hpo,
    orderedZ_eq bits]
  simp only [nonSeymour_eq alphaOne betaOne bits hp hpo hpi,
    hPhCode, hPCode, hfixed, hdelete, htoH, htoP, hm, hnA, hnP,
    hordP, hordZ, Bool.true_and, decide_true]

set_option maxHeartbeats 2000000 in
theorem near_a1_b0_of_general (bits : BitVec 218)
    (h : ThreeZHighDefect.highDefectCoreAtDefects 2 1 0 bits = true)
    (hphOne : ThreeZHighDefect.phOneComplete bits = true) :
    ThreeZNearSaturated.nearSaturatedCore true false (nearBits bits) = true := by
  simp only [ThreeZHighDefect.highDefectCoreAtDefects,
    ThreeZHighDefect.pCompatibleAtDefect, ThreeZHighDefect.phCompatibleAtDefect,
    if_pos, if_neg (by decide : (1 : Nat) ≠ 0)] at h
  have ⟨h4, _hphCompatible⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h3, hpComplete⟩ := Bool.and_eq_true_iff.mp h4
  have ⟨hleft, htoP0⟩ := Bool.and_eq_true_iff.mp h3
  have ⟨hcm, htoH1⟩ := Bool.and_eq_true_iff.mp hleft
  simp only [ThreeZHighDefect.highDefectCoreAtMissing] at hcm
  have ⟨hcore, hm0⟩ := Bool.and_eq_true_iff.mp hcm
  have hm : ThreeZHighDefect.totalMissingPZ bits = 2 := of_decide_eq_true hm0
  have htoH : ThreeZHighDefect.totalPToH bits + bitCount true = 17 := by
    change ThreeZHighDefect.totalPToH bits + 1 = 17
    exact of_decide_eq_true htoH1
  have htoP : ThreeZHighDefect.totalPOut bits + bitCount false = 21 := by
    change ThreeZHighDefect.totalPOut bits + 0 = 21
    exact of_decide_eq_true htoP0
  have hf := ThreeZHighDefect.highCoreFacts_of_true hcore
  have hPhCode : (!true || (ThreeZNearSaturated.phMissingCode (nearBits bits)).ult 35) = true := by
    simpa [phMissingCode_eq] using (Bool.and_eq_true_iff.mp hphOne).1
  have hPCode : (!false || (ThreeZNearSaturated.pMissingCode (nearBits bits)).ult 21) = true := by simp
  exact nearCore_of_fields true false bits
    (pArc_false_eq bits hpComplete) (pToH_true_eq bits hphOne)
    (hToP_true_eq bits hphOne) hPhCode hPCode hf.fixed hf.deletion htoH htoP hm
    hf.nonSeymourA hf.nonSeymourP hf.orderedP_true hf.orderedZ_true

set_option maxHeartbeats 2000000 in
theorem near_a0_b1_of_general (bits : BitVec 218)
    (h : ThreeZHighDefect.highDefectCoreAtDefects 2 0 1 bits = true) :
    ThreeZNearSaturated.nearSaturatedCore false true (nearBits bits) = true := by
  simp only [ThreeZHighDefect.highDefectCoreAtDefects,
    ThreeZHighDefect.pCompatibleAtDefect, ThreeZHighDefect.phCompatibleAtDefect,
    if_pos, if_neg (by decide : (1 : Nat) ≠ 0)] at h
  have ⟨h4, hphComplete⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h3, hpOne⟩ := Bool.and_eq_true_iff.mp h4
  have ⟨hleft, htoP1⟩ := Bool.and_eq_true_iff.mp h3
  have ⟨hcm, htoH0⟩ := Bool.and_eq_true_iff.mp hleft
  simp only [ThreeZHighDefect.highDefectCoreAtMissing] at hcm
  have ⟨hcore, hm0⟩ := Bool.and_eq_true_iff.mp hcm
  have hm : ThreeZHighDefect.totalMissingPZ bits = 2 := of_decide_eq_true hm0
  have htoH : ThreeZHighDefect.totalPToH bits + bitCount false = 17 := by
    change ThreeZHighDefect.totalPToH bits + 0 = 17
    exact of_decide_eq_true htoH0
  have htoP : ThreeZHighDefect.totalPOut bits + bitCount true = 21 := by
    change ThreeZHighDefect.totalPOut bits + 1 = 21
    exact of_decide_eq_true htoP1
  have hf := ThreeZHighDefect.highCoreFacts_of_true hcore
  have hPhCode : (!false || (ThreeZNearSaturated.phMissingCode (nearBits bits)).ult 35) = true := by simp
  have hPCode : (!true || (ThreeZNearSaturated.pMissingCode (nearBits bits)).ult 21) = true := by
    simpa [pMissingCode_eq] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hpOne).1).1
  exact nearCore_of_fields false true bits
    (pArc_true_eq bits hpOne) (pToH_false_eq bits)
    (hToP_false_eq bits hphComplete) hPhCode hPCode hf.fixed hf.deletion htoH htoP hm
    hf.nonSeymourA hf.nonSeymourP hf.orderedP_true hf.orderedZ_true

end SeymourEight.ThreeZNearCompression
