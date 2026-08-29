import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Rows.SaturatedM2
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Rows.SaturatedM3
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.Rows.SaturatedM2PH16
import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XFour.HighDefect.CoreDefs
import Batteries.Data.BitVec.Lemmas
import Mathlib.Tactic.IntervalCases

/-!
# Compression of saturated three-`Z` cores

At zero `P-H` and internal-`P` defect, orientation makes the reverse half of
each incidence pair redundant.  This deterministic projection connects the
graph-friendly 218-bit layout to the checked 155-bit saturated certificates.
-/

namespace SeymourEight.ThreeZHighDefectCompression

open FiveZExactRisk ThreeZHighDefect ThreeZSaturated

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def upperPBit (bits : BitVec 218) (n : Nat) : Bool :=
  if n < 6 then ThreeZHighDefect.pArc bits 0 (n + 1)
  else if n < 11 then ThreeZHighDefect.pArc bits 1 (n - 4)
  else if n < 15 then ThreeZHighDefect.pArc bits 2 (n - 8)
  else if n < 18 then ThreeZHighDefect.pArc bits 3 (n - 11)
  else if n < 20 then ThreeZHighDefect.pArc bits 4 (n - 13)
  else ThreeZHighDefect.pArc bits 5 6

def saturatedBitAt (bits : BitVec 218) (n : Nat) : Bool :=
  if n < 21 then upperPBit bits n
  else if n < 56 then bits.getLsbD (n + 28)
  else bits.getLsbD (n + 63)

def saturatedBits (bits : BitVec 218) : ThreeZSaturated.Encoding :=
  BitVec.ofFnLE fun n : Fin 155 ↦ saturatedBitAt bits n

theorem saturatedBits_get (bits : BitVec 218) (n : Nat) (hn : n < 155) :
    (saturatedBits bits).getLsbD n = saturatedBitAt bits n := by
  rw [saturatedBits, BitVec.getLsbD_ofFnLE]
  simp only [hn, ↓reduceDIte]

theorem saturatedBits_getElem (bits : BitVec 218) (n : Nat) (hn : n < 155) :
    (saturatedBits bits)[n] = saturatedBitAt bits n := by
  rw [saturatedBits, BitVec.getElem_ofFnLE]

theorem all_eq_true_iff (n : Nat) (f : Nat → Bool) :
    all n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
      simp only [all, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · have : i = n := by omega
          simpa [this] using hn
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem pArc_complement (bits : BitVec 218)
    (hc : ThreeZHighDefect.pComplete bits = true)
    (i j : Nat) (hi : i < 7) (hj : j < 7)
    (hne : i ≠ j) :
    ThreeZHighDefect.pArc bits i j = !ThreeZHighDefect.pArc bits j i := by
  have hci := (all_eq_true_iff 7 _).mp hc i hi
  have hcij := (all_eq_true_iff 7 _).mp (Bool.and_eq_true_iff.mp hci).2 j hj
  simpa [ThreeZHighDefect.pComplete, hne, beq_iff_eq] using hcij

theorem ph_complement (bits : BitVec 218)
    (hc : ThreeZHighDefect.phComplete bits = true)
    (i h : Nat) (hi : i < 7) (hh : h < 5) :
    ThreeZHighDefect.pToH bits i h = !ThreeZHighDefect.hToP bits h i := by
  have hci := (all_eq_true_iff 7 _).mp hc i hi
  simpa only [beq_iff_eq] using (all_eq_true_iff 5 _).mp hci h hh

set_option linter.flexible false in
theorem pArc_forward (bits : BitVec 218) (i j : Nat)
    (hi : i < 7) (hj : j < 7) (hij : i < j) :
    ThreeZSaturated.pArc (saturatedBits bits) i j =
      ThreeZHighDefect.pArc bits i j := by
  interval_cases i <;> interval_cases j <;>
    simp_all [ThreeZSaturated.pArc, ThreeZSaturated.upperIndex]
  all_goals
    rw [saturatedBits_getElem] <;>
      simp [saturatedBitAt, upperPBit, ThreeZHighDefect.pArc]

theorem pArc_eq (bits : BitVec 218) (hc : pComplete bits = true)
    (i j : Nat) (hi : i < 7) (hj : j < 7) :
    ThreeZSaturated.pArc (saturatedBits bits) i j =
      ThreeZHighDefect.pArc bits i j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact pArc_forward bits i j hi hj hij
  · subst j
    simp [ThreeZSaturated.pArc]
    have hd := (Bool.and_eq_true_iff.mp ((all_eq_true_iff 7 _).mp hc i hi)).1
    simpa using hd
  · rw [pArc_complement bits hc i j hi hj (by omega)]
    have hf := pArc_forward bits j i hj hi hij
    rw [ThreeZSaturated.pArc] at hf
    simp only [Nat.ne_of_lt hij, hij, ↓reduceIte] at hf
    rw [ThreeZSaturated.pArc]
    simp only [Nat.ne_of_gt hij, show ¬i < j by omega, ↓reduceIte]
    exact congrArg (fun b : Bool => !b) hf

theorem pToH_eq (bits : BitVec 218) (i h : Nat) (hi : i < 7) (hh : h < 5) :
    ThreeZSaturated.pToH (saturatedBits bits) i h =
      ThreeZHighDefect.pToH bits i h := by
  rw [ThreeZSaturated.pToH, saturatedBits_get]
  · simp only [saturatedBitAt, show ¬(21 + i * 5 + h < 21) by omega,
      show 21 + i * 5 + h < 56 by omega, ↓reduceIte,
      ThreeZHighDefect.pToH]
    congr 1 <;> omega
  · omega

theorem hToP_eq (bits : BitVec 218) (hc : phComplete bits = true)
    (h i : Nat) (hh : h < 5) (hi : i < 7) :
    ThreeZSaturated.hToP (saturatedBits bits) h i =
      ThreeZHighDefect.hToP bits h i := by
  rw [ThreeZSaturated.hToP, pToH_eq bits i h hi hh,
    ph_complement bits hc i h hi hh]
  simp

theorem pToZ_eq (bits : BitVec 218) (i z : Nat) (hi : i < 7) (hz : z < 3) :
    ThreeZSaturated.pToZ (saturatedBits bits) i z =
      ThreeZHighDefect.pToZ bits i z := by
  rw [ThreeZSaturated.pToZ, saturatedBits_get]
  · simp only [saturatedBitAt, show ¬(56 + i * 3 + z < 21) by omega,
      show ¬(56 + i * 3 + z < 56) by omega, ↓reduceIte,
      ThreeZHighDefect.pToZ]
    congr 1 <;> omega
  · omega

theorem rToP_eq (bits : BitVec 218) (r i : Nat) (hr : r < 2) (hi : i < 7) :
    ThreeZSaturated.rToP (saturatedBits bits) r i =
      ThreeZHighDefect.rToP bits r i := by
  rw [ThreeZSaturated.rToP, saturatedBits_get]
  · simp only [saturatedBitAt, show ¬(77 + r * 7 + i < 21) by omega,
      show ¬(77 + r * 7 + i < 56) by omega, ↓reduceIte,
      ThreeZHighDefect.rToP]
    congr 1 <;> omega
  · omega

theorem aArc_eq (bits : BitVec 218) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    ThreeZSaturated.aArc (saturatedBits bits) i j =
      ThreeZHighDefect.aArc bits i j := by
  rw [ThreeZSaturated.aArc, saturatedBits_get]
  · simp only [saturatedBitAt, show ¬(91 + i * 8 + j < 21) by omega,
      show ¬(91 + i * 8 + j < 56) by omega, ↓reduceIte,
      ThreeZHighDefect.aArc]
    congr 1 <;> omega
  · omega

theorem coreArc_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) (u v : Nat) :
    ThreeZSaturated.coreArc (saturatedBits bits) u v =
      ThreeZHighDefect.coreArc bits u v := by
  by_cases hu8 : u < 8
  · by_cases hv8 : v < 8
    · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
        aArc_eq bits u v hu8 hv8]
    · by_cases hv15 : v < 15
      · have hvp : v - 8 < 7 := by omega
        by_cases hu0 : u = 0
        · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
            hv15, ThreeZSaturated.aToP, ThreeZHighDefect.aToP, hu0]
        · by_cases hu6 : u < 6
          · have hpred : u - 1 < 5 := by omega
            simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
                hv15, ThreeZSaturated.aToP, ThreeZHighDefect.aToP, hu0, hu6,
                hToP_eq bits hph (u - 1) (v - 8) hpred hvp]
          · have hur : u - 6 < 2 := by omega
            simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8,
                hv15, ThreeZSaturated.aToP, ThreeZHighDefect.aToP, hu0, hu6,
                rToP_eq bits (u - 6) (v - 8) hur hvp]
      · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hv8, hv15]
  · by_cases hu15 : u < 15
    · have hup : u - 8 < 7 := by omega
      by_cases hv8 : v < 8
      · by_cases hv0 : 0 < v
        · by_cases hv6 : v < 6
          · have hvh : v - 1 < 5 := by omega
            simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15,
                hv8, ThreeZSaturated.pToA, ThreeZHighDefect.pToA, hv0, hv6,
                pToH_eq bits (u - 8) (v - 1) hup hvh]
          · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15,
                hv8, ThreeZSaturated.pToA, ThreeZHighDefect.pToA, hv0, hv6]
        · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15,
              hv8, ThreeZSaturated.pToA, ThreeZHighDefect.pToA, hv0]
      · by_cases hv15 : v < 15
        · simpa [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15,
              hv8, hv15] using pArc_eq bits hp (u - 8) (v - 8) hup (by omega)
        · by_cases hv18 : v < 18
          · simpa [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15,
                hv8, hv15, hv18] using
              pToZ_eq bits (u - 8) (v - 15) hup (by omega)
          · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15,
                hv8, hv15, hv18]
    · simp [ThreeZSaturated.coreArc, ThreeZHighDefect.coreArc, hu8, hu15]

theorem coreArc_fun_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) :
    ThreeZSaturated.coreArc (saturatedBits bits) =
      ThreeZHighDefect.coreArc bits := by
  funext u v
  exact coreArc_eq bits hp hph u v

theorem deletionReached_fun_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) (deleted : Nat) :
    ThreeZSaturated.deletionReached (saturatedBits bits) deleted =
      ThreeZHighDefect.deletionReached bits deleted := by
  funext target
  simp only [ThreeZSaturated.deletionReached,
    ThreeZSaturated.retainedAfterDelete, ThreeZSaturated.aOneNeighbor,
    ThreeZHighDefect.deletionReached, ThreeZHighDefect.retainedAfterDelete,
    ThreeZHighDefect.aOneNeighbor, coreArc_fun_eq bits hp hph]
  rfl

theorem secondFromA_fun_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) (source : Nat) :
    ThreeZSaturated.secondFromA (saturatedBits bits) source =
      ThreeZHighDefect.secondFromA bits source := by
  funext target
  simp only [ThreeZSaturated.secondFromA, ThreeZSaturated.reachedFromA,
    ThreeZHighDefect.secondFromA, ThreeZHighDefect.reachedFromA,
    coreArc_fun_eq bits hp hph]

set_option maxHeartbeats 1000000 in
theorem fixedStructure_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) :
    ThreeZSaturated.fixedStructure (saturatedBits bits) =
      ThreeZHighDefect.fixedStructure bits := by
  simp (config := { maxSteps := 1000000 }) only [
    ThreeZSaturated.fixedStructure, ThreeZHighDefect.fixedStructure,
    ThreeZSaturated.aOut, ThreeZHighDefect.aOut,
    ThreeZSaturated.aPOut, ThreeZHighDefect.aPOut,
    ThreeZSaturated.coreOutdegree, ThreeZHighDefect.coreOutdegree,
    ThreeZSaturated.aToP, ThreeZHighDefect.aToP,
    coreArc_fun_eq bits hp hph,
    all, any, count, bitCount]
  simp [aArc_eq bits, pToH_eq bits, hToP_eq bits hph,
    rToP_eq bits, pToZ_eq bits]

theorem deletionExpands_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) :
    ThreeZSaturated.aOneDeletionExpands (saturatedBits bits) =
      ThreeZHighDefect.aOneDeletionExpands bits := by
  simp only [ThreeZSaturated.aOneDeletionExpands,
    ThreeZSaturated.deletionExpansionCount, ThreeZSaturated.deletionReached,
    ThreeZSaturated.retainedAfterDelete, ThreeZSaturated.aOneNeighbor,
    ThreeZHighDefect.aOneDeletionExpands,
    ThreeZHighDefect.deletionExpansionCount, ThreeZHighDefect.deletionReached,
    ThreeZHighDefect.retainedAfterDelete, ThreeZHighDefect.aOneNeighbor,
    deletionReached_fun_eq bits hp hph]

theorem nonSeymour_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) (u : Nat) :
    ThreeZSaturated.aNonSeymour (saturatedBits bits) u =
      ThreeZHighDefect.aNonSeymour bits u := by
  simp only [ThreeZSaturated.aNonSeymour, ThreeZSaturated.aSecondCount,
    ThreeZSaturated.secondFromA, ThreeZSaturated.reachedFromA,
    ThreeZSaturated.coreOutdegree, ThreeZHighDefect.aNonSeymour,
    ThreeZHighDefect.aSecondCount, ThreeZHighDefect.secondFromA,
    ThreeZHighDefect.reachedFromA, ThreeZHighDefect.coreOutdegree,
    coreArc_fun_eq bits hp hph, secondFromA_fun_eq bits hp hph]

set_option maxHeartbeats 1000000 in
theorem totalPToH_eq (bits : BitVec 218) :
    ThreeZSaturated.totalPToH (saturatedBits bits) =
      ThreeZHighDefect.totalPToH bits := by
  simp only [ThreeZSaturated.totalPToH, ThreeZHighDefect.totalPToH,
    count, bitCount]
  simp [pToH_eq bits]

set_option maxHeartbeats 1000000 in
theorem totalMissingPZ_eq (bits : BitVec 218) :
    ThreeZSaturated.totalMissingPZ (saturatedBits bits) =
      ThreeZHighDefect.totalMissingPZ bits := by
  simp only [ThreeZSaturated.totalMissingPZ, ThreeZHighDefect.totalMissingPZ,
    count, bitCount]
  simp [pToZ_eq bits]

theorem pDegree_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (p : Nat) (hpLt : p < 7) :
    ThreeZSaturated.pDegree (saturatedBits bits) p =
      ThreeZHighDefect.pDegree bits p := by
  simp only [ThreeZSaturated.pDegree, ThreeZHighDefect.pDegree, count, bitCount]
  simp [pArc_eq bits hp, pToH_eq bits, pToZ_eq bits, hpLt]

set_option maxHeartbeats 1000000 in
theorem orderedP_eq (bits : BitVec 218)
    (hp : ThreeZHighDefect.pComplete bits = true) :
    ThreeZSaturated.orderedP (saturatedBits bits) =
      ThreeZHighDefect.orderedP bits := by
  simp (config := { maxSteps := 1000000 }) only [ThreeZSaturated.orderedP,
    ThreeZSaturated.pDegree, ThreeZHighDefect.orderedP,
    ThreeZHighDefect.pDegree, all, count, bitCount]
  simp [pArc_eq bits hp, pToH_eq bits, pToZ_eq bits]

set_option maxHeartbeats 1000000 in
theorem orderedZ_eq (bits : BitVec 218) :
    ThreeZSaturated.orderedZ (saturatedBits bits) =
      ThreeZHighDefect.orderedZ bits := by
  simp (config := { maxSteps := 1000000 }) only [ThreeZSaturated.orderedZ,
    ThreeZSaturated.zCode, ThreeZHighDefect.orderedZ,
    ThreeZHighDefect.zCode, all, count16, bitCount16]
  simp [pToZ_eq bits]

/- The final transfer is kept separate from the small saturation checks.
Its Boolean normalization now sees identical primitive arc relations. -/
set_option maxHeartbeats 3000000 in
theorem saturated_of_general_fields (missing pToHTotal : Nat)
    (bits : BitVec 218)
    (hcore : ThreeZHighDefect.highDefectCore bits = true)
    (hm : ThreeZHighDefect.totalMissingPZ bits = BitVec.ofNat 8 missing)
    (htoH : ThreeZHighDefect.totalPToH bits = BitVec.ofNat 8 pToHTotal)
    (hp : ThreeZHighDefect.pComplete bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) :
    ThreeZSaturated.saturatedCoreAtMissingPToH missing pToHTotal
      (saturatedBits bits) = true := by
  have hf := ThreeZHighDefect.highCoreFacts_of_true hcore
  rw [ThreeZSaturated.saturatedCoreAtMissingPToH,
    fixedStructure_eq bits hp hph, deletionExpands_eq bits hp hph,
    totalPToH_eq bits, totalMissingPZ_eq bits,
    orderedP_eq bits hp, orderedZ_eq bits]
  simp only [nonSeymour_eq bits hp hph, hf.fixed, hf.deletion, htoH, hm,
    hf.nonSeymourA, hf.nonSeymourP, hf.orderedP_true, hf.orderedZ_true,
    Bool.true_and, decide_true]

set_option maxHeartbeats 3000000 in
theorem saturated_of_general (missing : Nat) (bits : BitVec 218)
    (h : ThreeZHighDefect.highDefectCoreAtDefects missing 0 0 bits = true) :
    ThreeZSaturated.saturatedCoreAtMissing missing (saturatedBits bits) = true := by
  simp only [ThreeZHighDefect.highDefectCoreAtDefects,
    ThreeZHighDefect.pCompatibleAtDefect,
    ThreeZHighDefect.phCompatibleAtDefect, if_pos] at h
  have ⟨h4, hph⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h3, hp⟩ := Bool.and_eq_true_iff.mp h4
  have hleft := (Bool.and_eq_true_iff.mp h3).1
  have htoH : ThreeZHighDefect.totalPToH bits = BitVec.ofNat 8 17 := by
    simpa using of_decide_eq_true (Bool.and_eq_true_iff.mp hleft).2
  have hcm := (Bool.and_eq_true_iff.mp hleft).1
  simp only [ThreeZHighDefect.highDefectCoreAtMissing] at hcm
  have hcore := (Bool.and_eq_true_iff.mp hcm).1
  have hm : ThreeZHighDefect.totalMissingPZ bits = BitVec.ofNat 8 missing :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hcm).2
  rw [ThreeZSaturated.saturatedCoreAtMissing]
  exact saturated_of_general_fields missing 17 bits hcore hm htoH hp hph

theorem saturated_m2_ph16_of_general (bits : BitVec 218)
    (h : ThreeZHighDefect.highDefectCoreAtDefects 2 1 0 bits = true)
    (hph : ThreeZHighDefect.phComplete bits = true) :
    ThreeZSaturated.saturatedCoreAtMissingPToH 2 16
      (saturatedBits bits) = true := by
  simp only [ThreeZHighDefect.highDefectCoreAtDefects,
    ThreeZHighDefect.pCompatibleAtDefect, if_pos] at h
  have ⟨h4, _hcompatPH⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h3, hp⟩ := Bool.and_eq_true_iff.mp h4
  have ⟨hleft, _htoP⟩ := Bool.and_eq_true_iff.mp h3
  have ⟨hcm, htoH0⟩ := Bool.and_eq_true_iff.mp hleft
  simp only [ThreeZHighDefect.highDefectCoreAtMissing] at hcm
  have ⟨hcore, hm0⟩ := Bool.and_eq_true_iff.mp hcm
  have hm : ThreeZHighDefect.totalMissingPZ bits = BitVec.ofNat 8 2 :=
    of_decide_eq_true hm0
  have htoH : ThreeZHighDefect.totalPToH bits = BitVec.ofNat 8 16 := by
    have heq : ThreeZHighDefect.totalPToH bits + (1 : BitVec 8) =
        (16 : BitVec 8) + 1 := by
      simpa using of_decide_eq_true htoH0
    bv_omega
  exact saturated_of_general_fields 2 16 bits hcore hm htoH hp hph

theorem saturated_m2_of_general (bits : BitVec 218)
    (h : ThreeZHighDefect.highDefectCoreAtDefects 2 0 0 bits = true) :
    ThreeZSaturated.saturatedCoreAtMissing 2 (saturatedBits bits) = true :=
  saturated_of_general 2 bits h

theorem saturated_m3_of_general (bits : BitVec 218)
    (h : ThreeZHighDefect.highDefectCoreAtDefects 3 0 0 bits = true) :
    ThreeZSaturated.saturatedCoreAtMissing 3 (saturatedBits bits) = true :=
  saturated_of_general 3 bits h

end SeymourEight.ThreeZHighDefectCompression
