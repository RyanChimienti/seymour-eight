import SeymourEight.Certificates.BSevenKTwo.RSeven.XFour.ZThreeCoreDefs

/-!
# Finite normalization of the two missing `P → Z` incidences

Rows are ordered by increasing direct `Z` degree.  Columns are ordered first
by their number of missing incidences and, inside a tie, by whether `p0`
misses them.  This chooses one of the three genuine two-cell orbits without
constraining any internal `P` incidence.
-/

namespace SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeNormalization

open ZThreeCore

def zIn (bits : Encoding) (z : Nat) : BitVec 8 :=
  count 7 fun p => pToZ bits p z

def zOrbitKey (bits : Encoding) (z : Nat) : BitVec 8 :=
  2 * (7 - zIn bits z) + bitCount (!pToZ bits 0 z)

def orderedExternalRows (bits : Encoding) : Bool :=
  all 6 fun p => (pZOut bits p).ule (pZOut bits (p + 1))

def orderedExternalZ (bits : Encoding) : Bool :=
  all 2 fun z => (zOrbitKey bits (z + 1)).ule (zOrbitKey bits z)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 512000000 in
theorem externalOrbit_of_ordered (bits : Encoding)
    (hTotal : (totalPToZ bits == 19) = true)
    (hRows : orderedExternalRows bits = true)
    (hZ : orderedExternalZ bits = true) :
    externalOrbit 0 bits || externalOrbit 1 bits || externalOrbit 2 bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [totalPToZ, orderedExternalRows, orderedExternalZ, zOrbitKey, zIn,
     externalOrbit, pZPattern, pZOut, pToZ, all, count, bitCount,
     Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hTotal hRows hZ ⊢
  bv_decide

end SeymourEight.BSevenKTwo.RSeven.XFourNoRoot.ZThreeNormalization
