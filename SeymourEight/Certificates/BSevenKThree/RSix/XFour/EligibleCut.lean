import SeymourEight.Certificates.BSevenKThree.RSix.XFour.StrongDualDefs

/-!
# Direct capacity cut for eligible H vertices

The seven `H` degree inequalities force a useful aggregate bound: the reverse
`H → P` count plus the number of degree-eight `H` vertices pointing to `Q`
is at least the missing capacity in the `A` block.  Keeping this redundant
cut in a tiny isolated certificate greatly improves propagation in the
delta-zero positive-alpha obstruction.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual

open Core Shared.FiniteCore

def eligibleCapacityCut (arc : Nat → Nat → Bool) : Bool :=
  (31 + aMissing arc).ule (totalHToP arc + eligibleHCount arc)

def eligibleCapacityConsequence (arc : Nat → Nat → Bool) : Bool :=
  !(aOut arc 0 == 3) || !aConditions arc || eligibleCapacityCut arc

theorem aOut_zero_eq_three_of_fixed {arc : Nat → Nat → Bool}
    (hFixed : fixedAOne arc = true) : aOut arc 0 = 3 := by
  rw [fixedAOne, all_eq_true_iff] at hFixed
  have h0 := beq_iff_eq.mp (hFixed 0 (by omega))
  have h1 := beq_iff_eq.mp (hFixed 1 (by omega))
  have h2 := beq_iff_eq.mp (hFixed 2 (by omega))
  have h3 := beq_iff_eq.mp (hFixed 3 (by omega))
  have h4 := beq_iff_eq.mp (hFixed 4 (by omega))
  have h5 := beq_iff_eq.mp (hFixed 5 (by omega))
  have h6 := beq_iff_eq.mp (hFixed 6 (by omega))
  have h7 := beq_iff_eq.mp (hFixed 7 (by omega))
  simp [aOut, aArc, count, bitCount, h0, h1, h2, h3, h4, h5, h6, h7]

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem eligibleCapacityConsequence_true (arc : Nat → Nat → Bool) :
    eligibleCapacityConsequence arc = true := by
  simp (config := { maxSteps := 1000000 }) only
    [eligibleCapacityConsequence, eligibleCapacityCut, eligibleHCount,
      aConditions, totalHToP, aMissing, totalAOut, aDegree, hPOut, aBOut,
      aPOut, aOut, aToQ, aToP, aArc, sumCount, count, bitCount, all]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.StrongDual
