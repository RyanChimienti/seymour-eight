import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Reduced

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

abbrev Encoding := BitVec 197

def encodedArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then
      if u = 0 then decide (1 ≤ v && v ≤ 3)
      else if v = 0 then
        if u ≤ 3 then false else bits.getLsbD (u - 4)
      else decide (u ≠ v) && bits.getLsbD (4 + directedIndex 7 (u - 1) (v - 1))
    else if v < 14 then
      if u = 0 then true else bits.getLsbD (76 + 6 * (u - 1) + (v - 8))
    else if v = 14 then
      if u = 0 then false else bits.getLsbD (154 + (u - 1))
    else false
  else if u < 14 then
    if v < 8 then
      if 1 ≤ v && v ≤ 6 then bits.getLsbD (118 + 6 * (u - 8) + (v - 1))
      else false
    else if v < 14 then
      decide (u ≠ v) && bits.getLsbD (46 + directedIndex 6 (u - 8) (v - 8))
    else if v < 20 then bits.getLsbD (161 + 6 * (u - 8) + (v - 14))
    else false
  else false

def qUnreached (arc : Nat → Nat → Bool) : Bool :=
  (all 3 fun a => !arc (1+a) 14) && (all 6 fun p => !arc (8+p) 14)

def totalPZ (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  sumCount 6 (pZOut zCount arc)

def externalMissing (zCount : Nat) (arc : Nat → Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 (6 * zCount) - totalPZ zCount arc

def genericEffectiveFour (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  let m := externalMissing 4 arc; let s := pZOut 4 arc p
  if m == 0 then effectiveAt s 11 9 8 7 7
  else if m == 1 then effectiveAt s 10 8 7 7 7
  else if m == 2 then effectiveAt s 9 8 7 6 6
  else if m == 3 then effectiveAt s 8 7 7 6 6
  else if m == 4 then effectiveAt s 7 7 6 6 6
  else if m == 5 then effectiveAt s 6 6 6 6 6
  else if m == 6 then effectiveAt s 5 6 6 5 5
  else if m == 7 then effectiveAt s 4 5 5 5 5
  else if m == 8 then effectiveAt s 3 5 5 5 5
  else effectiveAt s 2 4 5 5 5

def genericEffectiveFive (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  let m := externalMissing 5 arc; let s := pZOut 5 arc p
  if m == 0 then effectiveAt s 12 9 8 7 6
  else if m == 1 then effectiveAt s 11 9 8 7 6
  else if m == 2 then effectiveAt s 10 8 7 7 6
  else if m == 3 then effectiveAt s 9 8 7 6 6
  else if m == 4 then effectiveAt s 8 7 7 6 6
  else if m == 5 then effectiveAt s 7 7 6 6 5
  else if m == 6 then effectiveAt s 6 6 6 6 5
  else if m == 7 then effectiveAt s 5 6 6 5 5
  else if m == 8 then effectiveAt s 4 5 5 5 5
  else effectiveAt s 0 4 5 5 5

def genericEffective (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  if zCount = 4 then genericEffectiveFour arc p else genericEffectiveFive arc p

def pGenericEffective (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun p => (pSecondP arc p + genericEffective zCount arc p + 1).ule
    (pOut arc p + 2 * pHOut arc p + pZOut zCount arc p)

def reducedCoreFn (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedAPQ arc && fixedPivot arc &&
  everyXReached arc && rUnreached arc && qUnreached arc && allZReached zCount arc &&
  aMinimumAndPivot arc && aNonSeymour zCount arc && pMinimum zCount arc &&
  all 8 (hallCondition zCount arc) && degreeThreeClassification arc &&
  threeInnerWitnesses arc && arithmetic zCount arc && pGenericEffective zCount arc &&
  sharpKing arc && reducedOrdered zCount arc

def reducedCore (zCount : Nat) (bits : Encoding) : Bool :=
  reducedCoreFn zCount (encodedArc bits)

macro "r6x3_unreached_simp" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only
    [reducedCore, reducedCoreFn, qUnreached, totalPZ, externalMissing,
    genericEffective, genericEffectiveFour, genericEffectiveFive,
    pGenericEffective, Core.orientedA, Core.orientedP, Core.orientedAPQ,
    Core.fixedPivot, Core.everyXReached, Core.rUnreached, Core.allZReached,
    Core.aMinimumAndPivot, Core.aNonSeymour, Core.pMinimum, Core.hallCondition,
    Core.degreeThreeClassification, Core.threeInnerWitnesses, Core.arithmetic,
    Core.effectiveAt, Core.sharpKing, Core.sharpKingLower, Core.beta, Core.alpha,
    Core.etaH, Core.tau, Core.qDefect, Core.crossMissing, Core.degreeGain,
    Core.aMissing, Core.totalAOut, Core.totalHToP, Core.totalPToH,
    Core.totalPOut, Core.totalHOut, Core.secondCount, Core.strictSecond,
    Core.reaches, Core.innerSeymour, Core.innerSecondCount, Core.innerSecond,
    Core.innerReaches, Core.hallCount, Core.hallReached, Core.degreeThreeInner,
    Core.degreeThree, Core.pDegree, Core.pAuxOut, Core.pSecondP, Core.pZOut,
    Core.aOut, Core.aPOut, Core.aBOut, Core.pOut, Core.pHOut, Core.hPOut,
    Core.reducedOrdered, Core.pLexLe, encodedArc, Core.directedIndex,
    Shared.FiniteCore.sumCount, Shared.FiniteCore.count,
    Shared.FiniteCore.bitCount, Shared.FiniteCore.any, Shared.FiniteCore.all])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- The four-external-target unreached obstruction is a finite 197-bit decision.
theorem four_unsat (bits : Encoding) : reducedCore 4 bits = false := by
  r6x3_unreached_simp
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.UnreachedCore
