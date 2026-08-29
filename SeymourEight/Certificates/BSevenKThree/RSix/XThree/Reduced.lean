import SeymourEight.Certificates.BSevenKThree.RSix.XThree.Tactic

namespace SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core

open Shared.FiniteCore

def pLexLe (zCount : Nat) (arc : Nat → Nat → Bool) (i j : Nat) : Bool :=
  let di := pDegree zCount arc i
  let dj := pDegree zCount arc j
  let zi := pZOut zCount arc i
  let zj := pZOut zCount arc j
  let qi := bitCount (arc (8+i) 14)
  let qj := bitCount (arc (8+j) 14)
  let ai := count 3 fun a => arc (8+i) (1+a)
  let aj := count 3 fun a => arc (8+j) (1+a)
  let xi := count 3 fun x => arc (8+i) (4+x)
  let xj := count 3 fun x => arc (8+j) (4+x)
  di.ult dj || (di == dj &&
    (zi.ult zj || (zi == zj &&
      (qi.ult qj || (qi == qj &&
        (ai.ult aj || (ai == aj &&
          (xi.ult xj || (xi == xj && (pOut arc i).ule (pOut arc j))))))))))

def reducedOrdered (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  (all 5 fun p => pLexLe zCount arc (p+1) p) &&
  (all 2 fun a => (aBOut arc (a+2)).ule (aBOut arc (a+1))) &&
  (all 2 fun x => (aBOut arc (x+5)).ule (aBOut arc (x+4))) &&
  (all (zCount-1) fun z =>
    (count 6 fun p => arc (8+p) (16+z)).ule
      (count 6 fun p => arc (8+p) (15+z)))

def genericEffectiveFour (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  let m := externalMissing 3 arc; let s := pAuxOut 3 arc p
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
  let m := externalMissing 4 arc; let s := pAuxOut 4 arc p
  if m == 0 then effectiveAt s 12 9 8 7 6
  else if m == 1 then effectiveAt s 11 9 8 7 6
  else if m == 2 then effectiveAt s 10 8 7 7 6
  else if m == 3 then effectiveAt s 9 8 7 6 6
  else if m == 4 then effectiveAt s 8 7 7 6 6
  else if m == 5 then effectiveAt s 7 7 6 6 5
  else if m == 6 then effectiveAt s 6 6 6 6 5
  else if m == 7 then effectiveAt s 5 6 6 5 5
  else if m == 8 then effectiveAt s 4 5 5 5 5
  else if m == 9 then effectiveAt s 0 4 5 5 5
  else if m == 10 then effectiveAt s 0 4 5 5 4
  else if m == 11 then effectiveAt s 0 4 4 4 4
  else effectiveAt s 0 3 4 4 4

def genericEffective (zCount : Nat) (arc : Nat → Nat → Bool) (p : Nat) : BitVec 8 :=
  if zCount = 3 then genericEffectiveFour arc p else genericEffectiveFive arc p

def pGenericEffective (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun p => (pSecondP arc p + genericEffective zCount arc p + 1).ule
    (pOut arc p + 2 * pHOut arc p + pAuxOut zCount arc p)

def reducedCoreFn (zCount : Nat) (arc : Nat → Nat → Bool) : Bool :=
  orientedA arc && orientedP arc && orientedAPQ arc && fixedPivot arc &&
  everyXReached arc && rUnreached arc && qReached arc && allZReached zCount arc &&
  aMinimumAndPivot arc && aNonSeymour zCount arc && pMinimum zCount arc &&
  all 8 (hallCondition zCount arc) && degreeThreeClassification arc &&
  threeInnerWitnesses arc && arithmetic zCount arc && pGenericEffective zCount arc && sharpKing arc &&
  reducedOrdered zCount arc

def reducedCore (zCount : Nat) (bits : Encoding) : Bool :=
  reducedCoreFn zCount (encodedArc bits)

macro "r6x3_reduced_simp" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only
    [reducedCore, reducedCoreFn, orientedA, orientedP, orientedAPQ,
    fixedPivot, everyXReached, rUnreached, qReached, allZReached,
    aMinimumAndPivot, aNonSeymour, pMinimum, hallCondition,
    degreeThreeClassification, threeInnerWitnesses, arithmetic, pGenericEffective,
    genericEffective, genericEffectiveFour, genericEffectiveFive, effectiveAt, sharpKing,
    sharpKingLower, beta, alpha, etaH, tau, qDefect, crossMissing,
    degreeGain, aMissing, totalAOut, totalHToP, totalPToH, totalPOut,
    totalHOut, totalPAux, externalMissing, secondCount, strictSecond, reaches, innerSeymour,
    innerSecondCount, innerSecond, innerReaches, hallCount, hallReached,
    degreeThreeInner, degreeThree, pDegree, pAuxOut, pSecondP, pZOut,
    aOut, aPOut, aBOut, pOut, pHOut, hPOut, reducedOrdered, pLexLe,
    encodedArc, directedIndex, Shared.FiniteCore.sumCount,
    Shared.FiniteCore.count, Shared.FiniteCore.bitCount,
    Shared.FiniteCore.any, Shared.FiniteCore.all])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- The compact obstruction is a 191-bit finite decision problem.
theorem four_reduced_unsat (bits : Encoding) : reducedCore 3 bits = false := by
  r6x3_reduced_simp
  bv_decide (config := { timeout := 600, acNf := true })

end SeymourEight.BSevenKThree.RSix.XThreeNoRoot.Core
