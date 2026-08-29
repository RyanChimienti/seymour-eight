import SeymourEight.Shared.FiniteCore

/-!
# Finite core for the no-root `r = 6`, `x = 4` rows

The three auxiliary columns are `Z` in the unreached-`Q` row and the reached
member of `Q` followed by `Z` in the other row.  Keeping this union intact
avoids a split by the number of `A₁ → Q` arcs or by external defect.
-/

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core

open Shared.FiniteCore

abbrev Encoding := BitVec 136

def directedIndex (i j : Nat) : Nat := 5 * i + if j < i then j else j - 1

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (directedIndex i j)

def pToH (bits : Encoding) (p h : Nat) : Bool :=
  bits.getLsbD (30 + 6 * p + h)

def hToP (bits : Encoding) (h p : Nat) : Bool :=
  bits.getLsbD (66 + 6 * h + p)

def pToE (bits : Encoding) (p e : Nat) : Bool :=
  bits.getLsbD (102 + 3 * p + e)

def aPair (bits : Encoding) (i j : Nat) : Bool :=
  decide (i ≠ j) && bits.getLsbD (120 + i)

def aToX (bits : Encoding) (a x : Nat) : Bool :=
  bits.getLsbD (122 + 4 * a + x)

def aToE (bits : Encoding) (a e : Nat) : Bool :=
  bits.getLsbD (130 + 3 * a + e)

def pOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pArc bits p)
def pHOut (bits : Encoding) (p : Nat) : BitVec 8 := count 6 (pToH bits p)
def pEOut (bits : Encoding) (p : Nat) : BitVec 8 := count 3 (pToE bits p)

def pReached (bits : Encoding) (p q : Nat) : Bool :=
  any 6 (fun middle => decide (middle ≠ p) && decide (middle ≠ q) &&
    pArc bits p middle && pArc bits middle q) ||
  any 6 (fun h => pToH bits p h && hToP bits h q)

def pSecond (bits : Encoding) (p q : Nat) : Bool :=
  decide (p ≠ q) && !pArc bits p q && pReached bits p q

def pSecondCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 (pSecond bits p)

def totalHP (bits : Encoding) : BitVec 8 :=
  count 36 fun n => hToP bits (n / 6) (n % 6)

def totalPH (bits : Encoding) : BitVec 8 :=
  count 36 fun n => pToH bits (n / 6) (n % 6)

def totalPP (bits : Encoding) : BitVec 8 :=
  count 30 fun n =>
    let p := n / 5
    let j := n % 5
    pArc bits p (if j < p then j else j + 1)

def totalPE (bits : Encoding) : BitVec 8 :=
  count 18 fun n => pToE bits (n / 3) (n % 3)

def qSourceCount (bits : Encoding) : BitVec 8 :=
  count 2 fun a => aToE bits a 0

def pRowKey (bits : Encoding) (p : Nat) : BitVec 16 :=
  (pOut bits p + pHOut bits p + pEOut bits p).zeroExtend 16 * 4096 +
    (pEOut bits p).zeroExtend 16 * 256 +
    (pHOut bits p).zeroExtend 16 * 16 + (pOut bits p).zeroExtend 16

def orderedP (bits : Encoding) : Bool :=
  all 5 fun p => (pRowKey bits (p + 1)).ule (pRowKey bits p)

def hPOut (bits : Encoding) (h : Nat) : BitVec 8 := count 6 (hToP bits h)

def orderedH (bits : Encoding) : Bool :=
  (hPOut bits 1).ule (hPOut bits 0) &&
    all 3 fun x => (hPOut bits (3 + x)).ule (hPOut bits (2 + x))

def ePIn (bits : Encoding) (e : Nat) : BitVec 8 :=
  count 6 fun p => pToE bits p e

def orderedZ (bits : Encoding) : Bool := (ePIn bits 2).ule (ePIn bits 1)

def auxiliaryContribution (bits : Encoding) : BitVec 8 :=
  if (17 : BitVec 8).ule (totalPE bits) then 8 else 6

/-- The elementary row-wise capacity bound.  Unlike the stronger common-union
bound used by `core`, this also applies in the exact two-defect branch. -/
def individualContribution (bits : Encoding) (p : Nat) : BitVec 8 :=
  if totalPE bits == 18 then 7
  else if totalPE bits == 17 then
    if pEOut bits p == 2 then 8 else 7
  else if pEOut bits p == 1 then 8 else 7

def oriented (bits : Encoding) : Bool :=
  (all 6 fun i => all 6 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)) &&
  (all 6 fun p => all 6 fun h => !(pToH bits p h && hToP bits h p)) &&
  !(aPair bits 0 1 && aPair bits 1 0)

def orientedBasic (bits : Encoding) : Bool :=
  (all 6 fun i => all 6 fun j =>
    decide (i = j) || !(pArc bits i j && pArc bits j i)) &&
  (all 6 fun p => all 6 fun h => !(pToH bits p h && hToP bits h p))

def fixedAuxiliarySources (bits : Encoding) : Bool :=
  all 2 fun a => !aToE bits a 1 && !aToE bits a 2

def everyTargetReached (bits : Encoding) : Bool :=
  (all 4 fun x =>
    any 2 (fun a => aToX bits a x) ||
      any 6 (fun p => pToH bits p (2 + x))) &&
  (all 3 fun e => any 6 fun p => pToE bits p e)

def aOneConditions (bits : Encoding) : Bool := all 2 fun a =>
  let internal := count 2 (aPair bits a) + count 4 (aToX bits a)
  let toB := count 6 (hToP bits a) + count 3 (aToE bits a)
  (2 : BitVec 8).ule internal && (8 : BitVec 8).ule (internal + toB) &&
    (!(internal == 2) || (6 : BitVec 8).ule (count 6 (hToP bits a)))

def retainedToX (bits : Encoding) (deleted x : Nat) : Bool :=
  any 8 fun u => decide (u ≠ deleted) &&
    if u < 2 then aToX bits u x else pToH bits (u - 2) (2 + x)

def retainedToE (bits : Encoding) (deleted e : Nat) : Bool :=
  any 8 fun u => decide (u ≠ deleted) &&
    if u < 2 then aToE bits u e else pToE bits (u - 2) e

def retainedToDeleted (bits : Encoding) (deleted : Nat) : Bool :=
  any 8 fun u => decide (u ≠ deleted) &&
    if u < 2 then
      if deleted < 2 then aPair bits u deleted
      else hToP bits u (deleted - 2)
    else
      if deleted < 2 then pToH bits (u - 2) deleted
      else pArc bits (u - 2) (deleted - 2)

def sevenSetExpansion (bits : Encoding) : Bool := all 8 fun deleted =>
  (7 : BitVec 8).ule
    (count 4 (retainedToX bits deleted) +
      count 3 (retainedToE bits deleted) +
      bitCount (retainedToDeleted bits deleted))

def pConditions (bits : Encoding) : Bool := all 6 fun p =>
  (8 : BitVec 8).ule (pOut bits p + pHOut bits p + pEOut bits p) &&
  (pSecondCount bits p + auxiliaryContribution bits + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut bits p)

def individualPConditions (bits : Encoding) : Bool := all 6 fun p =>
  (8 : BitVec 8).ule (pOut bits p + pHOut bits p + pEOut bits p) &&
  (pSecondCount bits p + individualContribution bits p + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut bits p)

def coreAt (c : Nat) (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && orientedBasic bits &&
  (21 : BitVec 8).ule (totalHP bits + c) &&
  (17 : BitVec 8).ule (totalPE bits) && pConditions bits

def core (bits : Encoding) : Bool := coreAt 0 bits

def coreCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  coreAt c bits && totalPE bits == 18 - m &&
    totalPH bits == 15 + c - alpha && totalPP bits == 15 - beta

def individualCore (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits &&
  oriented bits && fixedAuxiliarySources bits && everyTargetReached bits &&
  aOneConditions bits && sevenSetExpansion bits &&
  (21 : BitVec 8).ule (totalHP bits + qSourceCount bits) &&
  individualPConditions bits

def individualCoreCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  individualCore bits && qSourceCount bits == c && totalPE bits == 18 - m &&
    totalPH bits == 15 + c - alpha && totalPP bits == 15 - beta

def sharpKingZero (bits : Encoding) : Bool :=
  any 6 fun p => (5 : BitVec 8).ule (pOut bits p + pSecondCount bits p)

def equalExternalClassReach (bits : Encoding) : Bool :=
  all 6 fun p => all 6 fun q => decide (p = q) ||
    !(pEOut bits p == pEOut bits q) || pArc bits p q || pSecond bits p q

def pReachedAfterLocalDelete (bits : Encoding) (p kind deleted q : Nat) : Bool :=
  any 6 (fun middle => decide (middle ≠ p) && decide (middle ≠ q) &&
    !(kind == 0 && middle == deleted) &&
    pArc bits p middle && pArc bits middle q) ||
  any 6 (fun h => !(kind == 1 && h == deleted) &&
    pToH bits p h && hToP bits h q)

def pSecondAfterLocalDelete
    (bits : Encoding) (p kind deleted q : Nat) : Bool :=
  decide (p ≠ q) &&
    (if kind == 0 && q == deleted then
      pReachedAfterLocalDelete bits p kind deleted q
    else !pArc bits p q && pReachedAfterLocalDelete bits p kind deleted q)

def pSecondAfterLocalDeleteCount
    (bits : Encoding) (p kind deleted : Nat) : BitVec 8 :=
  count 6 (pSecondAfterLocalDelete bits p kind deleted)

def contributionAfterEDelete (bits : Encoding) (p : Nat) : BitVec 8 :=
  if pEOut bits p == 1 then 0 else if pEOut bits p == 2 then 8 else 7

def exactTailDeletionConditions (bits : Encoding) : Bool := all 6 fun p =>
  (all 6 fun q => !pArc bits p q ||
      (7 : BitVec 8).ule
        (pSecondAfterLocalDeleteCount bits p 0 q +
          individualContribution bits p)) &&
  (all 6 fun h => !pToH bits p h ||
      (7 : BitVec 8).ule
        (pSecondAfterLocalDeleteCount bits p 1 h +
          individualContribution bits p)) &&
  (all 3 fun e => !pToE bits p e ||
      (7 : BitVec 8).ule
        (pSecondAfterLocalDeleteCount bits p 2 e +
          contributionAfterEDelete bits p))

def individualKingCoreCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  individualCoreCase c m alpha beta bits && sharpKingZero bits &&
    equalExternalClassReach bits && exactTailDeletionConditions bits

def coreNoSeven (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits &&
  oriented bits && fixedAuxiliarySources bits && everyTargetReached bits &&
  aOneConditions bits &&
  (21 : BitVec 8).ule (totalHP bits + qSourceCount bits) &&
  (17 : BitVec 8).ule (totalPE bits) && pConditions bits

def coreNoSevenCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  coreNoSeven bits && qSourceCount bits == c && totalPE bits == 18 - m &&
    totalPH bits == 15 + c - alpha && totalPP bits == 15 - beta

def coreLean (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
  fixedAuxiliarySources bits && aOneConditions bits &&
  (21 : BitVec 8).ule (totalHP bits + qSourceCount bits) &&
  (17 : BitVec 8).ule (totalPE bits) && pConditions bits

def coreLeanCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  coreLean bits && qSourceCount bits == c && totalPE bits == 18 - m &&
    totalPH bits == 15 + c - alpha && totalPP bits == 15 - beta

def coreUltra (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && oriented bits &&
  fixedAuxiliarySources bits &&
  (21 : BitVec 8).ule (totalHP bits + qSourceCount bits) &&
  (17 : BitVec 8).ule (totalPE bits) && pConditions bits

def coreUltraCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  coreUltra bits && qSourceCount bits == c && totalPE bits == 18 - m &&
    totalPH bits == 15 + c - alpha && totalPP bits == 15 - beta

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.Core
