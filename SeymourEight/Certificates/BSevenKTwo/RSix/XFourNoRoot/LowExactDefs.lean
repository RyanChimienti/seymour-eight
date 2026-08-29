import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.MTwoCoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore

open Shared.FiniteCore

def lowTotals (alpha beta : Nat) (bits : Encoding) : Bool :=
  (count 18 (fun n => pToE bits (n / 3) (n % 3)) == 17) &&
  (count 30 (fun n =>
    let p := n / 5
    let j := n % 5
    pArc bits p (if j < p then j else j + 1)) == 15 - beta) &&
  (count 36 (fun n => pToH bits (n / 6) (n % 6)) == 17 - alpha) &&
  ((19 : BitVec 8).ule (count 36 fun n => hToP bits (n / 6) (n % 6)))

def lowPConditions (bits : Encoding) : Bool := all 6 fun p =>
  (8 : BitVec 8).ule (pOut bits p) &&
  (pLocalSecondCount bits p + pOutsideSecondSeven bits p).ult (pOut bits p) &&
  (!(pOut bits p == 8) || all 3 (fun deleted => !pToE bits p deleted ||
    (7 : BitVec 8).ule (deletionCountESeven bits p deleted)))

def lowPNoDeletion (bits : Encoding) : Bool := all 6 fun p =>
  (8 : BitVec 8).ule (pOut bits p) &&
  (pLocalSecondCount bits p + pOutsideSecondSeven bits p).ult (pOut bits p)

def lowExactCore (alpha beta : Nat) (bits : Encoding) : Bool :=
  oriented bits && hToQ bits 0 && hToQ bits 1 &&
    everyXReached bits && hConditions bits && rConditions bits &&
    lowTotals alpha beta bits &&
    xConditionsSeven bits && eConditionsSeven bits

def saturatedPP (bits : Encoding) : Bool :=
  all 6 fun p => all 6 fun q => decide (p = q) ||
    pArc bits p q || pArc bits q p

def saturatedPH (bits : Encoding) : Bool :=
  (all 6 fun p => all 6 fun h => pToH bits p h || hToP bits h p) &&
    (count 36 (fun n => hToP bits (n / 6) (n % 6)) == 19)

def completePH (bits : Encoding) : Bool :=
  all 6 fun p => all 6 fun h => pToH bits p h || hToP bits h p

def missingPHPair (bits : Encoding) (n : Nat) : Bool :=
  !(pToH bits (n / 6) (n % 6) || hToP bits (n % 6) (n / 6))

def atMostOneMissingPH (bits : Encoding) : Bool :=
  all 36 fun n => all 36 fun m => decide (n = m) ||
    !(missingPHPair bits n && missingPHPair bits m)

def orderedXOnly (bits : Encoding) : Bool := all 3 fun x =>
  (16 * hPOut bits (3 + x) + count 6 (fun p => pToH bits p (3 + x))).ule
    (16 * hPOut bits (2 + x) + count 6 (fun p => pToH bits p (2 + x)))

def orderedETail (bits : Encoding) : Bool :=
  (count 6 fun p => pToE bits p 2).ule (count 6 fun p => pToE bits p 1)

/-- The part of `N⁺(E) \ (P ∪ E)` visible in the eight `A` labels, the
root label, and the seven outside labels.  These are exactly its possible
vertices in the graph bridge. -/
def effectiveAuxUnionCount (bits : Encoding) : BitVec 8 :=
  count 9 (fun n => any 3 fun e =>
    eLocalArc bits e (if n < 8 then n else 17)) +
  count 7 (fun w => any 3 fun e => outsideAdjSeven bits w e)

/-- A row witnessing the seven-vertex effective union: it sees all three
auxiliaries, and exactly seven encoded strict second neighbors are reached
through the retained/outside partition. -/
def badFullAuxRow (bits : Encoding) : Bool := any 6 fun p =>
  (all 3 fun e => pToE bits p e) &&
    pLocalSecondCount bits p + pOutsideSecondSeven bits p == 7

def pSecondPCount (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 6 fun q => pStrictSecondLocal bits p (8 + q)

/-- The individual effective-union inequality.  At total auxiliary defect one,
rows see either two auxiliaries (effective contribution eight) or all three
(effective contribution seven). -/
def lowEffectivePConditions (bits : Encoding) : Bool := all 6 fun p =>
  (pSecondPCount bits p + (if pEOut bits p == 2 then 9 else 8)).ule
    (pPOut bits p + 2 * pHOut bits p + pEOut bits p)

/-- Equality structure forced by the sharp `H` degree-capacity bound in the
`c=1` row. -/
def tightHStructure (bits : Encoding) : Bool :=
  (all 4 fun x => hToQ bits (2 + x) && hToAOne bits (2 + x) &&
    hToR bits (2 + x)) &&
  (all 6 fun i => all 6 fun j => decide (i = j) || hArc bits i j || hArc bits j i)

/-- With one missing `P → E` incidence, the row ordering puts the unique
deficient row last; the tail-column ordering leaves only columns zero or two
as the missing position. -/
def canonicalPEOneMissing (bits : Encoding) : Bool :=
  (all 5 fun p => all 3 fun e => pToE bits p e) && pToE bits 5 1 &&
    ((!pToE bits 5 0 && pToE bits 5 2) ||
      (pToE bits 5 0 && !pToE bits 5 2))

def lowExactCore00 (bits : Encoding) : Bool :=
  (oriented bits && hToQ bits 0 && hToQ bits 1 &&
      everyXReached bits && hConditions bits && rConditions bits &&
      lowTotals 0 0 bits && xConditionsSeven bits && eConditionsSeven bits) &&
    lowPNoDeletion bits && saturatedPairRectangles bits

def lowExactCore10 (bits : Encoding) : Bool :=
  lowExactCore 1 0 bits && (all 6 fun p => pOut bits p == 8) &&
    auxiliaryDeletionPConditionsSeven bits && saturatedPP bits

def lowExactCore10HP (hp : Nat) (bits : Encoding) : Bool :=
  lowExactCore10 bits &&
    (count 36 (fun n => hToP bits (n / 6) (n % 6)) == hp) &&
    if hp = 20 then completePH bits else true

def lowExactCore10HPCode (hp code : Nat) (bits : Encoding) : Bool :=
  lowExactCore10HP hp bits && (all 5 fun p => pECode bits p == 7) &&
    pECode bits 5 == code

def lowAuxPattern (outside internal reverse : Nat) (bits : Encoding) : Bool :=
  (count 21 (fun n => outsideAdjSeven bits (n % 7) (n / 7)) == outside) &&
    (count 9 (fun n => eArc bits (n / 3) (n % 3)) == internal) &&
    (count 18 (fun n => eToP bits (n / 6) (n % 6)) == reverse)

def lowExactCore10Leaf (hp code outside internal reverse : Nat)
    (bits : Encoding) : Bool :=
  lowExactCore10HPCode hp code bits &&
    lowAuxPattern outside internal reverse bits && lowPNoDeletion bits

def lowExactCore10Code (hp code : Nat) (bits : Encoding) : Bool :=
  lowExactCore10HPCode hp code bits && lowPNoDeletion bits

def lowExactCore10All (hp : Nat) (bits : Encoding) : Bool :=
  lowExactCore10HP hp bits && lowPNoDeletion bits

def lowExactCore01 (bits : Encoding) : Bool :=
  lowExactCore 0 1 bits && (all 6 fun p => pOut bits p == 8) &&
    auxiliaryDeletionPConditionsSeven bits && saturatedPH bits

def lowExactCore01Code (code : Nat) (bits : Encoding) : Bool :=
  lowExactCore01 bits && lowPNoDeletion bits &&
    (all 5 fun p => pECode bits p == 7) &&
    pECode bits 5 == code

def lowExactCore01All (bits : Encoding) : Bool :=
  lowExactCore01 bits && lowPNoDeletion bits

/-- The `c = 1, m = 1` residual, after naming the unique `A₁ → q`
source first.  No ordering predicate depends on the two `A₁` labels. -/
def lowExactCOneMOne (bits : Encoding) : Bool :=
  orderedP bits && orderedXOnly bits && orderedETail bits && oriented bits &&
    hToQ bits 0 && !hToQ bits 1 && everyXReached bits &&
    hConditions bits && rConditions bits &&
    (count 18 (fun n => pToE bits (n / 3) (n % 3)) == 17) &&
    (count 30 (fun n =>
      let p := n / 5
      let j := n % 5
      pArc bits p (if j < p then j else j + 1)) == 15) &&
    (count 36 (fun n => pToH bits (n / 6) (n % 6)) == 16) &&
    ((20 : BitVec 8).ule (count 36 fun n => hToP bits (n / 6) (n % 6))) &&
    xConditionsSeven bits && eConditionsSeven bits &&
    (all 6 fun p => pOut bits p == 8) &&
    auxiliaryDeletionPConditionsSeven bits && saturatedPP bits &&
    completePH bits && lowPNoDeletion bits && lowEffectivePConditions bits &&
    tightHStructure bits && canonicalPEOneMissing bits

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.MTwoCore
