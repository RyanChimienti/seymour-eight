import SeymourEight.Certificates.BSevenKThree.RSix.XFour.ActualTailDefs

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompactActualTail

open Shared.FiniteCore Core AuxiliaryCore ActualTail

def auxArcSubReal (auxArc realAuxArc : Nat → Nat → Bool) : Bool :=
  all 4 fun i => all 19 fun target => !auxArc i target || realAuxArc i target

def namedSecondCount (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p : Nat) : BitVec 8 :=
  count 19 (actualSecondNamed arc pToZ realAuxArc p)

def namedDeletionConditions (arc pToZ realAuxArc : Nat → Nat → Bool)
    (p : Nat) : Bool :=
  all 17 fun d =>
    let deleted := 1 + d
    !pDirect arc pToZ p deleted ||
      (namedSecondCount arc pToZ realAuxArc p).ule
        (count 19 (deletionSecondNamed arc pToZ realAuxArc p deleted))

def compactActualTailCore (p : Nat)
    (arc pToZ auxArc realAuxArc : Nat → Nat → Bool) : Bool :=
  canonicalAuxiliaryCore arc pToZ auxArc &&
    pDegree 1 3 arc pToZ p == 8 &&
    actualAuxiliaryOriented arc pToZ realAuxArc &&
    auxArcSubReal auxArc realAuxArc &&
    (namedSecondCount arc pToZ realAuxArc p).ule 7 &&
    namedDeletionConditions arc pToZ realAuxArc p

def compactCapacityRangeLeaf (capacity lower upper : Nat)
    (arc pToZ auxArc realAuxArc : Nat → Nat → Bool) : Bool :=
  commonCore 1 3 arc pToZ &&
    capacityDefect arc pToZ == BitVec.ofNat 8 capacity &&
    compactActualTailCore (6 - capacity) arc pToZ auxArc realAuxArc &&
    (BitVec.ofNat 8 lower).ule (externalMissing 1 3 arc pToZ) &&
    (externalMissing 1 3 arc pToZ).ule (BitVec.ofNat 8 upper)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.CompactActualTail
