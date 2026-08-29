import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.CoreDefs

/-!
# Compact one-vertex-expansion cores

For four or six external targets, the degree-seven theorem applied to the
seven `P` outneighbors of `a₁` already supplies the decisive reduction.
-/

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core

def pUnionTarget (zCount : Nat) (bits : Encoding) (target : Nat) : Bool :=
  decide (target ≠ 0) && decide (target < 8 || 15 ≤ target) &&
    any 7 fun p => coreArc zCount bits (8 + p) target

def pUnionExpansion (zCount : Nat) (bits : Encoding) : Bool :=
  (7 : BitVec 8).ule (count (15 + zCount) (pUnionTarget zCount bits))

def structuralCore (zCount : Nat) (bits : Encoding) : Bool :=
  orientedA bits && orientedP bits && orientedPH bits &&
    everyXReached bits && rUnreached bits && allZReached zCount bits &&
    aMinimumAndDegree bits && all 8 (aNonSeymour zCount bits) &&
    pMinimumDegree zCount bits

def core (zCount : Nat) (bits : Encoding) : Bool :=
  structuralCore zCount bits && pUnionExpansion zCount bits

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.ExpansionCore
