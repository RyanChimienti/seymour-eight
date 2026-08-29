import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.ExpansionDefs

/-!
# Reused finite core for the `r = 7`, `x = 2`, five-target rows

The 228-bit `x = 3` layout already has enough room: its third `X` position is
reinterpreted as the first of two `R` positions, while the unused sixth
`P ↔ H` column is forced to zero.  Only the two `X` non-Seymour inequalities
are needed; the Hall and degree-three clauses from the `x = 3` family drop out.
-/

namespace SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Core

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot
open XThreeNoRoot.Core XThreeNoRoot.ExpansionCore

abbrev Encoding := XThreeNoRoot.Core.Encoding

def everyXReached (bits : Encoding) : Bool :=
  all 2 fun x =>
    any 3 (fun a => XThreeNoRoot.Core.aArc bits (1 + a) (4 + x)) ||
      any 7 (fun p => XThreeNoRoot.Core.pToH bits p (3 + x))

def rUnreached (bits : Encoding) : Bool :=
  all 3 (fun a => all 2 fun r => !XThreeNoRoot.Core.aArc bits (1 + a) (6 + r)) &&
    all 7 (fun p => all 2 fun r => !XThreeNoRoot.Core.pToH bits p (5 + r))

def pHOut (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 5 (XThreeNoRoot.Core.pToH bits p)

def pMinimumDegree (zCount : Nat) (bits : Encoding) : Bool :=
  all 7 fun p =>
    (8 : BitVec 8).ule
      (XThreeNoRoot.Core.pOut bits p + pHOut bits p +
        XThreeNoRoot.Core.pZOut zCount bits p)

def structuralCore (zCount : Nat) (bits : Encoding) : Bool :=
  XThreeNoRoot.Core.orientedA bits && XThreeNoRoot.Core.orientedP bits &&
    XThreeNoRoot.Core.orientedPH bits && everyXReached bits && rUnreached bits &&
    XThreeNoRoot.Core.allZReached zCount bits &&
    XThreeNoRoot.Core.aMinimumAndDegree bits &&
    all 2 (fun x => XThreeNoRoot.Core.aNonSeymour zCount bits (4 + x)) &&
    pMinimumDegree zCount bits

def core (zCount : Nat) (bits : Encoding) : Bool :=
  structuralCore zCount bits && pUnionExpansion zCount bits

end SeymourEight.BSevenKThree.RSeven.XTwoNoRoot.Core
