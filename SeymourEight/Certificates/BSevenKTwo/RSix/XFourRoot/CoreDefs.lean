import SeymourEight.Certificates.BSevenKTwo.RSix.XFourNoRoot.CoreDefs

namespace SeymourEight.BSevenKTwo.RSix.XFourRoot.Core

open RSix.XFourNoRoot.Core
open Shared.FiniteCore

def rootPConditions (bits : Encoding) : Bool := all 6 fun p =>
  (8 : BitVec 8).ule (pOut bits p + pHOut bits p + pEOut bits p) &&
  (pSecondCount bits p + 8 + 1).ule
    (pOut bits p + 2 * pHOut bits p + pEOut bits p)

def rootCoreAt (c : Nat) (bits : Encoding) : Bool :=
  orderedP bits && orderedH bits && orderedZ bits && orientedBasic bits &&
    (21 : BitVec 8).ule (totalHP bits + c) && rootPConditions bits

def rootCoreCase (c m alpha beta : Nat) (bits : Encoding) : Bool :=
  rootCoreAt c bits && totalPE bits == 18 - m &&
    totalPH bits == 15 + c - alpha && totalPP bits == 15 - beta

end SeymourEight.BSevenKTwo.RSix.XFourRoot.Core
