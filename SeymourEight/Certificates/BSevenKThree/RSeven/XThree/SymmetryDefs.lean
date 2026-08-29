import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.CoreDefs
import Batteries.Data.BitVec.Lemmas

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core

def pIn (bits : Encoding) (p : Nat) : BitVec 8 := count 7 fun q => pArc bits q p
def hToPIn (bits : Encoding) (p : Nat) : BitVec 8 := count 6 fun h => hToP bits h p

def pInvariantKey (zCount : Nat) (bits : Encoding) (p : Nat) : BitVec 32 :=
  let degree := pOut bits p + pHOut bits p + pZOut zCount bits p
  (((((degree.zeroExtend 32 * 8 + (pZOut zCount bits p).zeroExtend 32) * 8 +
    (pHOut bits p).zeroExtend 32) * 8 + (pOut bits p).zeroExtend 32) * 8 +
    (pIn bits p).zeroExtend 32) * 8 + (hToPIn bits p).zeroExtend 32)

def orderedP (zCount : Nat) (bits : Encoding) : Bool :=
  all 6 fun p => (pInvariantKey zCount bits (p + 1)).ule
    (pInvariantKey zCount bits p)

def hIncidenceCode (bits : Encoding) (h : Nat) : BitVec 14 :=
  BitVec.ofFnLE fun i : Fin 14 =>
    if _hi : i.val < 7 then hToP bits h i.val else pToH bits (i.val - 7) h

def hInvariantKey (bits : Encoding) (h : Nat) : BitVec 32 :=
  (((aPOut bits (h + 1)).zeroExtend 32 * 8 +
      (aOut bits (h + 1)).zeroExtend 32) * 16384) +
    (hIncidenceCode bits h).zeroExtend 32

def orderedStructuralClasses (bits : Encoding) : Bool :=
  all 2 (fun h => (hInvariantKey bits (h + 1)).ule (hInvariantKey bits h)) &&
    all 2 (fun h => (hInvariantKey bits (h + 4)).ule
      (hInvariantKey bits (h + 3)))

def zIncidenceCode (bits : Encoding) (z : Nat) : BitVec 7 :=
  BitVec.ofFnLE fun p : Fin 7 => pToZ bits p.val z

def orderedZ (zCount : Nat) (bits : Encoding) : Bool :=
  all (zCount - 1) fun z =>
    (zIncidenceCode bits (z + 1)).ule (zIncidenceCode bits z)

def ordered (zCount : Nat) (bits : Encoding) : Bool :=
  orderedP zCount bits && orderedStructuralClasses bits && orderedZ zCount bits

def symmetricCore (zCount : Nat) (bits : Encoding) : Bool :=
  commonCore zCount bits && ordered zCount bits

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore
