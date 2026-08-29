import SeymourEight.Certificates.BSevenKThree.RSeven.XFour.CoreDefs
import Batteries.Data.BitVec.Lemmas

/-!
# Canonical-label predicates for the hardest `(7,3)` finite core

The ordering is sequential and therefore graph-realizable: first sort `P` by
label-invariant scalar data, then sort `A₁`, `X`, and `Z` by their complete
incidence patterns to the now-labelled `P` set.
-/

namespace SeymourEight.BSevenKThree.RSeven.XFourNoRoot.SymmetricCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XFourNoRoot.Core

def bitCount32 (b : Bool) : BitVec 32 := if b then 1 else 0

def sumCode32 : Nat → (Nat → BitVec 32) → BitVec 32
  | 0, _ => 0
  | n + 1, f => sumCode32 n f + f n

def pIn (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun q => pArc bits q p

def hToPIn (bits : Encoding) (p : Nat) : BitVec 8 :=
  count 7 fun h => hToP bits h p

def pInvariantKey (bits : Encoding) (p : Nat) : BitVec 32 :=
  let degree := pOut bits p + pHOut bits p + pZOut 5 bits p
  (((((degree.zeroExtend 32 * 8 + (pZOut 5 bits p).zeroExtend 32) * 8 +
    (pHOut bits p).zeroExtend 32) * 8 + (pOut bits p).zeroExtend 32) * 8 +
    (pIn bits p).zeroExtend 32) * 8 + (hToPIn bits p).zeroExtend 32)

def orderedP (bits : Encoding) : Bool :=
  all 6 fun p => (pInvariantKey bits (p + 1)).ule (pInvariantKey bits p)

def hIncidenceCode (bits : Encoding) (h : Nat) : BitVec 14 :=
  BitVec.ofFnLE fun i : Fin 14 =>
    if _hi : i.val < 7 then hToP bits h i.val
    else pToH bits (i.val - 7) h

def hInvariantKey (bits : Encoding) (h : Nat) : BitVec 32 :=
  (((aPOut bits (h + 1)).zeroExtend 32 * 8 +
      (aOut bits (h + 1)).zeroExtend 32) * 16384) +
    (hIncidenceCode bits h).zeroExtend 32

def orderedStructuralClasses (bits : Encoding) : Bool :=
  all 2 (fun h => (hInvariantKey bits (h + 1)).ule (hInvariantKey bits h)) &&
    all 3 (fun h => (hInvariantKey bits (h + 4)).ule
      (hInvariantKey bits (h + 3)))

def zIncidenceCode (bits : Encoding) (z : Nat) : BitVec 7 :=
  BitVec.ofFnLE fun p : Fin 7 => pToZ bits p.val z

def orderedZ (bits : Encoding) : Bool :=
  all 4 fun z => (zIncidenceCode bits (z + 1)).ule (zIncidenceCode bits z)

def ordered (bits : Encoding) : Bool :=
  orderedP bits && orderedStructuralClasses bits && orderedZ bits

def symmetricCore (bits : Encoding) : Bool := commonCore bits && ordered bits

def exactLeaf (m delta d : Nat) (bits : Encoding) : Bool :=
  symmetricCore bits && externalMissing 5 bits == BitVec.ofNat 8 m &&
    aMissing bits == BitVec.ofNat 8 delta &&
    alpha bits + internalMissing bits == BitVec.ofNat 8 d

def intervalLeaf (mLo mHi dLo dHi : Nat) (bits : Encoding) : Bool :=
  symmetricCore bits &&
    (BitVec.ofNat 8 mLo).ule (externalMissing 5 bits) &&
    (externalMissing 5 bits).ule (BitVec.ofNat 8 mHi) &&
    aMissing bits == 0 &&
    (BitVec.ofNat 8 dLo).ule (alpha bits + internalMissing bits) &&
    (alpha bits + internalMissing bits).ule (BitVec.ofNat 8 dHi)

end SeymourEight.BSevenKThree.RSeven.XFourNoRoot.SymmetricCore
