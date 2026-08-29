import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Projected high-defect three-`Z` core

This is the `x = 4` analogue of the projected four-`Z` core.  It retains
`A` (eight vertices), `P` (seven vertices), and `Z` (three vertices).  The
seven members of `A \ {a₁}` and all seven members of `P` carry
non-Seymour inequalities, while `a₁` contributes its seven-neighbor
one-arc-deletion expansions.

The block sizes still total 218 bits:

* `P × P`: 49;
* `P × H` and `H × P`, with `|H| = 5`: 35 each;
* `P × Z`, with `|Z| = 3`: 21;
* `R × P`, with `|R| = 2`: 14; and
* `A × A`: 64.
-/

namespace SeymourEight.ThreeZHighDefect

open FiveZExactRisk

def pArc (bits : BitVec 218) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : BitVec 218) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 5 + h)

def hToP (bits : BitVec 218) (h i : Nat) : Bool :=
  bits.getLsbD (84 + h * 7 + i)

def pToZ (bits : BitVec 218) (i z : Nat) : Bool :=
  bits.getLsbD (119 + i * 3 + z)

def rToP (bits : BitVec 218) (r i : Nat) : Bool :=
  bits.getLsbD (140 + r * 7 + i)

def aArc (bits : BitVec 218) (i j : Nat) : Bool :=
  bits.getLsbD (154 + i * 8 + j)

def aToP (bits : BitVec 218) (a i : Nat) : Bool :=
  if a = 0 then true
  else if a < 6 then hToP bits (a - 1) i
  else rToP bits (a - 6) i

def pToA (bits : BitVec 218) (i a : Nat) : Bool :=
  if 0 < a && a < 6 then pToH bits i (a - 1) else false

def coreArc (bits : BitVec 218) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 18 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def coreOutdegree (bits : BitVec 218) (u : Nat) : BitVec 8 :=
  count 18 (coreArc bits u)

def aOut (bits : BitVec 218) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def aPOut (bits : BitVec 218) (a : Nat) : BitVec 8 :=
  count 7 (aToP bits a)

def totalHToP (bits : BitVec 218) : BitVec 8 :=
  count 35 fun q => hToP bits (q % 5) (q / 5)

def totalPToH (bits : BitVec 218) : BitVec 8 :=
  count 35 fun q => pToH bits (q / 5) (q % 5)

def totalPOut (bits : BitVec 218) : BitVec 8 :=
  count 49 fun q => pArc bits (q / 7) (q % 7)

def totalMissingPZ (bits : BitVec 218) : BitVec 8 :=
  count 21 fun q => !pToZ bits (q / 3) (q % 3)

def pDegree (bits : BitVec 218) (i : Nat) : BitVec 8 :=
  count 3 (pToZ bits i) + count 5 (pToH bits i) + count 7 (pArc bits i)

def pDegreeSum (bits : BitVec 218) : BitVec 8 :=
  sumCount 7 (pDegree bits)

/-- Symmetry break for the interchangeable `P` vertices. -/
def orderedP (bits : BitVec 218) : Bool :=
  all 6 fun i =>
    (pDegree bits (i + 1)).ule (pDegree bits i) &&
      (!(pDegree bits i == pDegree bits (i + 1)) ||
        (count 5 (pToH bits (i + 1))).ule (count 5 (pToH bits i)))

def zCode (bits : BitVec 218) (z : Nat) : BitVec 16 :=
  count16 7 fun i => bitCount16 (pToZ bits i z) <<< i

def orderedZ (bits : BitVec 218) : Bool :=
  all 2 fun z => (zCode bits (z + 1)).ule (zCode bits z)

/-- The two capacity-saturated incidence blocks, recorded separately so that
compression proofs need not unfold the full 18-vertex orientation check. -/
def orientedP (bits : BitVec 218) : Bool :=
  orientedSquare 7 (pArc bits)

def orientedPH (bits : BitVec 218) : Bool :=
  all 7 fun i => all 5 fun h => !(pToH bits i h && hToP bits h i)

def pComplete (bits : BitVec 218) : Bool :=
  all 7 fun i => !pArc bits i i && all 7 fun j =>
    decide (i = j) || (pArc bits i j == !pArc bits j i)

def phComplete (bits : BitVec 218) : Bool :=
  all 7 fun i => all 5 fun h => pToH bits i h == !hToP bits h i

def upperPairI (q : Nat) : Nat :=
  if q < 6 then 0 else if q < 11 then 1 else if q < 15 then 2
  else if q < 18 then 3 else if q < 20 then 4 else 5

def upperPairJ (q : Nat) : Nat :=
  if q < 6 then q + 1 else if q < 11 then q - 4 else if q < 15 then q - 8
  else if q < 18 then q - 11 else if q < 20 then q - 13 else 6

def firstTrue : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => if p 0 then 0 else 1 + firstTrue n (fun i => p (i + 1))

def firstTrueBV (w : Nat) : Nat → (Nat → Bool) → BitVec w
  | 0, _ => 0
  | n + 1, p => if p 0 then 0 else 1 + firstTrueBV w n (fun i => p (i + 1))

def pMissingIndex (bits : BitVec 218) : BitVec 5 :=
  firstTrueBV 5 21 fun q =>
    !pArc bits (upperPairI q) (upperPairJ q) &&
      !pArc bits (upperPairJ q) (upperPairI q)

def phMissingIndex (bits : BitVec 218) : BitVec 6 :=
  firstTrueBV 6 35 fun q =>
    !pToH bits (q / 5) (q % 5) && !hToP bits (q % 5) (q / 5)

def pOneComplete (bits : BitVec 218) : Bool :=
  (pMissingIndex bits).ult 21 && all 7 (fun i => !pArc bits i i) &&
  all 21 fun q =>
    if pMissingIndex bits == BitVec.ofNat 5 q then
      !pArc bits (upperPairI q) (upperPairJ q) &&
        !pArc bits (upperPairJ q) (upperPairI q)
    else
      pArc bits (upperPairI q) (upperPairJ q) ==
        !pArc bits (upperPairJ q) (upperPairI q)

def phOneComplete (bits : BitVec 218) : Bool :=
  (phMissingIndex bits).ult 35 && all 35 fun q =>
    if phMissingIndex bits == BitVec.ofNat 6 q then
      !pToH bits (q / 5) (q % 5) && !hToP bits (q % 5) (q / 5)
    else
      pToH bits (q / 5) (q % 5) == !hToP bits (q % 5) (q / 5)

def pCompatibleAtDefect (beta : Nat) (bits : BitVec 218) : Bool :=
  if beta = 0 then pComplete bits else if beta = 1 then pOneComplete bits else true

def phCompatibleAtDefect (alpha : Nat) (bits : BitVec 218) : Bool :=
  if alpha = 0 then phComplete bits
  else if alpha = 1 then phOneComplete bits || phComplete bits
  else true

def reachedFromA (bits : BitVec 218) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc bits source middle && coreArc bits middle target

def secondFromA (bits : BitVec 218) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachedFromA bits source target

def aSecondCount (bits : BitVec 218) (source : Nat) : BitVec 8 :=
  count 18 (secondFromA bits source)

def aNonSeymour (bits : BitVec 218) (source : Nat) : Bool :=
  (aSecondCount bits source).ult (coreOutdegree bits source)

def aOneNeighbor (d : Nat) : Nat :=
  if d = 0 then 1 else d + 7

def retainedAfterDelete (deleted vertex : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) && decide (vertex = aOneNeighbor d)

def deletionReached (bits : BitVec 218) (deleted target : Nat) : Bool :=
  decide (target ≠ 0) && !retainedAfterDelete deleted target &&
    any 18 fun middle =>
      retainedAfterDelete deleted middle && coreArc bits middle target

def deletionExpansionCount (bits : BitVec 218) (deleted : Nat) : BitVec 8 :=
  count 18 (deletionReached bits deleted)

def aOneDeletionExpands (bits : BitVec 218) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule (deletionExpansionCount bits deleted)

def fixedStructure (bits : BitVec 218) : Bool :=
  orientedSquare 18 (coreArc bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 2 (fun q => !aArc bits 1 (q + 6)) &&
  (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) &&
  (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) &&
  (aArc bits 1 4 || any 7 (fun i => pToH bits i 3)) &&
  (aArc bits 1 5 || any 7 (fun i => pToH bits i 4)) &&
  all 8 (fun a => (1 : BitVec 8).ule (aOut bits a)) &&
  all 7 (fun q =>
    !(aOut bits (q + 1) = 1) || (7 : BitVec 8).ule (aPOut bits (q + 1))) &&
  all 15 (fun u => (8 : BitVec 8).ule (coreOutdegree bits u)) &&
  all 3 (fun z => any 7 (fun i => pToZ bits i z))

def highDefectCore (bits : BitVec 218) : Bool :=
  fixedStructure bits && aOneDeletionExpands bits &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  (2 : BitVec 8).ule (totalMissingPZ bits) &&
  all 7 (fun q => aNonSeymour bits (q + 1)) &&
  all 7 (fun q => aNonSeymour bits (q + 8)) && orderedP bits && orderedZ bits

structure HighCoreFacts (bits : BitVec 218) : Prop where
  fixed : fixedStructure bits = true
  deletion : aOneDeletionExpands bits = true
  hToPBound : (18 : BitVec 8).ule (totalHToP bits) = true
  missingBound : (2 : BitVec 8).ule (totalMissingPZ bits) = true
  nonSeymourA : all 7 (fun q => aNonSeymour bits (q + 1)) = true
  nonSeymourP : all 7 (fun q => aNonSeymour bits (q + 8)) = true
  orderedP_true : orderedP bits = true
  orderedZ_true : orderedZ bits = true

theorem highCoreFacts_of_true {bits : BitVec 218}
    (h : highDefectCore bits = true) : HighCoreFacts bits := by
  simp only [highDefectCore] at h
  have ⟨h8, hz⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h7, hp⟩ := Bool.and_eq_true_iff.mp h8
  have ⟨h6, hnP⟩ := Bool.and_eq_true_iff.mp h7
  have ⟨h5, hnA⟩ := Bool.and_eq_true_iff.mp h6
  have ⟨h4, hm⟩ := Bool.and_eq_true_iff.mp h5
  have ⟨h3, hhp⟩ := Bool.and_eq_true_iff.mp h4
  have ⟨hf, hd⟩ := Bool.and_eq_true_iff.mp h3
  exact ⟨hf, hd, hhp, hm, hnA, hnP, hp, hz⟩

def highDefectCoreAtMissing (missing : Nat) (bits : BitVec 218) : Bool :=
  highDefectCore bits && totalMissingPZ bits = BitVec.ofNat 8 missing

def highDefectCoreAtMissingDegree (missing degreeSum : Nat)
    (bits : BitVec 218) : Bool :=
  highDefectCoreAtMissing missing bits &&
    pDegreeSum bits = BitVec.ofNat 8 degreeSum

/-- Exact capacity-defect slice.  In the graph application the degree
identity makes `alpha + beta = 3 - missing`; recording both values explicitly
substantially reduces certificate-search memory. -/
def highDefectCoreAtDefects (missing alpha beta : Nat)
    (bits : BitVec 218) : Bool :=
  highDefectCoreAtMissing missing bits &&
    totalPToH bits + BitVec.ofNat 8 alpha = 17 &&
    totalPOut bits + BitVec.ofNat 8 beta = 21 &&
    pCompatibleAtDefect beta bits && phCompatibleAtDefect alpha bits

end SeymourEight.ThreeZHighDefect
