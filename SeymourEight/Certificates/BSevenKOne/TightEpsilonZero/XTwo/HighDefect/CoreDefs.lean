import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Projected high-defect five-`Z` core

This core retains exactly the incidences used by the high-defect argument:
the eight vertices of `A`, seven vertices of `P`, and five vertices of `Z`.
The seven non-`a₁` members of `A` carry the non-Seymour inequalities; `a₁`
contributes its degree-seven one-arc-deletion expansions.  No non-Seymour
constraint on `P`, outgoing arc from `Z`, or anonymous outside vertex is
retained.

Vertex indices in the unified core are `A = 0,...,7`, `P = 8,...,14`, and
`Z = 15,...,19`.  Within `A`, index zero is `a₁`, index one is `A₁`, indices
two and three are `X`, and indices four through seven are `R`.
-/

namespace SeymourEight.FiveZHighDefect

open FiveZExactRisk

/-! ## Primary-variable layout (218 bits) -/

def pArc (bits : BitVec 218) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : BitVec 218) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 3 + h)

def hToP (bits : BitVec 218) (h i : Nat) : Bool :=
  bits.getLsbD (70 + h * 7 + i)

def pToZ (bits : BitVec 218) (i z : Nat) : Bool :=
  bits.getLsbD (91 + i * 5 + z)

def rToP (bits : BitVec 218) (r i : Nat) : Bool :=
  bits.getLsbD (126 + r * 7 + i)

def aArc (bits : BitVec 218) (i j : Nat) : Bool :=
  bits.getLsbD (154 + i * 8 + j)

/-! ## Unified incidences and counts -/

def aToP (bits : BitVec 218) (a i : Nat) : Bool :=
  if a = 0 then true
  else if a < 4 then hToP bits (a - 1) i
  else rToP bits (a - 4) i

def pToA (bits : BitVec 218) (i a : Nat) : Bool :=
  if 0 < a && a < 4 then pToH bits i (a - 1) else false

def coreArc (bits : BitVec 218) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aArc bits u v
    else if v < 15 then aToP bits u (v - 8)
    else false
  else if u < 15 then
    if v < 8 then pToA bits (u - 8) v
    else if v < 15 then pArc bits (u - 8) (v - 8)
    else if v < 20 then pToZ bits (u - 8) (v - 15)
    else false
  else false

def coreOutdegree (bits : BitVec 218) (u : Nat) : BitVec 8 :=
  count 20 (coreArc bits u)

def aOut (bits : BitVec 218) (a : Nat) : BitVec 8 :=
  count 8 (aArc bits a)

def aPOut (bits : BitVec 218) (a : Nat) : BitVec 8 :=
  count 7 (aToP bits a)

def totalHToP (bits : BitVec 218) : BitVec 8 :=
  count 21 fun q => aToP bits (q / 7 + 1) (q % 7)

def totalMissingPZ (bits : BitVec 218) : BitVec 8 :=
  count 35 fun q => !pToZ bits (q / 5) (q % 5)

/-! ## The seven non-Seymour inequalities in `A \ {a₁}` -/

def reachedFromA (bits : BitVec 218) (source target : Nat) : Bool :=
  any 15 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      coreArc bits source middle && coreArc bits middle target

def secondFromA (bits : BitVec 218) (source target : Nat) : Bool :=
  decide (target ≠ source) && !coreArc bits source target &&
    reachedFromA bits source target

def aSecondCount (bits : BitVec 218) (source : Nat) : BitVec 8 :=
  count 20 (secondFromA bits source)

def aNonSeymour (bits : BitVec 218) (source : Nat) : Bool :=
  (aSecondCount bits source).ult (coreOutdegree bits source)

/-! ## Degree-seven deletion expansions at `a₁` -/

/-- The eight exact out-neighbors of `a₁`: first `A₁`, then the seven `P`s. -/
def aOneNeighbor (d : Nat) : Nat :=
  if d = 0 then 1 else d + 7

def retainedAfterDelete (deleted vertex : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) && decide (vertex = aOneNeighbor d)

def deletionReached (bits : BitVec 218) (deleted target : Nat) : Bool :=
  decide (target ≠ 0) && !retainedAfterDelete deleted target &&
    any 20 fun middle =>
      retainedAfterDelete deleted middle && coreArc bits middle target

def deletionExpansionCount (bits : BitVec 218) (deleted : Nat) : BitVec 8 :=
  count 20 (deletionReached bits deleted)

def aOneDeletionExpands (bits : BitVec 218) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule (deletionExpansionCount bits deleted)

/-! ## Complete projected core -/

def fixedStructure (bits : BitVec 218) : Bool :=
  orientedSquare 20 (coreArc bits) &&
  aArc bits 0 1 && all 6 (fun q => !aArc bits 0 (q + 2)) &&
  all 4 (fun q => !aArc bits 1 (q + 4)) &&
  (aArc bits 1 2 || any 7 (fun i => pToH bits i 1)) &&
  (aArc bits 1 3 || any 7 (fun i => pToH bits i 2)) &&
  all 8 (fun a => (1 : BitVec 8).ule (aOut bits a)) &&
  all 7 (fun q =>
    !(aOut bits (q + 1) = 1) || (7 : BitVec 8).ule (aPOut bits (q + 1))) &&
  all 15 (fun u => (8 : BitVec 8).ule (coreOutdegree bits u)) &&
  (11 : BitVec 8).ule (totalHToP bits) &&
  all 5 (fun z => any 7 (fun i => pToZ bits i z))

def highDefectCore (bits : BitVec 218) : Bool :=
  fixedStructure bits && aOneDeletionExpands bits &&
  (4 : BitVec 8).ule (totalMissingPZ bits) &&
  all 7 (fun q => aNonSeymour bits (q + 1))

def highDefectCoreAtMissing (missing : Nat) (bits : BitVec 218) : Bool :=
  highDefectCore bits && totalMissingPZ bits = BitVec.ofNat 8 missing

end SeymourEight.FiveZHighDefect
