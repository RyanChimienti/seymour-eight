import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.TerminalCoreDefs

/-!
# Root-neighborhood core for the tight epsilon-one x=4 row

The first 119 bits use the terminal `P ∪ H` layout.  The final 21 bits encode,
for each of the seven `P` vertices, its arc to the root followed by its two
arcs to `Z`.
-/

namespace SeymourEight.EpsilonOneRootCore

open TerminalCore

abbrev Encoding := BitVec 140

def pArc (bits : Encoding) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

def pToH (bits : Encoding) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 5 + h)

def hToP (bits : Encoding) (h i : Nat) : Bool :=
  bits.getLsbD (84 + h * 7 + i)

def rootArc (bits : Encoding) (i : Nat) : Bool :=
  bits.getLsbD (119 + i * 3)

def pToZ (bits : Encoding) (i z : Nat) : Bool :=
  bits.getLsbD (120 + i * 3 + z)

def orientedOnP (bits : Encoding) : Bool :=
  allSeven (fun i ↦ !pArc bits i i) &&
    allSeven (fun i ↦ allSeven (fun j ↦
      decide (i = j) || !(pArc bits i j && pArc bits j i)))

def orientedBetweenPAndH (bits : Encoding) : Bool :=
  allSeven (fun i ↦ allFive (fun h ↦
    !(pToH bits i h && hToP bits h i)))

def pOutCount (bits : Encoding) (i : Nat) : BitVec 8 :=
  sumSeven (pArc bits i)

def pToHCount (bits : Encoding) (i : Nat) : BitVec 8 :=
  sumFive (pToH bits i)

def totalPToH (bits : Encoding) : BitVec 8 :=
  sumCountSeven (pToHCount bits)

def totalPOut (bits : Encoding) : BitVec 8 :=
  sumCountSeven (pOutCount bits)

def totalHToP (bits : Encoding) : BitVec 8 :=
  sumCountFive (fun h ↦ sumSeven (hToP bits h))

def externalCount (bits : Encoding) (i : Nat) : BitVec 8 :=
  bitCount (rootArc bits i) + bitCount (pToZ bits i 0) +
    bitCount (pToZ bits i 1)

def totalExternal (bits : Encoding) : BitVec 8 :=
  sumCountSeven (externalCount bits)

def retainedDegree (bits : Encoding) (i : Nat) : BitVec 8 :=
  externalCount bits i + pToHCount bits i + pOutCount bits i

def totalRetainedDegree (bits : Encoding) : BitVec 8 :=
  sumCountSeven (retainedDegree bits)

def rootReached (bits : Encoding) : Bool :=
  anySeven (rootArc bits)

def reachedViaPOrH (bits : Encoding) (i j : Nat) : Bool :=
  anySeven (fun middle ↦
    decide (middle ≠ i) && decide (middle ≠ j) &&
      pArc bits i middle && pArc bits middle j) ||
  anyFive (fun h ↦ pToH bits i h && hToP bits h j)

def secondPCount (bits : Encoding) (i : Nat) : BitVec 8 :=
  sumSeven (fun j ↦
    decide (j ≠ i) && !pArc bits i j && reachedViaPOrH bits i j)

def missingPairCount (bits : Encoding) : BitVec 8 :=
  bitCount (!pArc bits 0 1 && !pArc bits 1 0) +
  bitCount (!pArc bits 0 2 && !pArc bits 2 0) +
  bitCount (!pArc bits 0 3 && !pArc bits 3 0) +
  bitCount (!pArc bits 0 4 && !pArc bits 4 0) +
  bitCount (!pArc bits 0 5 && !pArc bits 5 0) +
  bitCount (!pArc bits 0 6 && !pArc bits 6 0) +
  bitCount (!pArc bits 1 2 && !pArc bits 2 1) +
  bitCount (!pArc bits 1 3 && !pArc bits 3 1) +
  bitCount (!pArc bits 1 4 && !pArc bits 4 1) +
  bitCount (!pArc bits 1 5 && !pArc bits 5 1) +
  bitCount (!pArc bits 1 6 && !pArc bits 6 1) +
  bitCount (!pArc bits 2 3 && !pArc bits 3 2) +
  bitCount (!pArc bits 2 4 && !pArc bits 4 2) +
  bitCount (!pArc bits 2 5 && !pArc bits 5 2) +
  bitCount (!pArc bits 2 6 && !pArc bits 6 2) +
  bitCount (!pArc bits 3 4 && !pArc bits 4 3) +
  bitCount (!pArc bits 3 5 && !pArc bits 5 3) +
  bitCount (!pArc bits 3 6 && !pArc bits 6 3) +
  bitCount (!pArc bits 4 5 && !pArc bits 5 4) +
  bitCount (!pArc bits 4 6 && !pArc bits 6 4) +
  bitCount (!pArc bits 5 6 && !pArc bits 6 5)

/-- A root arc exposes all eight members of the root outneighborhood. -/
def rootEquationAt (bits : Encoding) (i : Nat) : Bool :=
  !rootArc bits i ||
    (secondPCount bits i + 9).ule
      (externalCount bits i + 2 * pToHCount bits i + pOutCount bits i)

/-- Lexicographic order on the interchangeable `P` labels. -/
def orderedP (bits : Encoding) : Bool :=
  let orderedPair := fun i j ↦
    (retainedDegree bits j).ule (retainedDegree bits i) &&
      (!(retainedDegree bits i == retainedDegree bits j) ||
        ((!rootArc bits j || rootArc bits i) &&
          (!(rootArc bits i == rootArc bits j) ||
            (pToHCount bits j).ule (pToHCount bits i))))
  orderedPair 0 1 && orderedPair 1 2 && orderedPair 2 3 &&
    orderedPair 3 4 && orderedPair 4 5 && orderedPair 5 6

/-- Exact defect slice of the root-neighborhood relaxation. -/
def core (missing alpha beta : Nat) (bits : Encoding) : Bool :=
  orientedOnP bits && orientedBetweenPAndH bits && rootReached bits &&
  (totalExternal bits + BitVec.ofNat 8 missing == 21) &&
  (totalPToH bits + BitVec.ofNat 8 alpha == 17) &&
  (totalPOut bits + BitVec.ofNat 8 beta == 21) &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  allSeven (fun i ↦
    (8 : BitVec 8).ule (retainedDegree bits i) && rootEquationAt bits i) &&
  orderedP bits &&
  (totalRetainedDegree bits + BitVec.ofNat 8 (missing + alpha + beta) == 59)

end SeymourEight.EpsilonOneRootCore
