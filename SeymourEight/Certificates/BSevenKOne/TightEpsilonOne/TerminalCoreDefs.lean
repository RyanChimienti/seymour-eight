import Std.Tactic.BVDecide

/-!
# Boolean definitions for terminal `P ∪ H` cores

This file defines the finite encodings used by the certificate module.  The
`one-missing-root` core retains seven vertices of `P`, five vertices of `H`,
the oriented incidences among them, exact degree totals, and the local
counting identity imposed at each vertex of `P`.
-/

namespace SeymourEight.TerminalCore

/-- Convert a Boolean incidence to its zero-or-one eight-bit count. -/
def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def allFive (p : Nat → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4

def anyFive (p : Nat → Bool) : Bool :=
  p 0 || p 1 || p 2 || p 3 || p 4

def sumFive (p : Nat → Bool) : BitVec 8 :=
  bitCount (p 0) + bitCount (p 1) + bitCount (p 2) + bitCount (p 3) +
    bitCount (p 4)

def sumCountFive (p : Nat → BitVec 8) : BitVec 8 :=
  p 0 + p 1 + p 2 + p 3 + p 4

def allSeven (p : Nat → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6

def anySeven (p : Nat → Bool) : Bool :=
  p 0 || p 1 || p 2 || p 3 || p 4 || p 5 || p 6

def sumSeven (p : Nat → Bool) : BitVec 8 :=
  bitCount (p 0) + bitCount (p 1) + bitCount (p 2) + bitCount (p 3) +
    bitCount (p 4) + bitCount (p 5) + bitCount (p 6)

def sumCountSeven (p : Nat → BitVec 8) : BitVec 8 :=
  p 0 + p 1 + p 2 + p 3 + p 4 + p 5 + p 6

/-- The first 49 bits encode arcs inside `P`. -/
def pArc (bits : BitVec 119) (i j : Nat) : Bool :=
  bits.getLsbD (i * 7 + j)

/-- The next 35 bits encode arcs from `P` to `H`. -/
def pToH (bits : BitVec 119) (i h : Nat) : Bool :=
  bits.getLsbD (49 + i * 5 + h)

/-- The final 35 bits encode arcs from `H` to `P`. -/
def hToP (bits : BitVec 119) (h i : Nat) : Bool :=
  bits.getLsbD (84 + h * 7 + i)

def orientedOnP (bits : BitVec 119) : Bool :=
  allSeven (fun i ↦ !pArc bits i i) &&
    allSeven (fun i ↦ allSeven (fun j ↦
      decide (i = j) || !(pArc bits i j && pArc bits j i)))

def orientedBetweenPAndH (bits : BitVec 119) : Bool :=
  allSeven (fun i ↦ allFive (fun h ↦
    !(pToH bits i h && hToP bits h i)))

def pOutCount (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  sumSeven (pArc bits i)

def pToHCount (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  sumFive (pToH bits i)

def totalPToH (bits : BitVec 119) : BitVec 8 :=
  sumCountSeven (pToHCount bits)

def totalHToP (bits : BitVec 119) : BitVec 8 :=
  sumCountFive (fun h ↦ sumSeven (hToP bits h))

/-- Total number of directed arcs inside the labelled `P` set. -/
def totalPOut (bits : BitVec 119) : BitVec 8 :=
  sumCountSeven (pOutCount bits)

/-- Whether `j` is reached from `i` in two steps through `P` or `H`. -/
def reachedViaPOrH (bits : BitVec 119) (i j : Nat) : Bool :=
  anySeven (fun middle ↦
    decide (middle ≠ i) && decide (middle ≠ j) &&
      pArc bits i middle && pArc bits middle j) ||
  anyFive (fun h ↦ pToH bits i h && hToP bits h j)

/-- Strict second-neighbor count in `P`, through an intermediate in `P ∪ H`. -/
def secondPCount (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  sumSeven (fun j ↦
    decide (j ≠ i) && !pArc bits i j && reachedViaPOrH bits i j)

/-- Number of missing oriented pairs inside `P`. -/
def missingPairCount (bits : BitVec 119) : BitVec 8 :=
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

/-- Two common `Z`-neighbors, plus the root arc except at exceptional `p₀`. -/
def retainedDegree (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  (if i = 0 then 2 else 3) + pToHCount bits i + pOutCount bits i

/-- The subtraction-free local counting test, with `e₀=0` and `eᵢ=1`
otherwise. -/
def equation18At (bits : BitVec 119) (i : Nat) : Bool :=
  (secondPCount bits i + 7).ule
    (pOutCount bits i + 2 * pToHCount bits i + (if i = 0 then 0 else 2))

/-- The finite terminal core for specified capacity defects and degree sum. -/
def oneMissingRootCore (bits : BitVec 119)
    (alpha beta degreeSum : BitVec 8) : Bool :=
  orientedOnP bits && orientedBetweenPAndH bits &&
  (missingPairCount bits == beta) &&
  (totalPToH bits + alpha == 17) &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  allSeven (fun i ↦
    (8 : BitVec 8).ule (retainedDegree bits i) &&
    (retainedDegree bits i).ule 9 && equation18At bits i) &&
  (sumCountSeven (retainedDegree bits) == degreeSum)

/-- Lexicographic ordering for the six interchangeable nonexceptional labels. -/
def interchangeableOrdered (bits : BitVec 119) : Bool :=
  let orderedPair := fun i j ↦
    (retainedDegree bits j).ule (retainedDegree bits i) &&
      (!(retainedDegree bits i == retainedDegree bits j) ||
        (pToHCount bits j).ule (pToHCount bits i))
  orderedPair 1 2 && orderedPair 2 3 && orderedPair 3 4 &&
    orderedPair 4 5 && orderedPair 5 6

/-- The general one-missing-root core with its tail symmetry broken. -/
def orderedOneMissingRootCore (bits : BitVec 119)
    (alpha beta degreeSum : BitVec 8) : Bool :=
  oneMissingRootCore bits alpha beta degreeSum && interchangeableOrdered bits

/--
Equivalent graph-friendly ordered core, recording the exact internal arc count
instead of the number of missing unordered pairs.
-/
def orderedOneMissingRootEdgeCore (bits : BitVec 119)
    (alpha internalEdges degreeSum : BitVec 8) : Bool :=
  orientedOnP bits && orientedBetweenPAndH bits &&
  (totalPOut bits == internalEdges) &&
  (totalPToH bits + alpha == 17) &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  allSeven (fun i ↦
    (8 : BitVec 8).ule (retainedDegree bits i) &&
    (retainedDegree bits i).ule 9 && equation18At bits i) &&
  interchangeableOrdered bits &&
  (sumCountSeven (retainedDegree bits) == degreeSum)

/-! ## Complete degree-sum-58 core -/

/-- The degree-sum-58 core, allowing degree ten. -/
def degreeTenCore (bits : BitVec 119) : Bool :=
  orientedOnP bits && orientedBetweenPAndH bits &&
  (totalPOut bits == 21) && (totalPToH bits == 17) &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  allSeven (fun i ↦
    (8 : BitVec 8).ule (retainedDegree bits i) &&
    (retainedDegree bits i).ule 10 && equation18At bits i) &&
  interchangeableOrdered bits &&
  (sumCountSeven (retainedDegree bits) == 58)

/--
Canonical tournament orientation using only the upper-triangular `P` bits.
For `i<j` the stored bit is `i→j`; its negation is `j→i`.
-/
def tournamentArc (bits : BitVec 119) (i j : Nat) : Bool :=
  if i = j then false
  else if i < j then pArc bits i j
  else !pArc bits j i

def tournamentPOutCount (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  sumSeven (tournamentArc bits i)

def tournamentReachedViaPOrH (bits : BitVec 119) (i j : Nat) : Bool :=
  anySeven (fun middle ↦
    decide (middle ≠ i) && decide (middle ≠ j) &&
      tournamentArc bits i middle && tournamentArc bits middle j) ||
  anyFive (fun h ↦ pToH bits i h && hToP bits h j)

def tournamentSecondPCount (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  sumSeven (fun j ↦
    decide (j ≠ i) && !tournamentArc bits i j &&
      tournamentReachedViaPOrH bits i j)

def tournamentRetainedDegree (bits : BitVec 119) (i : Nat) : BitVec 8 :=
  (if i = 0 then 2 else 3) + pToHCount bits i + tournamentPOutCount bits i

def tournamentEquation18At (bits : BitVec 119) (i : Nat) : Bool :=
  (tournamentSecondPCount bits i + 7).ule
    (tournamentPOutCount bits i + 2 * pToHCount bits i +
      (if i = 0 then 0 else 2))

/-- Lexicographic degree/`P→H` ordering of the interchangeable vertices `1,...,6`. -/
def tournamentInterchangeableOrdered (bits : BitVec 119) : Bool :=
  let orderedPair := fun i j ↦
    (tournamentRetainedDegree bits j).ule (tournamentRetainedDegree bits i) &&
      (!(tournamentRetainedDegree bits i == tournamentRetainedDegree bits j) ||
        (pToHCount bits j).ule (pToHCount bits i))
  orderedPair 1 2 && orderedPair 2 3 && orderedPair 3 4 &&
    orderedPair 4 5 && orderedPair 5 6

/-- The `beta=0` specialization, with tournament orientation built into the encoding. -/
def tournamentOneMissingRootCore (bits : BitVec 119)
    (alpha degreeSum : BitVec 8) : Bool :=
  orientedBetweenPAndH bits &&
  (totalPToH bits + alpha == 17) &&
  (18 : BitVec 8).ule (totalHToP bits) &&
  allSeven (fun i ↦
    (8 : BitVec 8).ule (tournamentRetainedDegree bits i) &&
    (tournamentRetainedDegree bits i).ule 9 && tournamentEquation18At bits i) &&
  tournamentInterchangeableOrdered bits &&
  (sumCountSeven (tournamentRetainedDegree bits) == degreeSum)

end SeymourEight.TerminalCore
