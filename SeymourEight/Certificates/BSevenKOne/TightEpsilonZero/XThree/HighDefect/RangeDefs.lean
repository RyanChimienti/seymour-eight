import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XThree.HighDefect.CoreDefs

namespace SeymourEight.FourZHighDefect

open FiveZExactRisk

/-- The seven vertices outside `N⁺(a₁)` that can be reached after deleting one
of its eight out-neighbors: the three represented `X` vertices, followed by
the four `Z` vertices. -/
def deletionExternalTarget (q : Nat) : Nat :=
  if q < 3 then q + 2 else q + 12

/-- Reachability from the seven retained out-neighbors of `a₁`. -/
def reachedFromRetainedNeighbor (bits : BitVec 218)
    (deleted target : Nat) : Bool :=
  any 8 fun d => decide (d ≠ deleted) &&
    coreArc bits (aOneNeighbor d) target

/-- Compact form of the exact deletion expansion count.  The first summand
counts the reachable `X`/`Z` vertices.  The second records whether the deleted
out-neighbor itself becomes a second neighbor through another retained
out-neighbor. -/
def compactDeletionExpansionCount (bits : BitVec 218)
    (deleted : Nat) : BitVec 8 :=
  count 7 (fun q =>
      reachedFromRetainedNeighbor bits deleted (deletionExternalTarget q)) +
    bitCount (reachedFromRetainedNeighbor bits deleted (aOneNeighbor deleted))

def compactAOneDeletionExpands (bits : BitVec 218) : Bool :=
  all 8 fun deleted =>
    (7 : BitVec 8).ule (compactDeletionExpansionCount bits deleted)

/-- The union of all graph-side `(missing, degreeSum)` rows.  The final two
constraints state the aggregate minimum-degree and orientation-capacity
bounds directly, without fixing either scalar to one of 21 exact pairs. -/
def highDefectRangeCore (bits : BitVec 218) : Bool :=
  fixedStructure bits && compactAOneDeletionExpands bits &&
    (totalMissingPZ bits).ule 7 &&
    (2 : BitVec 8).ule (totalMissingPZ bits) &&
    all 7 (fun q => aNonSeymour bits (q + 1)) &&
    all 7 (fun q => aNonSeymour bits (q + 8)) && orderedP bits &&
    orderedZ bits &&
    (56 : BitVec 8).ule (pDegreeSum bits) &&
    (pDegreeSum bits + totalMissingPZ bits).ule 63

end SeymourEight.FourZHighDefect
