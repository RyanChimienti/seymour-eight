import SeymourEight.Certificates.BSevenKOne.TightEpsilonZero.XTwo.ExactUnion.FiveZExactCoreDefs

/-!
# Aggregate five-`Z`, union-at-least-eight certificate

This certificate retains only the `P`, `H`, and `P → Z` incidences.  The
five-`Z` capacity lemma supplies an effective lower bound of eight, six, or
five external second-neighbours according as a `P` vertex misses zero, one,
or at least two vertices of `Z`.
-/

namespace SeymourEight.FiveZExactRisk

/-- Effective external second-neighbour contribution from the direct
`Z`-neighbours of a `P` vertex when the full external union has size at
least eight. -/
def fiveZExternalLower (bits : BitVec 280) (i : Nat) : BitVec 8 :=
  if pZOut bits i = 5 then 8
  else if pZOut bits i = 4 then 6
  else 5

/-- Necessary non-Seymour inequality after allowing every direct `H`-neighbour
to overlap the guaranteed external second-neighbour set. -/
def pNonSeymourUnionEight (bits : BitVec 280) (i : Nat) : Bool :=
  (secondPCount bits i + fiveZExternalLower bits i).ult
    (pDegree bits i + pHOut bits i)

def familyCoreUnionEight (bits : BitVec 280) : Bool :=
  orientedSquare 7 (pArc bits) && orientedPH bits &&
  (11 : BitVec 8).ule (totalHToP bits) &&
  (totalMissingPZ bits).ule 3 &&
  all 7 (fun i => (8 : BitVec 8).ule (pDegree bits i)) &&
  all 7 (pNonSeymourUnionEight bits)

def familyCoreUnionEightAtMissing (missing : Nat) (bits : BitVec 280) : Bool :=
  familyCoreUnionEight bits &&
    totalMissingPZ bits = BitVec.ofNat 8 missing &&
    (totalMissingPPairs bits).ule (BitVec.ofNat 8 (10 - missing))

/-- A row of the aggregate certificate at exact external, `P`--`H`, and
internal-`P` defects.  Exposing these parameters makes the defect-two and
defect-three families independently checkable. -/
def familyCoreUnionEightAtDefects (missing alpha beta : Nat)
    (bits : BitVec 280) : Bool :=
  familyCoreUnionEight bits &&
    totalMissingPZ bits = BitVec.ofNat 8 missing &&
    sumCount 7 (pHOut bits) + BitVec.ofNat 8 alpha = 10 &&
    sumCount 7 (pOut bits) = BitVec.ofNat 8 (21 - beta) &&
    sumCount 7 (pDegree bits) =
      BitVec.ofNat 8 (66 - missing - alpha - beta)

end SeymourEight.FiveZExactRisk
