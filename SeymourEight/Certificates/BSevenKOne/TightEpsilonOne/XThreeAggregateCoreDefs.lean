import SeymourEight.Certificates.BSevenKOne.TightEpsilonOne.XThreeReducedCoreDefs

/-!
# Aggregate reduced core for tight epsilon-one `(x,z)=(3,3)`

For `m = 28 - total(P,E)`, the degree sum forces the last `m` degree-sorted
vertices to have degree eight.  This expresses all eight possible values of
`m` in one core.
-/

namespace SeymourEight.EpsilonOneXThreeReducedCore

/-- The lexicographic order already available from the graph-side root
sorter: degree, root incidence, then `P-H` outdegree. -/
def aggregateOrderedP (b : Encoding) : Bool :=
  all 6 fun i =>
    (pDegree b (i + 1)).ule (pDegree b i) &&
      (!(pDegree b i == pDegree b (i + 1)) ||
        ((!pe b (i + 1) 0 || pe b i 0) &&
          (!(pe b i 0 == pe b (i + 1) 0) ||
            (pHOut b (i + 1)).ule (pHOut b i))))

/-- Combined form of the eight exact-tail predicates.  If `T` is the
number of `P -> E` arcs, row `i` lies in the forced degree-eight tail exactly
when `i >= T - 21`. -/
def aggregateTail (b : Encoding) : Bool :=
  all 7 fun i =>
    pDegree b i == 8 ||
      (BitVec.ofNat 8 (22 + i)).ule (sumCount 7 (pEOut b))

def aggregateCore (b : Encoding) : Bool :=
  oriented b && fixedStructure b && covered b &&
  all 7 (fun i => (8 : BitVec 8).ule (pDegree b i) &&
    rootEquation b i && protectedRedundancy b i) &&
  (21 : BitVec 8).ule (sumCount 7 (pEOut b)) &&
  (14 : BitVec 8).ule (sumCount 4 (fun h => count 7 (hp b h))) &&
  (sumCount 7 (pHOut b)).ule 14 && hNonSeymour b &&
  aggregateOrderedP b && aggregateTail b

end SeymourEight.EpsilonOneXThreeReducedCore
