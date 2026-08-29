import SeymourEight.CaseReduction
import SeymourEight.Cases.BSixKThree
import SeymourEight.Cases.BSixKTwo
import SeymourEight.Cases.BSevenKOne
import SeymourEight.Cases.BSevenKThree
import SeymourEight.Cases.BSevenKTwo

set_option linter.style.header false

namespace SeymourEight

/--
If Seymour's Second Neighborhood Conjecture holds for graphs having a vertex with
outdegree at most seven, then it holds for graphs having a vertex with outdegree at
most eight.
-/
theorem seymourEight.{u}
    (hSeven : Digraph.LimitedSeymourConjecture.{u} 7) :
    Digraph.LimitedSeymourConjecture.{u} 8 :=
  degreeEightConjecture_of_subcases hSeven BSixKTwo.bSixKTwoCase
    BSixKThree.bSixKThreeCase BSevenKOne.bSevenKOneCase
      BSevenKTwo.bSevenKTwoCase BSevenKThree.bSevenKThreeCase

end SeymourEight
