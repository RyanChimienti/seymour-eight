import SeymourEight.Certificates.BSevenKThree.RSix.XFour.CoreDefs

/-!
# Tiny arithmetic certificates for the dual-defect compositions

The graph bridge supplies bounds on the three dual-defect summands.  These
certificates only enumerate the resulting three eight-bit integers, avoiding
all graph-arc variables.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.DualCases

def alphaOneCases (eta hq cross : BitVec 8) : Bool :=
  !((3 : BitVec 8).ule eta && eta.ule 49 && hq.ule 7 && cross.ule 42 &&
      eta + hq + cross == 4) ||
    (eta == 4 && hq == 0 && cross == 0) ||
    (eta == 3 && hq == 1 && cross == 0) ||
    (eta == 3 && hq == 0 && cross == 1)

def alphaTwoCases (eta hq cross : BitVec 8) : Bool :=
  !((3 : BitVec 8).ule eta && eta.ule 49 && hq.ule 7 && cross.ule 42 &&
      eta + hq + cross == 5) ||
    (eta == 5 && hq == 0 && cross == 0) ||
    (eta == 4 && hq == 1 && cross == 0) ||
    (eta == 4 && hq == 0 && cross == 1) ||
    (eta == 3 && hq == 2 && cross == 0) ||
    (eta == 3 && hq == 1 && cross == 1) ||
    (eta == 3 && hq == 0 && cross == 2)

def alphaThreeCases (eta hq cross : BitVec 8) : Bool :=
  !((3 : BitVec 8).ule eta && eta.ule 49 && hq.ule 7 && cross.ule 42 &&
      eta + hq + cross == 6) ||
    (eta == 6 && hq == 0 && cross == 0) ||
    (eta == 5 && hq == 1 && cross == 0) ||
    (eta == 4 && hq == 2 && cross == 0) ||
    (eta == 3 && hq == 3 && cross == 0) ||
    (eta == 5 && hq == 0 && cross == 1) ||
    (eta == 4 && hq == 1 && cross == 1) ||
    (eta == 3 && hq == 2 && cross == 1) ||
    (eta == 4 && hq == 0 && cross == 2) ||
    (eta == 3 && hq == 1 && cross == 2) ||
    (eta == 3 && hq == 0 && cross == 3)

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem alphaOneCases_true (eta hq cross : BitVec 8) :
    alphaOneCases eta hq cross = true := by
  simp only [alphaOneCases]
  bv_decide

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem alphaTwoCases_true (eta hq cross : BitVec 8) :
    alphaTwoCases eta hq cross = true := by
  simp only [alphaTwoCases]
  bv_decide

set_option compiler.extract_closed false in
set_option compiler.reuse false in
set_option compiler.small 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 512000000 in
theorem alphaThreeCases_true (eta hq cross : BitVec 8) :
    alphaThreeCases eta hq cross = true := by
  simp only [alphaThreeCases]
  bv_decide

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.DualCases
