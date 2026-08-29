import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XFour.Tactic

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletion

open Lean Parser Tactic
open Core

macro "r6x4_h_deletion_decide" : tactic =>
  `(tactic|
    simp only [highAlphaZeroLeaf, hDeletionLeaf, hQDeletionConditions,
      hDeleteQCount, hDeleteQSecond] <;>
    r6x4_no_root_decide)

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.HDeletion
