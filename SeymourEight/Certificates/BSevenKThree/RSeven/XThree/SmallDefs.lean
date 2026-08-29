import SeymourEight.Certificates.BSevenKThree.RSeven.XThree.SymmetryDefs

/-!
# Inactive external-target columns

Smaller rows use only the active external columns; every remaining column of
the fixed six-column encoding is zero.
-/

namespace SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SmallCore

open Shared.FiniteCore
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.Core
open SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SymmetricCore

def inactiveZZero (zCount : Nat) (bits : Encoding) : Bool :=
  all (6 - zCount) fun j => all 7 fun p => !pToZ bits p (zCount + j)

end SeymourEight.BSevenKThree.RSeven.XThreeNoRoot.SmallCore
