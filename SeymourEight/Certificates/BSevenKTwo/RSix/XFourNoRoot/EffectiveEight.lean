import SeymourEight.Shared.FiniteCore

namespace SeymourEight.BSevenKTwo.RSix.XFourNoRoot.EffectiveEightCore

open Shared.FiniteCore

abbrev Encoding := BitVec 66

def pToE (bits : Encoding) (p e : Nat) : Bool :=
  bits.getLsbD (3 * p + e)

def eToP (bits : Encoding) (e p : Nat) : Bool :=
  bits.getLsbD (18 + 6 * e + p)

def eArc (bits : Encoding) (e f : Nat) : Bool :=
  decide (e ≠ f) && bits.getLsbD (36 + 3 * e + f)

def eToW (bits : Encoding) (e w : Nat) : Bool :=
  bits.getLsbD (45 + 7 * e + w)

def localArc (bits : Encoding) (e target : Nat) : Bool :=
  if target < 3 then eArc bits e target else eToP bits e (target - 3)

def targetToE (bits : Encoding) (target e : Nat) : Bool :=
  if target < 3 then eArc bits target e else pToE bits (target - 3) e

def conditions (bits : Encoding) : Bool :=
  (all 3 fun e => all 3 fun f =>
    decide (e = f) || !(eArc bits e f && eArc bits f e)) &&
  (all 3 fun e => all 6 fun p => !(eToP bits e p && pToE bits p e)) &&
  (count 18 fun n => pToE bits (n / 3) (n % 3)) == 18 &&
  (all 3 fun e => (8 : BitVec 8).ule
    (count 9 (localArc bits e) + count 7 (eToW bits e)))

def deletionWitness (bits : Encoding) : Bool :=
  any 3 fun u => any 3 fun v => any 3 fun t =>
    (count 9 (localArc bits u) == 1) &&
    (all 7 fun w => eToW bits u w) &&
    localArc bits u v &&
      (all 7 fun w => eToW bits v w) && targetToE bits v t &&
      decide (u ≠ t) && !localArc bits u t &&
      (all 7 fun w => eToW bits t w)

set_option maxRecDepth 10000

set_option maxHeartbeats 2000000 in
theorem conditions_imply_witness (bits : Encoding) :
    conditions bits = true → deletionWitness bits = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [conditions, deletionWitness, localArc, targetToE, pToE, eToP, eArc,
      eToW, Shared.FiniteCore.count, Shared.FiniteCore.all,
      Shared.FiniteCore.any, Shared.FiniteCore.bitCount]
  bv_decide (config := { timeout := 1200, acNf := true })

end SeymourEight.BSevenKTwo.RSix.XFourNoRoot.EffectiveEightCore
