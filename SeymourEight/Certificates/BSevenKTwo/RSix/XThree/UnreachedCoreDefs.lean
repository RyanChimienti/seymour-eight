import SeymourEight.Certificates.BSevenKTwo.RSix.XThree.CoreDefs

/-!
# Finite core for the `r = 6`, `x = 3`, `y = 0` rows

The four external columns are the four vertices of `Z`.  The unique `Q`
vertex is a nineteenth local target; its seven non-pivot `A` incidences use
the otherwise unused seventh `P` row exactly as in the reached encoding.
-/

namespace SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedCore

open Shared.FiniteCore

abbrev Encoding := Core.Encoding

/-- Local indices are `A[8]`, `P[6]`, `Z[4]`, and the unique `Q` at 18. -/
def coreArc (bits : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then Core.aArc bits u v
    else if v < 14 then Core.aToP bits u (v - 8)
    else if v < 18 then false
    else if v = 18 then Core.aToQ bits u
    else false
  else if u < 14 then
    if v < 8 then Core.pToA bits (u - 8) v
    else if v < 14 then Core.pArc bits (u - 8) (v - 8)
    else if v < 18 then Core.pToE bits (u - 8) (v - 14)
    else false
  else false

def directCount (bits : Encoding) (u : Nat) : BitVec 8 :=
  count 19 (coreArc bits u)

def reachesLocal (bits : Encoding) (source target : Nat) : Bool :=
  any 14 fun middle => decide (middle != source) && decide (middle != target) &&
    coreArc bits source middle && coreArc bits middle target

def strictSecondLocal (bits : Encoding) (source target : Nat) : Bool :=
  decide (target != source) && !coreArc bits source target &&
    reachesLocal bits source target

def localSecondCount (bits : Encoding) (source : Nat) : BitVec 8 :=
  count 19 (strictSecondLocal bits source)

def aNonSeymour (bits : Encoding) (a : Nat) : Bool :=
  (localSecondCount bits a).ult (directCount bits a)

def pNonSeymour (bits : Encoding) (p : Nat) : Bool :=
  (localSecondCount bits (8 + p)).ult (directCount bits (8 + p))

def uVertex (u : Nat) : Nat := if u < 2 then 1 + u else 6 + u
def secondTarget (t : Nat) : Nat := if t < 3 then 3 + t else 11 + t

def privateTarget (bits : Encoding) (deleted target : Nat) : Bool :=
  coreArc bits (uVertex deleted) (secondTarget target) &&
    all 8 fun other => decide (other = deleted) ||
      !coreArc bits (uVertex other) (secondTarget target)

def deletedReached (bits : Encoding) (deleted : Nat) : Bool :=
  any 8 fun other => decide (other != deleted) &&
    coreArc bits (uVertex other) (uVertex deleted)

def tightPrivate (bits : Encoding) : Bool :=
  all 8 fun deleted =>
    (count 7 (privateTarget bits deleted)).ule
      (bitCount (deletedReached bits deleted))

theorem pDirectCount_eq (bits : Encoding) (p : Nat) (hp : p < 6) :
    Core.directCount bits (8 + p) = directCount bits (8 + p) := by
  have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Core.directCount, directCount, count, bitCount, coreArc, Core.coreArc]

def allZReached (bits : Encoding) : Bool :=
  all 4 fun z => any 6 fun p => Core.pToE bits p z

/-- The unique `Q` vertex lies in `B=N⁺(A)\A`, but is not reached from A₁∪P. -/
def qStructure (bits : Encoding) : Bool :=
  !Core.aToQ bits 1 && !Core.aToQ bits 2 &&
    any 7 (fun a => Core.aToQ bits (1 + a))

/-- On pivot-neighbor sources, the reached-core deletion predicate differs
from the native unreached predicate only at target `14`: it reads the two
`A₁ → q` bits there.  `qStructure` makes both bits false, so the predicates
coincide. -/
theorem tightPrivate_eq_core_of_qStructure (bits : Encoding)
    (hq : qStructure bits = true) :
    tightPrivate bits = Core.tightPrivate bits := by
  have hq' := hq
  simp only [qStructure, Bool.and_eq_true] at hq'
  have hOne : Core.aToQ bits 1 = false := by
    cases h : Core.aToQ bits 1
    · rfl
    · rw [h] at hq'
      simp at hq'
  have hTwo : Core.aToQ bits 2 = false := by
    cases h : Core.aToQ bits 2
    · rfl
    · rw [h] at hq'
      simp at hq'
  simp (config := { maxSteps := 1000000 })
    [tightPrivate, privateTarget, deletedReached, uVertex, secondTarget,
      Core.tightPrivate, Core.privateTarget, Core.deletedReached,
      Core.uVertex, Core.secondTarget, coreArc, Core.coreArc,
      Shared.FiniteCore.all, Shared.FiniteCore.any, Shared.FiniteCore.count,
      hOne, hTwo]

def commonCore (bits : Encoding) : Bool :=
  Core.orientedA bits && Core.orientedP bits && Core.orientedPH bits &&
  Core.fixedA bits && Core.everyXReached bits &&
  allZReached bits && qStructure bits &&
  (3 : BitVec 8).ule (count 6 fun k =>
    let a := k / 3
    let x := k % 3
    Core.aArc bits (1 + a) (3 + x)) &&
  Core.aMinimumAndDegree bits && all 8 (aNonSeymour bits) &&
  Core.pMinimumDegree bits && all 6 (pNonSeymour bits) &&
  Core.tightPrivate bits && Core.orderedP bits &&
  Core.orderedStructuralClasses bits

def core (bits : Encoding) : Bool :=
  commonCore bits && all 6 (Core.pEffectiveCondition bits) &&
  Core.sharpKing bits && Core.exactClassKing bits &&
  (18 : BitVec 8).ule (Core.totalHToP bits) &&
  (Core.totalHToP bits + Core.externalMissing bits).ule 21

end SeymourEight.BSevenKTwo.RSix.XThreeNoRoot.UnreachedCore
