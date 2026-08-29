import SeymourEight.Shared.FiniteCore

/-!
# The eight-vertex internal-degree-three lemma

This module isolates the small finite fact used by the `(7,3)` Hall
reduction.  It is independent of every case-specific adjacency layout, so the
same checked theorem can be instantiated directly by graph bridges and by
larger finite cores.
-/

namespace SeymourEight.Shared.InnerDegreeThree

open FiniteCore

def outCount (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count 8 (arc source)

def reaches (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  any 8 fun middle =>
    decide (middle ≠ source) && decide (middle ≠ target) &&
      arc source middle && arc middle target

def second (arc : Nat → Nat → Bool) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc source target &&
    reaches arc source target

def secondCount (arc : Nat → Nat → Bool) (source : Nat) : BitVec 8 :=
  count 8 (second arc source)

def degreeThree (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  outCount arc source == 3

def innerSeymour (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  (outCount arc source).ule (secondCount arc source)

def degreeThreeInner (arc : Nat → Nat → Bool) (source : Nat) : Bool :=
  degreeThree arc source && innerSeymour arc source

def oriented (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun i => !arc i i && all 8 fun j =>
    decide (i = j) || !(arc i j && arc j i)

def minimumThree (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun source => (3 : BitVec 8).ule (outCount arc source)

def classification (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun source => all 8 fun target =>
    decide (source = target) || !degreeThree arc source ||
      degreeThreeInner arc source || !arc source target ||
        degreeThreeInner arc target

def threeWitnesses (arc : Nat → Nat → Bool) : Bool :=
  (3 : BitVec 8).ule (count 8 (degreeThreeInner arc))

/- A direct finite check on the 56 possible directed arcs between eight
vertices.  The theorem quantifies over an arbitrary Boolean adjacency
function; `bv_decide` treats its finitely many applications as shared Boolean
variables, so no case-specific bit encoding is involved. -/
set_option maxRecDepth 100000 in
theorem consequences (arc : Nat → Nat → Bool) :
    !(oriented arc && minimumThree arc) ||
      (classification arc && threeWitnesses arc) = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [oriented, minimumThree, classification, threeWitnesses,
    degreeThreeInner, innerSeymour, degreeThree, secondCount, second, reaches,
    outCount, FiniteCore.any, FiniteCore.all, FiniteCore.count,
    FiniteCore.bitCount]
  bv_decide (config := { timeout := 300, acNf := true })

theorem classification_of (arc : Nat → Nat → Bool)
    (hOriented : oriented arc = true) (hMinimum : minimumThree arc = true) :
    classification arc = true := by
  have h := consequences arc
  simp only [hOriented, hMinimum, Bool.and_self, Bool.not_true, Bool.and_eq_true,
    Bool.decide_and, Bool.decide_eq_true, Bool.false_or] at h
  exact h.1

theorem threeWitnesses_of (arc : Nat → Nat → Bool)
    (hOriented : oriented arc = true) (hMinimum : minimumThree arc = true) :
    threeWitnesses arc = true := by
  have h := consequences arc
  simp only [hOriented, hMinimum, Bool.and_self, Bool.not_true, Bool.and_eq_true,
    Bool.decide_and, Bool.decide_eq_true, Bool.false_or] at h
  exact h.2

end SeymourEight.Shared.InnerDegreeThree
