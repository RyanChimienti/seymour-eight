import Std.Tactic.BVDecide

/-!
# Reduced named-vertex core for tight epsilon-one `(x,z)=(3,3)`

The first 218 bits use the existing `A ∪ P ∪ external` layout.  The final
12 bits record arcs from the three `Z` vertices to the four protected targets
`{a1} ∪ R`.
-/

namespace SeymourEight.EpsilonOneXThreeReducedCore

abbrev Encoding := BitVec 230

def bitCount (b : Bool) : BitVec 8 := if b then 1 else 0

def count : Nat → (Nat → Bool) → BitVec 8
  | 0, _ => 0
  | n + 1, p => count n p + bitCount (p n)

def sumCount : Nat → (Nat → BitVec 8) → BitVec 8
  | 0, _ => 0
  | n + 1, p => sumCount n p + p n

def all : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => all n p && p n

def any : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => any n p || p n

def pp (b : Encoding) (i j : Nat) := b.getLsbD (i * 7 + j)
def ph (b : Encoding) (i h : Nat) := b.getLsbD (49 + i * 4 + h)
def hp (b : Encoding) (h i : Nat) := b.getLsbD (77 + h * 7 + i)
def pe (b : Encoding) (i e : Nat) := b.getLsbD (105 + i * 4 + e)
def rp (b : Encoding) (r i : Nat) := b.getLsbD (133 + r * 7 + i)
def aa (b : Encoding) (a q : Nat) := b.getLsbD (154 + a * 8 + q)
def zp (b : Encoding) (z k : Nat) := b.getLsbD (218 + z * 4 + k)

def aToP (b : Encoding) (a i : Nat) : Bool :=
  if a = 0 then true else if a < 5 then hp b (a - 1) i else rp b (a - 5) i

def pToA (b : Encoding) (i a : Nat) : Bool :=
  if 0 < a && a < 5 then ph b i (a - 1) else false

/- Retained targets are `0..7=A`, `8..14=P`, `15..18=external`, with
external index `15=root` and `16..18=Z`. -/
def arc (b : Encoding) (u v : Nat) : Bool :=
  if u < 8 then
    if v < 8 then aa b u v else if v < 15 then aToP b u (v - 8) else false
  else if u < 15 then
    if v < 8 then pToA b (u - 8) v
    else if v < 15 then pp b (u - 8) (v - 8)
    else if v < 19 then pe b (u - 8) (v - 15)
    else false
  else false

def aOut (b : Encoding) (a : Nat) := count 8 (aa b a)
def aPOut (b : Encoding) (a : Nat) := count 7 (aToP b a)
def aDegree (b : Encoding) (a : Nat) := aOut b a + aPOut b a

def reached (b : Encoding) (source target : Nat) : Bool :=
  any 15 (fun middle => decide (middle ≠ source) && decide (middle ≠ target) &&
    arc b source middle && arc b middle target)

def secondFromA (b : Encoding) (source target : Nat) : Bool :=
  decide (target ≠ source) && !arc b source target && reached b source target

def aSecond (b : Encoding) (source : Nat) := count 19 (secondFromA b source)

def pPOut (b : Encoding) (i : Nat) := count 7 (pp b i)
def pHOut (b : Encoding) (i : Nat) := count 4 (ph b i)
def pEOut (b : Encoding) (i : Nat) := count 4 (pe b i)
def pDegree (b : Encoding) (i : Nat) := pPOut b i + pHOut b i + pEOut b i

def reachedP (b : Encoding) (i j : Nat) : Bool :=
  any 7 (fun q => decide (q ≠ i) && decide (q ≠ j) && pp b i q && pp b q j) ||
  any 4 (fun h => ph b i h && hp b h j)

def secondP (b : Encoding) (i : Nat) :=
  count 7 (fun j => decide (j ≠ i) && !pp b i j && reachedP b i j)

/-- A root arc exposes all eight vertices of `A`. -/
def rootEquation (b : Encoding) (i : Nat) : Bool :=
  !pe b i 0 || (secondP b i + 9).ule (pEOut b i + 2 * pHOut b i + pPOut b i)

def protectedA (k : Nat) : Nat := if k = 0 then 0 else k + 4

def alternateProtected (b : Encoding) (i k : Nat) : Bool :=
  any 3 (fun x => ph b i (x + 1) && aa b (x + 2) (protectedA k)) ||
  any 3 (fun z => pe b i (z + 1) && zp b z k)

def protectedRedundancy (b : Encoding) (i : Nat) : Bool :=
  !(pDegree b i == 8 && pe b i 0) ||
    (3 : BitVec 8).ule (count 4 (alternateProtected b i))

def oriented (b : Encoding) : Bool :=
  all 7 (fun i => !pp b i i) &&
  all 7 (fun i => all 7 (fun j => decide (i = j) || !(pp b i j && pp b j i))) &&
  all 7 (fun i => all 4 (fun h => !(ph b i h && hp b h i))) &&
  all 8 (fun a => !aa b a a) &&
  all 8 (fun a => all 8 (fun q => decide (a = q) || !(aa b a q && aa b q a)))

def fixedStructure (b : Encoding) : Bool :=
  aa b 0 1 && all 6 (fun q => !aa b 0 (q + 2)) &&
  all 3 (fun r => !aa b 1 (r + 5)) &&
  all 4 (fun h =>
    (1 : BitVec 8).ule (aOut b (h + 1)) &&
    (8 : BitVec 8).ule (aDegree b (h + 1)) &&
    (!(aOut b (h + 1) == 1) || aPOut b (h + 1) == 7)) &&
  all 3 (fun x => aa b 1 (x + 2) || any 7 (fun i => ph b i (x + 1)))

def covered (b : Encoding) : Bool :=
  all 4 (fun e => any 7 (fun i => pe b i e))

def hNonSeymour (b : Encoding) : Bool :=
  all 4 (fun h => (aSecond b (h + 1) + 1).ule (aDegree b (h + 1)))

def orderedP (b : Encoding) : Bool :=
  all 6 (fun i => (pDegree b (i + 1)).ule (pDegree b i))

def exactTail (m : Nat) (b : Encoding) : Bool :=
  all m (fun q => pDegree b (7 - m + q) == 8)

def core (m : Nat) (b : Encoding) : Bool :=
  oriented b && fixedStructure b && covered b &&
  all 7 (fun i => (8 : BitVec 8).ule (pDegree b i) &&
    rootEquation b i && protectedRedundancy b i) &&
  (sumCount 7 (pEOut b) + BitVec.ofNat 8 m == 28) &&
  (14 : BitVec 8).ule (sumCount 4 (fun h => count 7 (hp b h))) &&
  (sumCount 7 (pHOut b)).ule 14 && hNonSeymour b && orderedP b && exactTail m b

end SeymourEight.EpsilonOneXThreeReducedCore
