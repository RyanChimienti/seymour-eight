import SeymourEight.Certificates.BSevenKThree.RSix.XFour.HDeletionDefs

/-!
# Reconstructed arc tables in the `alpha = 0` rows

The dual identity forces every `H–P` pair to contain one arc and every
`H` vertex to point to `q`.  When `aMissing = 0`, the same is true of every
unordered pair in `A`.  The definitions below retain just one Boolean for
each such complementary pair.
-/

namespace SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid

open Shared.FiniteCore Core HDeletion

def alphaZeroArc (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  if i = 0 ∧ j < 15 then
    decide (1 ≤ j ∧ j ≤ 3 ∨ 8 ≤ j ∧ j < 14)
  else if 8 ≤ i ∧ i < 14 ∧ j = 0 then false
  else if 1 ≤ i ∧ i < 8 ∧ 8 ≤ j ∧ j < 14 then raw i j
  else if 8 ≤ i ∧ i < 14 ∧ 1 ≤ j ∧ j < 8 then !raw j i
  else if 1 ≤ i ∧ i < 8 ∧ j = 14 then true
  else raw i j

def fixedArc (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  if i = 0 ∧ j < 15 then
    decide (1 ≤ j ∧ j ≤ 3 ∨ 8 ≤ j ∧ j < 14)
  else if 8 ≤ i ∧ i < 14 ∧ j = 0 then false
  else raw i j

def aRigidArc (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  if i < 8 ∧ j < 8 then
    if i = 0 then decide (1 ≤ j ∧ j ≤ 3)
    else if j = 0 then decide (4 ≤ i ∧ i < 8)
    else if i = j then false
    else if i < j then raw i j
    else !raw j i
  else fixedArc raw i j

def rigidArc (raw : Nat → Nat → Bool) (i j : Nat) : Bool :=
  if i < 8 ∧ j < 8 then
    if i = 0 then decide (1 ≤ j ∧ j ≤ 3)
    else if j = 0 then decide (4 ≤ i ∧ i < 8)
    else if i = j then false
    else if i < j then raw i j
    else !raw j i
  else alphaZeroArc raw i j

def hQComplete (arc : Nat → Nat → Bool) : Bool :=
  all 7 fun h ↦ aToQ arc (1 + h)

def hpDirectionsComplete (arc : Nat → Nat → Bool) : Bool :=
  all 6 fun p ↦ all 7 fun h ↦
    pToA arc p (1 + h) == !aToP arc (1 + h) p

def aDirectionsComplete (arc : Nat → Nat → Bool) : Bool :=
  all 8 fun i ↦ !aArc arc i i && all 8 fun j ↦
    decide (i = j) || aArc arc i j == !aArc arc j i

def alphaZeroPremise (arc : Nat → Nat → Bool) : Bool :=
  fixedAOne arc && noPToAOne arc && hQComplete arc &&
    hpDirectionsComplete arc

def rigidPremise (arc : Nat → Nat → Bool) : Bool :=
  alphaZeroPremise arc && aDirectionsComplete arc

def alphaZeroAgreement (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun i ↦ all 15 fun j ↦ alphaZeroArc arc i j == arc i j

def rigidAgreement (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun i ↦ all 15 fun j ↦ rigidArc arc i j == arc i j

def fixedPremise (arc : Nat → Nat → Bool) : Bool :=
  fixedAOne arc && noPToAOne arc

def aRigidPremise (arc : Nat → Nat → Bool) : Bool :=
  fixedPremise arc && aDirectionsComplete arc

def aRigidAgreement (arc : Nat → Nat → Bool) : Bool :=
  all 15 fun i ↦ all 15 fun j ↦ aRigidArc arc i j == arc i j

def rigidHDeletionLeaf (m alphaValue betaValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  hDeletionLeaf m 0 alphaValue betaValue (rigidArc raw) pToZ

def semiRigidHDeletionLeaf (m delta alphaValue betaValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  hDeletionLeaf m delta alphaValue betaValue (alphaZeroArc raw) pToZ

def aRigidDualHDeletionLeaf
    (m alphaValue betaValue etaValue hqValue crossValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  dualHDeletionLeaf m 0 alphaValue betaValue etaValue hqValue crossValue
    (aRigidArc raw) pToZ

def rigidDualHDeletionLeaf
    (m alphaValue betaValue etaValue hqValue crossValue : Nat)
    (raw pToZ : Nat → Nat → Bool) : Bool :=
  dualHDeletionLeaf m 0 alphaValue betaValue etaValue hqValue crossValue
    (rigidArc raw) pToZ

end SeymourEight.BSevenKThree.RSix.XFourNoRoot.Rigid
