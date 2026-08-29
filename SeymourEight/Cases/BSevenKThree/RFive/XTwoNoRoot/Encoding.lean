import SeymourEight.Cases.BSevenKThree.RFive.XTwoNoRoot.Labels
import SeymourEight.Certificates.BSevenKThree.RFive.XTwo.CoreDefs

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Encoding

open Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def graphArc {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) : Bool :=
  if hiA : i < 8 then
    if hjA : j < 8 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 13 then
      decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if hjQ : j < 15 then
      decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.q ⟨j - 13, by omega⟩).1)
    else false
  else if hiP : i < 13 then
    if hjA : j < 8 then
      decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 13 then
      decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if hjQ : j < 15 then
      decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.q ⟨j - 13, by omega⟩).1)
    else false
  else false

def graphPToZ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) : Bool :=
  if hp : p < 5 then
    if hz : z < zCount then decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1)
    else false
  else false

def localVertex {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i : Nat) : V :=
  if hiA : i < 8 then (L.a ⟨i, hiA⟩).1
  else if hiP : i < 13 then (L.p ⟨i - 8, by omega⟩).1
  else if hiQ : i < 15 then (L.q ⟨i - 13, by omega⟩).1
  else (L.q 0).1

@[simp] theorem graphArc_A {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    graphArc G L i j = decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  simp [graphArc, hi, hj]

@[simp] theorem graphArc_AP {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i p : Nat) (hi : i < 8) (hp : p < 5) :
    graphArc G L i (8 + p) =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.p ⟨p, hp⟩).1) := by
  simp [graphArc, hi, show 8 + p < 13 by omega]

@[simp] theorem graphArc_PA {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p i : Nat) (hp : p < 5) (hi : i < 8) :
    graphArc G L (8 + p) i =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨i, hi⟩).1) := by
  simp [graphArc, hi, show 8 + p < 13 by omega]

@[simp] theorem graphArc_AQ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i q : Nat) (hi : i < 8) (hq : q < 2) :
    graphArc G L i (13 + q) =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.q ⟨q, hq⟩).1) := by
  simp [graphArc, hi, show ¬13 + q < 8 by omega,
    show ¬13 + q < 13 by omega, show 13 + q < 15 by omega]

@[simp] theorem graphArc_PQ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p q : Nat) (hp : p < 5) (hq : q < 2) :
    graphArc G L (8 + p) (13 + q) =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.q ⟨q, hq⟩).1) := by
  simp [graphArc, show 8 + p < 13 by omega, show ¬13 + q < 13 by omega,
    show ¬13 + q < 8 by omega, show 13 + q < 15 by omega]

@[simp] theorem graphPToZ_eq {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) (hp : p < 5) (hz : z < zCount) :
    graphPToZ G L p z =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  simp [graphPToZ, hp, hz]

end SeymourEight.BSevenKThree.RFive.XTwoNoRoot.Encoding
