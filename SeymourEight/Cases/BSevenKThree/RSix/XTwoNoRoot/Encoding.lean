import SeymourEight.Cases.BSevenKThree.RSix.XTwoNoRoot.Labels
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.CoreDefs
import SeymourEight.Certificates.BSevenKThree.RSix.XTwo.HardDefs

set_option linter.style.header false

namespace SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Encoding

open Labels

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def graphArc {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) : Bool :=
  if hiA : i < 8 then
    if hjA : j < 8 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 14 then
      decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if j = 14 then decide (G.Adj (L.a ⟨i, hiA⟩).1 (L.q 0).1)
    else false
  else if hiP : i < 14 then
    if hjA : j < 8 then
      decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.a ⟨j, hjA⟩).1)
    else if hjP : j < 14 then
      decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.p ⟨j - 8, by omega⟩).1)
    else if j = 14 then decide (G.Adj (L.p ⟨i - 8, by omega⟩).1 (L.q 0).1)
    else false
  else false

def graphPToZ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) : Bool :=
  if hp : p < 6 then
    if hz : z < zCount then decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1)
    else false
  else false

def localVertex {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i : Nat) : V :=
  if hiA : i < 8 then (L.a ⟨i, hiA⟩).1
  else if hiP : i < 14 then (L.p ⟨i - 8, by omega⟩).1
  else (L.q 0).1

def auxiliaryVertex {C : G.LocalConfiguration} (L : Labels G 5 C)
    (i : Nat) : V :=
  if hi : i < 6 then
    if i = 0 then (L.q 0).1 else (L.z ⟨i - 1, by omega⟩).1
  else (L.q 0).1

@[simp] theorem graphArc_A {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    graphArc G L i j = decide (G.Adj (L.a ⟨i, hi⟩).1 (L.a ⟨j, hj⟩).1) := by
  simp [graphArc, hi, hj]

@[simp] theorem graphArc_AP {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i p : Nat) (hi : i < 8) (hp : p < 6) :
    graphArc G L i (8 + p) =
      decide (G.Adj (L.a ⟨i, hi⟩).1 (L.p ⟨p, hp⟩).1) := by
  have hip : 8 + p < 14 := by omega
  simp [graphArc, hi, hip]

@[simp] theorem graphArc_PA {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p i : Nat) (hp : p < 6) (hi : i < 8) :
    graphArc G L (8 + p) i =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.a ⟨i, hi⟩).1) := by
  have hip : 8 + p < 14 := by omega
  simp [graphArc, hi, hip]

@[simp] theorem graphArc_P {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p r : Nat) (hp : p < 6) (hr : r < 6) :
    graphArc G L (8 + p) (8 + r) =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.p ⟨r, hr⟩).1) := by
  have hip : 8 + p < 14 := by omega
  have hir : 8 + r < 14 := by omega
  simp [graphArc, hip, hir]

@[simp] theorem graphArc_AQ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (i : Nat) (hi : i < 8) :
    graphArc G L i 14 = decide (G.Adj (L.a ⟨i, hi⟩).1 (L.q 0).1) := by
  simp [graphArc, hi]

@[simp] theorem graphArc_PQ {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p : Nat) (hp : p < 6) :
    graphArc G L (8 + p) 14 =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.q 0).1) := by
  have hip : 8 + p < 14 := by omega
  simp [graphArc, hip]

@[simp] theorem graphPToZ_eq {zCount : Nat} {C : G.LocalConfiguration}
    (L : Labels G zCount C) (p z : Nat) (hp : p < 6) (hz : z < zCount) :
    graphPToZ G L p z =
      decide (G.Adj (L.p ⟨p, hp⟩).1 (L.z ⟨z, hz⟩).1) := by
  simp [graphPToZ, hp, hz]

end SeymourEight.BSevenKThree.RSix.XTwoNoRoot.Encoding
