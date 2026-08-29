import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.CoreSoundness
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.PBridge
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.FixedA
import SeymourEight.Cases.BSevenKOne.TightEpsilonZero.XThree.ExactUnion.Accounting

set_option linter.style.header false

namespace SeymourEight.FourZExactSevenAssembly

open FourZExactSeven FourZExactSevenBridge FourZExactSevenGraphBridge
  FiveZExactRisk FiveZExactGraphBridge FiveZExactGlobalBridge
  FiveZExactPBridge Shared BSevenKOneCounting

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The labelled data consumed after the decoder/global bridge.  The three row
fields are the isolated P/H/Z second-neighborhood soundness obligations; all
other fields are accounting or symmetry labels. -/
structure CompatibleRowData (C : G.LocalConfiguration) where
  missing : Nat
  degreeSum : Nat
  overlap : OverlapType
  p : Fin 7 ≃ {v : V // v ∈ C.P}
  h : Fin 4 ≃ {v : V // v ∈ C.H}
  a : Fin 8 ≃ {v : V // v ∈ C.A}
  z : Fin 4 ≃ {v : V // v ∈ C.Z}
  w : Fin 7 ≃ {v : V // v ∈ FourZExactSevenGraphBridge.zExternalUnion G C}
  missing_le : missing ≤ 1
  pz_count : edgeCount G C.P C.Z + missing = 28
  pz_rows : ∀ i : Nat, (hi : i < 7) →
    directCount G C.Z (p ⟨i, hi⟩).1 =
      if missing = 1 ∧ i = 0 then 3 else 4
  degreeSum_eq : ∑ u ∈ C.P, G.outdegree u = degreeSum
  defectIdentity :
    totalMissingPPairs (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1)) +
      (14 - totalPToH (coreBits G.Adj (fun j ↦ (p j).1)
        (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
        (fun j ↦ (w j).1))) =
      BitVec.ofNat 8 (63 - missing - degreeSum)
  degreeBytes :
    sumCount 7 (pDegree missing (coreBits G.Adj (fun j ↦ (p j).1)
      (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
      (fun j ↦ (w j).1))) = BitVec.ofNat 8 degreeSum
  fixedA : fixedAStructure (coreBits G.Adj (fun j ↦ (p j).1)
    (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
    (fun j ↦ (w j).1)) = true
  zRows : all 4 (fun zi =>
    (8 : BitVec 8).ule (zDegree missing (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) zi) &&
    zNonSeymour missing overlap (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) zi) = true
  hRows : all 4 (hNonSeymour missing (coreBits G.Adj
    (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
    (fun j ↦ (z j).1) (fun j ↦ (w j).1))) = true
  pRows : all 7 (fun pi =>
    (8 : BitVec 8).ule (pDegree missing (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) pi) &&
    (pDegree missing (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) pi).ule 14 &&
    pNonSeymour missing overlap (coreBits G.Adj
      (fun j ↦ (p j).1) (fun j ↦ (h j).1) (fun j ↦ (a j).1)
      (fun j ↦ (z j).1) (fun j ↦ (w j).1)) pi) = true
  orderH : orderedH overlap (coreBits G.Adj (fun j ↦ (p j).1)
    (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
    (fun j ↦ (w j).1)) = true
  orderP : orderedP missing (coreBits G.Adj (fun j ↦ (p j).1)
    (fun j ↦ (h j).1) (fun j ↦ (a j).1) (fun j ↦ (z j).1)
    (fun j ↦ (w j).1)) = true

/-- Assembly independent of the physical row theorem imports. -/
theorem impossible_of_compatibleRowData (C : G.LocalConfiguration)
    (hG : G.IsOriented) (hMin : ∀ v, 8 ≤ G.outdegree v)
    (hRootDegree : G.outdegree C.s = 8) (hk : C.k = 1) (hx : C.x = 3)
    (hPB : C.P = C.B) (hEpsilon : epsilonS G C = 0)
    (d : CompatibleRowData G C)
    (hDispatch : ∀ bits : BitVec 214,
      core d.missing d.degreeSum d.overlap bits = false) : False := by
  let bits := coreBits G.Adj (fun j ↦ (d.p j).1) (fun j ↦ (d.h j).1)
    (fun j ↦ (d.a j).1) (fun j ↦ (d.z j).1) (fun j ↦ (d.w j).1)
  have hCore := coreBits_true G C hG hMin hRootDegree hk hx hPB hEpsilon
    d.missing d.degreeSum d.overlap d.p d.h d.a d.z d.w d.pz_rows
    d.defectIdentity d.degreeBytes d.fixedA d.zRows d.hRows d.pRows
    d.orderH d.orderP
  change core d.missing d.degreeSum d.overlap bits = true at hCore
  rw [hDispatch bits] at hCore
  contradiction

end SeymourEight.FourZExactSevenAssembly
