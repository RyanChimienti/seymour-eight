import SeymourEight.Cases.BSevenKTwo.RSix.XTwoNoRoot.GraphBridge

set_option linter.style.header false
set_option maxRecDepth 10000

namespace SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.MicroScratch

open Shared Shared.FiniteCore CertificateBridge
open Labels Encoding Core GraphBridge

variable {V : Type*} (G : Digraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private abbrev bits {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) : Core.Encoding := Encoding.coreBits G.Adj L

theorem aOneSecondH_true_local (b : Core.Encoding)
    (a h : Nat) (ha : a < 4) (hh : h < 4)
    (hFixed : fixedA b = true)
    (hs : aOneSecondH b a h = true) :
    strictSecondLocal 5 true b (1 + a) (1 + h) = true := by
  simp only [aOneSecondH, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hs
  rcases hs with ⟨⟨hne, hNot⟩, hVia⟩
  have hne' : a ≠ h := by simpa using hne
  rw [strictSecondLocal, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simp
      omega
    · simpa [coreArc, hArc, show 1 + a < 8 by omega,
        show 1 + h < 8 by omega] using hNot
  · rw [reachesLocal, any_eq_true_iff]
    rcases hVia with hViaHP | hViaT
    · rcases hViaHP with hViaH | hViaP
      · obtain ⟨k, hk, hpath⟩ := (any_eq_true_iff 4 _).mp hViaH
        refine ⟨1 + k, by omega, ?_⟩
        simpa [coreArc, hArc, show 1 + a < 8 by omega,
          show 1 + h < 8 by omega, show 1 + k < 8 by omega] using hpath
      · obtain ⟨p, hp, hpath⟩ := (any_eq_true_iff 6 _).mp hViaP
        refine ⟨8 + p, by omega, ?_⟩
        have hms : (8 + p != 1 + a) = true := by simp; omega
        have hmt : (8 + p != 1 + h) = true := by simp; omega
        simpa [coreArc, aToP, hToP, pToA, hms, hmt,
          show 1 + a < 8 by omega, show 1 + h < 8 by omega,
          show 8 + p < 14 by omega, show 1 + a < 5 by omega,
          show 0 < 1 + h by omega, show 1 + h < 5 by omega] using hpath
    · refine ⟨0, by omega, ?_⟩
      rcases hViaT with ⟨⟨haX, hh2⟩, hxa⟩
      have hA1Target : aArc b 0 (1 + h) = true := by
        interval_cases h <;> simp_all [fixedA]
      have hms : (0 != 1 + a) = true := by simp; omega
      have hmt : (0 != 1 + h) = true := by simp; omega
      have haEq : 1 + a = 3 + (a - 2) := by omega
      simpa [coreArc, xToT, hms, hmt, haEq,
        show 3 + (a - 2) < 8 by omega, show 1 + h < 8 by omega,
        hA1Target] using And.intro
          (And.intro (by omega : ¬0 = 3 + (a - 2)) hxa) hA1Target

set_option linter.flexible false in
theorem aOneSecondP_true_local (b : Core.Encoding)
    (a p : Nat) (ha : a < 4) (hp : p < 6)
    (_hFixed : fixedA b = true)
    (hs : aOneSecondP b a p = true) :
    strictSecondLocal 5 true b (1 + a) (8 + p) = true := by
  simp only [aOneSecondP, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hs
  rcases hs with ⟨hNot, (hVia | hVia) | hVia⟩
  · obtain ⟨h, hh, hpath⟩ := (any_eq_true_iff 4 _).mp hVia
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpath
    rcases hpath with ⟨⟨hne, hah⟩, hhp⟩
    rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · simp; omega
      · simpa [coreArc, aToP, hToP, show 1 + a < 8 by omega,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show 1 + a < 5 by omega] using hNot
    · rw [reachesLocal, any_eq_true_iff]
      refine ⟨1 + h, by omega, ?_⟩
      simpa [coreArc, aToP, hToP, hArc, show 1 + a < 8 by omega,
        show 1 + h < 8 by omega, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega, show 1 + a < 5 by omega,
        show 1 + h < 5 by omega] using
          And.intro (And.intro
            (And.intro (by simpa using hne : 1 + h ≠ 1 + a)
              (by omega : 1 + h ≠ 8 + p)) hah) hhp
  · obtain ⟨q, hq, hpath⟩ := (any_eq_true_iff 6 _).mp hVia
    simp only [Bool.and_eq_true] at hpath
    rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · simp; omega
      · simpa [coreArc, aToP, hToP, show 1 + a < 8 by omega,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show 1 + a < 5 by omega] using hNot
    · rw [reachesLocal, any_eq_true_iff]
      refine ⟨8 + q, by omega, ?_⟩
      have hqp : q ≠ p := by
        have := hpath.2
        simp [pArc] at this
        exact this.1
      simpa [coreArc, aToP, hToP, show 1 + a < 8 by omega,
        show ¬8 + q < 8 by omega, show 8 + q < 14 by omega,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show 1 + a < 5 by omega] using
          And.intro (And.intro (And.intro (by omega : 8 + q ≠ 1 + a)
            (by omega : 8 + q ≠ 8 + p)) hpath.1) hpath.2
  · rcases hVia with ⟨haX, hxa⟩
    rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · simp; omega
      · simpa [coreArc, aToP, hToP, show 1 + a < 8 by omega,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show 1 + a < 5 by omega] using hNot
    · rw [reachesLocal, any_eq_true_iff]
      refine ⟨0, by omega, ?_⟩
      have hPivotP : aToP b 0 p = true := by simp [aToP]
      have haEq : 1 + a = 3 + (a - 2) := by omega
      simpa [coreArc, xToT, haEq, show 1 + a < 8 by omega,
        show 3 + (a - 2) < 8 by omega,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        hPivotP] using And.intro
          (And.intro (by omega : 0 ≠ 1 + a) (by omega : 0 ≠ 8 + p))
          (And.intro hxa hPivotP)

theorem aOneSecondZ_true_local (b : Core.Encoding)
    (a z : Nat) (ha : a < 4) (hz : z < 4)
    (hs : aOneSecondZ b a z = true) :
    strictSecondLocal 5 true b (1 + a) (15 + z) = true := by
  obtain ⟨p, hp, hpath⟩ := (any_eq_true_iff 6 _).mp hs
  simp only [Bool.and_eq_true] at hpath
  rw [strictSecondLocal, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simp; omega
    · simp [coreArc, show 1 + a < 8 by omega, show ¬15 + z < 8 by omega,
      show ¬15 + z < 14 by omega, show ¬15 + z = 14 by omega]
  · rw [reachesLocal, any_eq_true_iff]
    refine ⟨8 + p, by omega, ?_⟩
    simpa [coreArc, aToP, hToP, show 1 + a < 8 by omega,
      show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
      show ¬15 + z < 8 by omega, show ¬15 + z < 14 by omega,
      show 15 + z < 19 by omega, show 15 + z - 14 = 1 + z by omega,
      show 1 + a < 5 by omega] using
        And.intro (And.intro (And.intro (by omega : 8 + p ≠ 1 + a)
          (by omega : 8 + p ≠ 15 + z)) hpath.1) hpath.2

theorem aOneSecondT_true_local (b : Core.Encoding)
    (a t : Nat) (ha : a < 4) (ht : t < 4)
    (hFixed : fixedA b = true)
    (hAOneA1 : ∀ a, a < 2 → aArc b (1 + a) 0 = false)
    (hNoHLoop : ∀ h, h < 4 → hArc b h h = false)
    (hs : aOneSecondT b a t = true) :
    strictSecondLocal 5 true b (1 + a)
      (if t = 0 then 0 else 4 + t) = true := by
  simp only [aOneSecondT, Bool.and_eq_true] at hs
  rcases hs with ⟨hNot, hVia⟩
  obtain ⟨x, hx, hpath⟩ := (any_eq_true_iff 2 _).mp hVia
  simp only [Bool.and_eq_true] at hpath
  let target := if t = 0 then 0 else 4 + t
  have ht8 : target < 8 := by dsimp [target]; split <;> omega
  rw [strictSecondLocal, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simp
      split <;> omega
    · by_cases ha2 : a < 2
      · by_cases ht0 : t = 0
        · subst t
          simpa [target, coreArc, show 1 + a < 8 by omega] using hAOneA1 a ha2
        · have hNoR : aArc b (1 + a) (4 + t) = false := by
            interval_cases a <;> interval_cases t <;>
              simp_all [fixedA, all]
          simpa [target, ht0, coreArc, show 1 + a < 8 by omega,
            show 4 + t < 8 by omega] using hNoR
      · have haEq : 1 + a = 3 + (a - 2) := by omega
        simp [ha2] at hNot
        simpa [target, coreArc, xToT, haEq, ht8,
          show 3 + (a - 2) < 8 by omega,
          show 1 + a < 8 by omega] using hNot
  · rw [reachesLocal, any_eq_true_iff]
    refine ⟨3 + x, by omega, ?_⟩
    have hmt : 3 + x ≠ target := by
      change 3 + x ≠ (if t = 0 then 0 else 4 + t)
      by_cases ht0 : t = 0 <;> simp [ht0] ; omega
    have hms : 3 + x ≠ 1 + a := by
      intro heq
      have haEq : a = 2 + x := by omega
      have hloop := hNoHLoop (2 + x) (by omega)
      rw [haEq] at hpath
      have hbad : hArc b (2 + x) (2 + x) = true := by
        simpa [Nat.add_assoc] using hpath.1
      rw [hloop] at hbad
      contradiction
    simpa [target, coreArc, xToT, hArc, ht8,
      show 1 + (2 + x) = 3 + x by omega, show 1 + a < 8 by omega,
      show 3 + x < 8 by omega] using And.intro
        (And.intro (And.intro hms hmt) hpath.1) hpath.2

theorem hSecondQCore_true_local (c : Nat) (b : Core.Encoding)
    (h : Nat) (hh : h < 4) (hs : hSecondQCore c b h = true) :
    strictSecondLocal 5 true b (1 + h) 14 = true := by
  simp only [hSecondQCore, Bool.and_eq_true, Bool.or_eq_true] at hs
  rcases hs with ⟨hNot, hVia | hVia⟩
  · rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · simp; omega
      · simpa [coreArc, hToQCore, show 1 + h < 8 by omega] using hNot
    · obtain ⟨k, hk, hpath⟩ := (any_eq_true_iff 4 _).mp hVia
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpath
      rw [reachesLocal, any_eq_true_iff]
      refine ⟨1 + k, by omega, ?_⟩
      simpa [coreArc, hToQCore, hArc, show 1 + h < 8 by omega,
        show 1 + k < 8 by omega] using
          And.intro (And.intro (And.intro hpath.1.1
            (by omega : 1 + k ≠ 14)) hpath.1.2) hpath.2
  · rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · simp; omega
      · simpa [coreArc, hToQCore, show 1 + h < 8 by omega] using hNot
    · obtain ⟨p, hp, hpath⟩ := (any_eq_true_iff 6 _).mp hVia
      simp only [Bool.and_eq_true] at hpath
      rw [reachesLocal, any_eq_true_iff]
      refine ⟨8 + p, by omega, ?_⟩
      simpa [coreArc, aToP, hToP, show 1 + h < 8 by omega,
        show 1 + h < 5 by omega, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega] using
          And.intro (And.intro (And.intro (by omega : 8 + p ≠ 1 + h)
            (by omega : 8 + p ≠ 14)) hpath.1) hpath.2

set_option linter.flexible false in
theorem pSecondP_true_local (b : Core.Encoding)
    (p q : Nat) (hp : p < 6) (hq : q < 6)
    (hs : (!pArc b p q && reachesPH b p q) = true) :
    strictSecondLocal 5 true b (8 + p) (8 + q) = true := by
  simp only [Bool.and_eq_true] at hs
  rcases hs with ⟨hNot, hReach⟩
  simp only [reachesPH, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hReach
  rcases hReach with ⟨hpq, hDirect | hVia⟩
  · simp [hDirect] at hNot
  have hpq' : p ≠ q := by simpa using hpq
  obtain ⟨m, hm, hpath⟩ := (any_eq_true_iff 10 _).mp hVia
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpath
  let w := if m < 6 then 8 + m else 1 + (m - 6)
  have hw14 : w < 14 := by dsimp [w]; split <;> omega
  rw [strictSecondLocal, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simp
      intro heq
      apply hpq'
      omega
    · simpa [coreArc, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega, show ¬8 + q < 8 by omega,
        show 8 + q < 14 by omega] using hNot
  · rw [reachesLocal, any_eq_true_iff]
    refine ⟨w, hw14, ?_⟩
    dsimp [w] at hpath ⊢
    simpa [w, coreArc, hw14, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega, show ¬8 + q < 8 by omega,
      show 8 + q < 14 by omega] using hpath

set_option linter.flexible false in
theorem pSecondHMicro_true_local (b : Core.Encoding)
    (p h : Nat) (hp : p < 6) (hh : h < 4)
    (hNoHLoop : ∀ k, k < 4 → hArc b k k = false)
    (hs : (!pToH b p h &&
      (any 6 (fun q => pArc b p q && pToH b q h) ||
       any 4 (fun k => pToH b p k && hArc b k h))) = true) :
    strictSecondLocal 5 true b (8 + p) (1 + h) = true := by
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hs
  rcases hs with ⟨hNot, hVia | hVia⟩
  all_goals rw [strictSecondLocal, Bool.and_eq_true]
  · constructor
    · rw [Bool.and_eq_true]
      refine ⟨(by simp; omega), ?_⟩
      simpa [coreArc, pToA,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show 1 + h < 8 by omega, show 0 < 1 + h by omega,
        show 1 + h < 5 by omega] using hNot
    · obtain ⟨q, hq, hpath⟩ := (any_eq_true_iff 6 _).mp hVia
      simp only [Bool.and_eq_true] at hpath
      have hqp : q ≠ p := by
        have := hpath.1
        simp [pArc] at this
        exact fun heq => this.1 heq.symm
      rw [reachesLocal, any_eq_true_iff]
      refine ⟨8 + q, by omega, ?_⟩
      simpa [coreArc, pToA, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega, show ¬8 + q < 8 by omega,
        show 8 + q < 14 by omega, show 1 + h < 8 by omega,
        show 0 < 1 + h by omega, show 1 + h < 5 by omega] using
          And.intro (And.intro (And.intro (by omega : 8 + q ≠ 8 + p)
            (by omega : 8 + q ≠ 1 + h)) hpath.1) hpath.2
  · constructor
    · rw [Bool.and_eq_true]
      refine ⟨(by simp; omega), ?_⟩
      simpa [coreArc, pToA,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show 1 + h < 8 by omega, show 0 < 1 + h by omega,
        show 1 + h < 5 by omega] using hNot
    · obtain ⟨k, hk, hpath⟩ := (any_eq_true_iff 4 _).mp hVia
      simp only [Bool.and_eq_true] at hpath
      have hkh : k ≠ h := by
        intro heq
        subst k
        have hloop := hNoHLoop h hh
        rw [hloop] at hpath
        simp at hpath
      rw [reachesLocal, any_eq_true_iff]
      refine ⟨1 + k, by omega, ?_⟩
      simpa [coreArc, pToA, hArc, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega, show 1 + k < 8 by omega,
        show 0 < 1 + k by omega, show 1 + k < 5 by omega,
        show 1 + h < 8 by omega] using
          And.intro (And.intro (And.intro (by omega : 1 + k ≠ 8 + p)
            (by omega : 1 + k ≠ 1 + h)) hpath.1) hpath.2

set_option linter.flexible false in
theorem pSecondEMicroCore_true_local (c : Nat) (b : Core.Encoding)
    (p e : Nat) (hp : p < 6) (he : e < 5)
    (hs : (!pToE b p e &&
      (any 6 (fun q => pArc b p q && pToE b q e) ||
       (decide (e = 0) && any 4 (fun h =>
          pToH b p h && hToQCore c b h)))) = true) :
    strictSecondLocal 5 true b (8 + p) (14 + e) = true := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hs
  rcases hs with ⟨hNot, hVia | ⟨he0, hVia⟩⟩
  · obtain ⟨q, hq, hpath⟩ := (any_eq_true_iff 6 _).mp hVia
    simp only [Bool.and_eq_true] at hpath
    have hqp : q ≠ p := by
      have := hpath.1
      simp [pArc] at this
      exact fun heq => this.1 heq.symm
    rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      refine ⟨(by simp; omega), ?_⟩
      simpa [coreArc,
        show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
        show ¬14 + e < 8 by omega, show ¬14 + e < 14 by omega,
        show 14 + e < 19 by omega] using hNot
    · rw [reachesLocal, any_eq_true_iff]
      refine ⟨8 + q, by omega, ?_⟩
      simpa [coreArc, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega, show ¬8 + q < 8 by omega,
        show 8 + q < 14 by omega, show ¬14 + e < 8 by omega,
        show ¬14 + e < 14 by omega, show 14 + e < 19 by omega] using
          And.intro (And.intro (And.intro (by omega : 8 + q ≠ 8 + p)
            (by omega : 8 + q ≠ 14 + e)) hpath.1) hpath.2
  · subst e
    obtain ⟨h, hh, hpath⟩ := (any_eq_true_iff 4 _).mp hVia
    simp only [Bool.and_eq_true] at hpath
    rw [strictSecondLocal, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      refine ⟨(by simp; omega), ?_⟩
      simpa [coreArc, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega] using hNot
    · rw [reachesLocal, any_eq_true_iff]
      refine ⟨1 + h, by omega, ?_⟩
      simpa [coreArc, pToA, hToQCore, show ¬8 + p < 8 by omega,
        show 8 + p < 14 by omega, show 1 + h < 8 by omega,
        show 0 < 1 + h by omega, show 1 + h < 5 by omega] using
        And.intro (And.intro (And.intro (by omega : 1 + h ≠ 8 + p)
          (by omega : 1 + h ≠ 14)) hpath.1) hpath.2

theorem pSecondT_true_local (b : Core.Encoding)
    (p t : Nat) (hp : p < 6) (ht : t < 4)
    (hs : (any 2 fun x => pToH b p (2 + x) && xToT b x t) = true) :
    strictSecondLocal 5 true b (8 + p)
      (if t = 0 then 0 else 4 + t) = true := by
  obtain ⟨x, hx, hpath⟩ := (any_eq_true_iff 2 _).mp hs
  simp only [Bool.and_eq_true] at hpath
  let target := if t = 0 then 0 else 4 + t
  have ht8 : target < 8 := by dsimp [target]; split <;> omega
  rw [strictSecondLocal, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · simp; split <;> omega
    · by_cases ht0 : t = 0
      · subst t
        simp [coreArc, pToA, show ¬8 + p < 8 by omega,
          show 8 + p < 14 by omega]
      · interval_cases t <;> simp_all [target, coreArc, pToA]
  · rw [reachesLocal, any_eq_true_iff]
    refine ⟨3 + x, by omega, ?_⟩
    have hmt : 3 + x ≠ target := by
      change 3 + x ≠ (if t = 0 then 0 else 4 + t)
      by_cases ht0 : t = 0 <;> simp [ht0] ; omega
    simpa [target, coreArc, pToA, xToT,
      show ¬8 + p < 8 by omega, show 8 + p < 14 by omega,
      show 1 + (2 + x) = 3 + x by omega, show 3 + x < 8 by omega,
      show 0 < 3 + x by omega, show 3 + x < 5 by omega, ht8] using
        And.intro (And.intro (And.intro (by omega : 3 + x ≠ 8 + p) hmt)
          hpath.1) hpath.2

private theorem count_toNat_le (n : Nat) (f : Nat → Bool) (hn : n < 256) :
    (count n f).toNat ≤ n := by
  rw [toNat_count n f hn]
  calc
    _ ≤ ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases f i <;> decide
    _ = n := by simp

private theorem bitCount_mono {a b : Bool} (h : a = true → b = true) :
    (bitCount a).toNat ≤ (bitCount b).toNat := by
  cases a <;> cases b <;> simp_all [bitCount]

theorem five_blocks_le_local
    (fH fP fZ fT : Nat → Bool) (fq : Bool) (g : Nat → Bool)
    (hH : ∀ i, i < 4 → fH i = true → g (1 + i) = true)
    (hP : ∀ i, i < 6 → fP i = true → g (8 + i) = true)
    (hZ : ∀ i, i < 4 → fZ i = true → g (15 + i) = true)
    (hT : ∀ i, i < 4 → fT i = true →
      g (if i = 0 then 0 else 4 + i) = true)
    (hq : fq = true → g 14 = true) :
    (count 4 fH + count 6 fP + count 4 fZ + count 4 fT + bitCount fq).toNat ≤
      (count 19 g).toNat := by
  have bH := count_toNat_le 4 fH (by omega)
  have bP := count_toNat_le 6 fP (by omega)
  have bZ := count_toNat_le 4 fZ (by omega)
  have bT := count_toNat_le 4 fT (by omega)
  have bq : (bitCount fq).toNat ≤ 1 := by cases fq <;> decide
  simp only [BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega : (count 4 fH).toNat + (count 6 fP).toNat < 256),
    Nat.mod_eq_of_lt (by omega : (count 4 fH).toNat + (count 6 fP).toNat +
      (count 4 fZ).toNat < 256),
    Nat.mod_eq_of_lt (by omega : (count 4 fH).toNat + (count 6 fP).toNat +
      (count 4 fZ).toNat + (count 4 fT).toNat < 256),
    Nat.mod_eq_of_lt (by omega : (count 4 fH).toNat + (count 6 fP).toNat +
      (count 4 fZ).toNat + (count 4 fT).toNat + (bitCount fq).toNat < 256)]
  rw [toNat_count 4 fH (by omega), toNat_count 6 fP (by omega),
    toNat_count 4 fZ (by omega), toNat_count 4 fT (by omega),
    toNat_count 19 g (by omega)]
  norm_num [Finset.sum_range_succ]
  have h0 := bitCount_mono (hT 0 (by omega))
  have h1 := bitCount_mono (hH 0 (by omega))
  have h2 := bitCount_mono (hH 1 (by omega))
  have h3 := bitCount_mono (hH 2 (by omega))
  have h4 := bitCount_mono (hH 3 (by omega))
  have h5 := bitCount_mono (hT 1 (by omega))
  have h6 := bitCount_mono (hT 2 (by omega))
  have h7 := bitCount_mono (hT 3 (by omega))
  have h8 := bitCount_mono (hP 0 (by omega))
  have h9 := bitCount_mono (hP 1 (by omega))
  have h10 := bitCount_mono (hP 2 (by omega))
  have h11 := bitCount_mono (hP 3 (by omega))
  have h12 := bitCount_mono (hP 4 (by omega))
  have h13 := bitCount_mono (hP 5 (by omega))
  have h14 := bitCount_mono hq
  have h15 := bitCount_mono (hZ 0 (by omega))
  have h16 := bitCount_mono (hZ 1 (by omega))
  have h17 := bitCount_mono (hZ 2 (by omega))
  have h18 := bitCount_mono (hZ 3 (by omega))
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  omega

theorem hRestrictedSecondCountCore_le_local (c : Nat) (b : Core.Encoding)
    (h : Nat) (hh : h < 4) (hFixed : fixedA b = true)
    (hAOneA1 : ∀ a, a < 2 → aArc b (1 + a) 0 = false)
    (hNoHLoop : ∀ k, k < 4 → hArc b k k = false) :
    (hRestrictedSecondCountCore c b h).toNat ≤
      (localSecondCount 5 true b (1 + h)).toNat := by
  unfold hRestrictedSecondCountCore localSecondCount
  apply five_blocks_le_local
  · intro i hi hs
    exact aOneSecondH_true_local b h i hh hi hFixed hs
  · intro i hi hs
    exact aOneSecondP_true_local b h i hh hi hFixed hs
  · intro i hi hs
    exact aOneSecondZ_true_local b h i hh hi hs
  · intro i hi hs
    exact aOneSecondT_true_local b h i hh hi hFixed hAOneA1 hNoHLoop hs
  · intro hs
    exact hSecondQCore_true_local c b h hh hs

private theorem count_three_le_four (f : Nat → Bool) :
    (count 3 f).toNat ≤ (count 4 f).toNat := by
  rw [toNat_count 3 f (by omega), toNat_count 4 f (by omega)]
  simp only [Finset.sum_range_succ]
  omega

theorem hRestrictedSecondCountFour_le_core (c : Nat) (b : Core.Encoding)
    (h : Nat) :
    (hRestrictedSecondCountFour c b h).toNat ≤
      (hRestrictedSecondCountCore c b h).toNat := by
  have bH := count_toNat_le 4 (aOneSecondH b h) (by omega)
  have bP := count_toNat_le 6 (aOneSecondP b h) (by omega)
  have bZ3 := count_toNat_le 3
    (fun z => any 6 fun p => hToP b h p && pToE b p (1 + z)) (by omega)
  have bZ4 := count_toNat_le 4
    (fun z => any 6 fun p => hToP b h p && pToE b p (1 + z)) (by omega)
  have bT := count_toNat_le 4 (aOneSecondT b h) (by omega)
  have bq : (bitCount (hSecondQCore c b h)).toNat ≤ 1 := by
    cases hSecondQCore c b h <;> decide
  have hZ := count_three_le_four
    (fun z => any 6 fun p => hToP b h p && pToE b p (1 + z))
  unfold hRestrictedSecondCountFour hRestrictedSecondCountCore hSecondZCount
    aOneSecondZ
  simp only [BitVec.toNat_add]
  repeat' first | rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem p_blocks_reorder
    (fP fH fE fT : Nat → Bool) :
    (count 6 fP + count 4 fH + count 5 fE + count 4 fT).toNat =
      (count 4 fH + count 6 fP + count 4 (fun i => fE (1 + i)) +
        count 4 fT + bitCount (fE 0)).toNat := by
  have bP := count_toNat_le 6 fP (by omega)
  have bH := count_toNat_le 4 fH (by omega)
  have bE := count_toNat_le 5 fE (by omega)
  have bZ := count_toNat_le 4 (fun i => fE (1 + i)) (by omega)
  have bT := count_toNat_le 4 fT (by omega)
  have bq : (bitCount (fE 0)).toNat ≤ 1 := by cases fE 0 <;> decide
  simp only [BitVec.toNat_add]
  repeat' first
    | rw [Nat.mod_eq_of_lt (by omega)]
  rw [toNat_count 6 fP (by omega), toNat_count 4 fH (by omega),
    toNat_count 5 fE (by omega), toNat_count 4 fT (by omega),
    toNat_count 4 (fun i => fE (1 + i)) (by omega)]
  norm_num [Finset.sum_range_succ]
  omega

theorem pMicroSecondCountCore_le_local (c : Nat) (b : Core.Encoding)
    (p : Nat) (hp : p < 6)
    (hNoHLoop : ∀ k, k < 4 → hArc b k k = false) :
    (pSecondPCount b p + pSecondHMicroCount b p +
      pSecondEMicroCoreCount c b p + pSecondTCount b p).toNat ≤
      (localSecondCount 5 true b (8 + p)).toNat := by
  let fP := fun q => !pArc b p q && reachesPH b p q
  let fH := fun h => !pToH b p h &&
    (any 6 (fun q => pArc b p q && pToH b q h) ||
      any 4 (fun k => pToH b p k && hArc b k h))
  let fE := fun e => !pToE b p e &&
    (any 6 (fun q => pArc b p q && pToE b q e) ||
      (decide (e = 0) && any 4 (fun h =>
        pToH b p h && hToQCore c b h)))
  let fT := fun t => any 2 fun x => pToH b p (2 + x) && xToT b x t
  have hc := five_blocks_le_local fH fP (fun i => fE (1 + i)) fT (fE 0)
    (strictSecondLocal 5 true b (8 + p))
    (fun i hi hs => pSecondHMicro_true_local b p i hp hi hNoHLoop hs)
    (fun i hi hs => pSecondP_true_local b p i hp hi hs)
    (fun i hi hs => by
      simpa [show 14 + (1 + i) = 15 + i by omega] using
        pSecondEMicroCore_true_local c b p (1 + i) hp (by omega) hs)
    (fun i hi hs => pSecondT_true_local b p i hp hi hs)
    (fun hs => pSecondEMicroCore_true_local c b p 0 hp (by omega) hs)
  change (count 6 fP + count 4 fH + count 5 fE + count 4 fT).toNat ≤ _
  rw [p_blocks_reorder]
  exact hc

def labelledVertex {C : G.LocalConfiguration} {q : V}
    (L : ReachedLabels G C q) (n : Nat) : V :=
  if hnA : n < 8 then (L.a ⟨n, hnA⟩).1
  else if hnP : n < 14 then (L.p ⟨n - 8, by omega⟩).1
  else if hnE : n < 19 then L.e ⟨n - 14, by omega⟩
  else C.s

theorem coreArc_graphBits (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (source target : Nat) (hs : source < 14) (ht : target < 19) :
    coreArc 5 true (bits G L) source target =
      decide (G.Adj (labelledVertex G L source) (labelledVertex G L target)) := by
  have hA0P : ∀ i : Fin 6, G.Adj (L.a 0).1 (L.p i).1 := by
    intro i
    rw [L.a_zero]
    exact (Finset.mem_filter.mp (L.p i).2).2
  have hP0 : ∀ i : Fin 6, ¬G.Adj (L.p i).1 (L.a 0).1 :=
    fun i => hG.2 (hA0P i)
  have hA0Q : ¬G.Adj (L.a 0).1 q := by
    rw [L.a_zero]
    intro ha1q
    exact (Finset.mem_sdiff.mp hqQ).2
      (Finset.mem_filter.mpr ⟨Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ,
        ha1q⟩)
  have hPR : ∀ i : Fin 6, ∀ r : Fin 3,
      ¬G.Adj (L.p i).1 (L.a ⟨r + 5, by omega⟩).1 :=
    fun i r => RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.P_not_adj_R
      G C _ _ (L.p i).2 (L.a_r r)
  unfold coreArc
  by_cases hsA : source < 8
  · rw [if_pos hsA]
    by_cases htA : target < 8
    · rw [if_pos htA, aArc_coreBits G.Adj L source target hsA htA]
      simp [labelledVertex, hsA, htA]
    · rw [if_neg htA]
      by_cases htP : target < 14
      · rw [if_pos htP]
        unfold aToP
        by_cases hs0 : source = 0
        · subst source
          simp [hA0P, labelledVertex, htA, htP]
        by_cases hsH : source < 5
        · rw [if_neg hs0, if_pos hsH,
            hToP_coreBits G.Adj L (source - 1) (target - 8) (by omega) (by omega)]
          have hfin : (⟨source - 1 + 1, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          simp [labelledVertex, hsA, htA, htP, hfin]
        · rw [if_neg hs0, if_neg hsH,
            rToP_coreBits G.Adj L (source - 5) (target - 8) (by omega) (by omega)]
          have hfin : (⟨source - 5 + 5, by omega⟩ : Fin 8) =
              ⟨source, hsA⟩ := Fin.ext (by simp; omega)
          simp [labelledVertex, hsA, htA, htP, hfin]
      · by_cases htq : target = 14
        · subst target
          simp only [if_neg (by omega : ¬14 < 14), Bool.true_and,
            decide_true, if_true]
          rw [aToQ_coreBits G.Adj L source hsA]
          by_cases hs0 : source = 0
          · subst source
            simp only [labelledVertex, dif_pos (by omega : 0 < 8),
              dif_neg (by omega : ¬14 < 8), dif_neg (by omega : ¬14 < 14),
              dif_pos (by omega : 14 < 19), ne_eq, not_true_eq_false]
            apply (decide_eq_false_iff_not.mpr ?_).symm
            have ha0 : (⟨0, hsA⟩ : Fin 8) = 0 := Fin.ext rfl
            have he0fin : (⟨14 - 14, by omega⟩ : Fin 5) = 0 := rfl
            rw [ha0, he0fin, he0]
            exact hA0Q
          · simp only [labelledVertex, dif_pos hsA,
              dif_neg (by omega : ¬14 < 8), dif_neg (by omega : ¬14 < 14),
              dif_pos (by omega : 14 < 19)]
            rw [show decide (source ≠ 0 ∧
                G.Adj (L.a ⟨source, hsA⟩).1 q) =
                decide (G.Adj (L.a ⟨source, hsA⟩).1 q) by
              exact Bool.decide_congr ⟨And.right, fun h => ⟨hs0, h⟩⟩]
            apply Bool.decide_congr
            have he0fin : (⟨14 - 14, by omega⟩ : Fin 5) = 0 := rfl
            rw [he0fin, he0]
        · have htZ : 14 < target := by omega
          let i : Fin 4 := ⟨target - 15, by omega⟩
          have hefin : (⟨target - 14, by omega⟩ : Fin 5) =
              ⟨i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
          have htail : L.e ⟨target - 14, by omega⟩ ∈ C.Z ∪ {C.s} := by
            rw [hefin]
            exact heZ i
          have hnot : ¬G.Adj (L.a ⟨source, hsA⟩).1
              (L.e ⟨target - 14, by omega⟩) := by
            rcases Finset.mem_union.mp htail with hz | hsroot
            · exact RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A_not_adj_Z
                G C hG (L.a ⟨source, hsA⟩).1
                (L.e ⟨target - 14, by omega⟩) (L.a _).2 hz
            · have heq : L.e ⟨target - 14, by omega⟩ = C.s :=
                Finset.mem_singleton.mp hsroot
              rw [heq]
              exact hG.2 (Finset.mem_filter.mp (L.a _).2).2
          simp only [if_neg htP, Bool.true_and,
            decide_eq_false_iff_not.mpr htq, Bool.not_true,
            Bool.false_and, labelledVertex, dif_pos hsA, dif_neg htA,
            dif_neg htP, dif_pos ht]
          exact (decide_eq_false_iff_not.mpr hnot).symm
  · have hsP : source < 14 := hs
    rw [if_neg hsA, if_pos hsP]
    by_cases htA : target < 8
    · rw [if_pos htA]
      unfold pToA
      by_cases htH : 0 < target ∧ target < 5
      · rw [if_pos (by simpa [Bool.and_eq_true] using htH),
          pToH_coreBits G.Adj L (source - 8) (target - 1) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA,
          show target - 1 + 1 = target by omega]
      · rw [if_neg (by simpa [Bool.and_eq_true] using htH)]
        have hc : target = 0 ∨ target = 5 ∨ target = 6 ∨ target = 7 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · simp [labelledVertex, hsA, hsP, hP0]
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 0
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 1
        · simpa [labelledVertex, hsA, hsP] using hPR ⟨source - 8, by omega⟩ 2
    · rw [if_neg htA]
      by_cases htP : target < 14
      · rw [if_pos htP, pArc_coreBits G.Adj L (source - 8) (target - 8)
          (by omega) (by omega)]
        have himp : G.Adj (L.p ⟨source - 8, by omega⟩).1
            (L.p ⟨target - 8, by omega⟩).1 → source - 8 ≠ target - 8 := by
          intro ha heq
          apply hG.1 (L.p ⟨source - 8, by omega⟩).1
          have hf : (⟨source - 8, by omega⟩ : Fin 6) =
              ⟨target - 8, by omega⟩ := Fin.ext heq
          simpa [hf] using ha
        rw [show decide (source - 8 ≠ target - 8 ∧
            G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) =
            decide (G.Adj (L.p ⟨source - 8, by omega⟩).1
              (L.p ⟨target - 8, by omega⟩).1) by
          exact Bool.decide_congr ⟨And.right, fun h => ⟨himp h, h⟩⟩]
        simp [labelledVertex, hsA, hsP, htA, htP]
      · rw [if_neg htP, if_pos ht,
          pToE_coreBits G.Adj L (source - 8) (target - 14) (by omega) (by omega)]
        simp [labelledVertex, hsA, hsP, htA, htP, ht]

theorem labelledVertex_injective (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e) :
    Function.Injective (fun i : Fin 19 => labelledVertex G L i.val) := by
  have hEMem : ∀ e : Fin 5,
      L.e e = q ∨ L.e e ∈ C.Z ∨ L.e e = C.s := by
    intro e
    by_cases he : e.val = 0
    · left
      have hef : e = 0 := Fin.ext he
      simpa [hef] using he0
    · right
      let i : Fin 4 := ⟨e.val - 1, by omega⟩
      have hef : e = ⟨i.val + 1, by omega⟩ := Fin.ext (by dsimp [i]; omega)
      rw [hef]
      rcases Finset.mem_union.mp (heZ i) with hz | hs
      · exact Or.inl hz
      · exact Or.inr (Finset.mem_singleton.mp hs)
  intro i j hij
  apply Fin.ext
  by_cases hiA : i.val < 8
  · by_cases hjA : j.val < 8
    · have ha : L.a ⟨i.val, hiA⟩ = L.a ⟨j.val, hjA⟩ := by
        apply Subtype.ext
        simpa [labelledVertex, hiA, hjA] using hij
      have hv := Fin.ext_iff.mp (L.a.injective ha)
      change i.val = j.val at hv
      exact hv
    · by_cases hjP : j.val < 14
      · exfalso
        have heq : (L.a ⟨i.val, hiA⟩).1 =
            (L.p ⟨j.val - 8, by omega⟩).1 := by
          simpa [labelledVertex, hiA, hjA, hjP] using hij
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (L.a _).2 (Digraph.LocalConfiguration.P_subset_B (G := G) C
              (heq ▸ (L.p _).2))
      · exfalso
        have heq : (L.a ⟨i.val, hiA⟩).1 = L.e ⟨j.val - 14, by omega⟩ := by
          simpa [labelledVertex, hiA, hjA, hjP, j.isLt] using hij
        rcases hEMem ⟨j.val - 14, by omega⟩ with hq | hz | hsroot
        · rw [hq] at heq
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
              (L.a _).2 (heq ▸ Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
              (Finset.mem_union_left C.B
                (Finset.mem_union_right {C.s} (heq ▸ (L.a _).2)))
        · rw [hsroot] at heq
          exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
            (heq ▸ (L.a _).2)
  · by_cases hiP : i.val < 14
    · by_cases hjA : j.val < 8
      · exfalso
        have heq : (L.p ⟨i.val - 8, by omega⟩).1 =
            (L.a ⟨j.val, hjA⟩).1 := by
          simpa [labelledVertex, hiA, hiP, hjA] using hij
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (heq ▸ (L.a _).2)
            (Digraph.LocalConfiguration.P_subset_B (G := G) C (L.p _).2)
      · by_cases hjP : j.val < 14
        · have hpEq : L.p ⟨i.val - 8, by omega⟩ =
              L.p ⟨j.val - 8, by omega⟩ := by
            apply Subtype.ext
            simpa [labelledVertex, hiA, hiP, hjA, hjP] using hij
          have hv := Fin.ext_iff.mp (L.p.injective hpEq)
          change i.val - 8 = j.val - 8 at hv
          omega
        · exfalso
          have heq : (L.p ⟨i.val - 8, by omega⟩).1 =
              L.e ⟨j.val - 14, by omega⟩ := by
            simpa [labelledVertex, hiA, hiP, hjA, hjP, j.isLt] using hij
          rcases hEMem ⟨j.val - 14, by omega⟩ with hq | hz | hsroot
          · rw [hq] at heq
            exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C))
                (L.p _).2 (heq ▸ hqQ)
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hz
                (heq ▸ (L.p _).2)
          · rw [hsroot] at heq
            exact Digraph.LocalConfiguration.s_notMem_P (G := G) C
              (heq ▸ (L.p _).2)
    · by_cases hjA : j.val < 8
      · exfalso
        have heq : L.e ⟨i.val - 14, by omega⟩ =
            (L.a ⟨j.val, hjA⟩).1 := by
          simpa [labelledVertex, hiA, hiP, i.isLt, hjA] using hij
        rcases hEMem ⟨i.val - 14, by omega⟩ with hq | hz | hsroot
        · rw [hq] at heq
          exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
              (heq ▸ (L.a _).2)
              (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
        · exact (Finset.disjoint_left.mp
            (Digraph.LocalConfiguration.disjoint_Z_known (G := G) C)) hz
              (Finset.mem_union_left C.B
                (Finset.mem_union_right {C.s} (heq ▸ (L.a _).2)))
        · rw [hsroot] at heq
          exact Digraph.LocalConfiguration.s_notMem_A (G := G) C hG.1
            (heq.symm ▸ (L.a _).2)
      · by_cases hjP : j.val < 14
        · exfalso
          have heq : L.e ⟨i.val - 14, by omega⟩ =
              (L.p ⟨j.val - 8, by omega⟩).1 := by
            simpa [labelledVertex, hiA, hiP, i.isLt, hjA, hjP] using hij
          rcases hEMem ⟨i.val - 14, by omega⟩ with hq | hz | hsroot
          · rw [hq] at heq
            exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C))
                (heq ▸ (L.p _).2) hqQ
          · exact (Finset.disjoint_left.mp
              (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hz
                (heq ▸ (L.p _).2)
          · rw [hsroot] at heq
            exact Digraph.LocalConfiguration.s_notMem_P (G := G) C
              (heq.symm ▸ (L.p _).2)
        · have heq : L.e ⟨i.val - 14, by omega⟩ =
              L.e ⟨j.val - 14, by omega⟩ := by
            simpa [labelledVertex, hiA, hiP, i.isLt, hjA, hjP, j.isLt] using hij
          have hv := Fin.ext_iff.mp (heInj heq)
          change i.val - 14 = j.val - 14 at hv
          omega

theorem strictSecondLocal_true_mem (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e)
    (source target : Nat) (hs : source < 14) (ht : target < 19)
    (hSecond : strictSecondLocal 5 true (bits G L) source target = true) :
    labelledVertex G L target ∈
      G.secondOutNeighborFinset (labelledVertex G L source) := by
  simp only [strictSecondLocal, Bool.and_eq_true, decide_eq_true_eq] at hSecond
  rcases hSecond with ⟨⟨hne, hNotArc⟩, hReach⟩
  obtain ⟨middle, hm, hPath⟩ := (any_eq_true_iff 14 _).mp hReach
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPath
  rcases hPath with ⟨⟨⟨_, _⟩, hFirst⟩, hLast⟩
  rw [coreArc_graphBits G C q hqQ L hG he0 heZ source middle hs (by omega)] at hFirst
  rw [coreArc_graphBits G C q hqQ L hG he0 heZ middle target hm ht] at hLast
  rw [coreArc_graphBits G C q hqQ L hG he0 heZ source target hs ht] at hNotArc
  have hne' : target ≠ source := by simpa using hne
  have hVertexNe : labelledVertex G L target ≠ labelledVertex G L source := by
    intro heq
    have hFin : (⟨target, ht⟩ : Fin 19) = ⟨source, by omega⟩ := by
      apply labelledVertex_injective G C q hqQ L hG he0 heZ heInj
      simpa using heq
    exact hne' (by simpa using congrArg Fin.val hFin)
  rw [Digraph.mem_secondOutNeighborFinset, Digraph.mem_secondOutNeighborSet]
  exact ⟨⟨_, of_decide_eq_true hFirst, of_decide_eq_true hLast⟩,
    by simpa using hNotArc, hVertexNe⟩

omit [Fintype V] [DecidableEq V] in
private theorem count_le_card_of_injective {n : Nat} (f : Nat → Bool)
    (label : Fin n → V) (S : Finset V) (hn : n < 256)
    (hinj : Function.Injective label)
    (hmem : ∀ i : Fin n, f i = true → label i ∈ S) :
    (count n f).toNat ≤ S.card := by
  classical
  let selected : Finset (Fin n) := Finset.univ.filter fun i => f i = true
  have hCard : selected.card = (count n f).toNat := by
    rw [toNat_count_eq_fin_sum n f hn]
    simp only [selected, Finset.card_filter]
  have hImageCard : (selected.image label).card = selected.card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hinj hab
  have hSubset : selected.image label ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact hmem i (Finset.mem_filter.mp hi).2
  rw [← hCard, ← hImageCard]
  exact Finset.card_le_card hSubset

theorem localSecondCount_le_graph (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e)
    (source : Nat) (hs : source < 14) :
    (localSecondCount 5 true (bits G L) source).toNat ≤
      G.secondOutdegree (labelledVertex G L source) := by
  change (count 19 (strictSecondLocal 5 true (bits G L) source)).toNat ≤ _
  unfold Digraph.secondOutdegree
  apply count_le_card_of_injective
    (label := fun i : Fin 19 => labelledVertex G L i.val)
    (hn := by omega)
    (hinj := labelledVertex_injective G C q hqQ L hG he0 heZ heInj)
  intro i hi
  exact strictSecondLocal_true_mem G C q hqQ L hG he0 heZ heInj
    source i.val hs i.isLt hi

theorem localSecondCount_lt_outdegree (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (L : ReachedLabels G C q) (hG : G.IsOriented)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e) (hNoSeymour : ¬G.HasSeymourVertex)
    (source : Nat) (hs : source < 14) :
    (localSecondCount 5 true (bits G L) source).toNat <
      G.outdegree (labelledVertex G L source) :=
  (localSecondCount_le_graph G C q hqQ L hG he0 heZ heInj source hs).trans_lt
    (Digraph.secondOutdegree_lt_outdegree_of_not_seymour G
      (fun h => hNoSeymour ⟨labelledVertex G L source, h⟩))

theorem fixedA_graphBits_true (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (_hG : G.IsOriented) :
    fixedA (bits G L) = true := by
  let b := bits G L
  have h01 : aArc b 0 1 = true := by
    rw [aArc_coreBits G.Adj L 0 1 (by omega) (by omega)]
    exact decide_eq_true (by
      rw [show (⟨0, by omega⟩ : Fin 8) = 0 by rfl, L.a_zero]
      simpa using (Finset.mem_filter.mp (L.a_aOne 0)).2)
  have h02 : aArc b 0 2 = true := by
    rw [aArc_coreBits G.Adj L 0 2 (by omega) (by omega)]
    exact decide_eq_true (by
      rw [show (⟨0, by omega⟩ : Fin 8) = 0 by rfl, L.a_zero]
      simpa using (Finset.mem_filter.mp (L.a_aOne 1)).2)
  have hTail : all 5 (fun i => !aArc b 0 (3 + i)) = true := by
    rw [all_eq_true_iff]
    intro i hi
    rw [aArc_coreBits G.Adj L 0 (3 + i) (by omega) (by omega)]
    rw [show (⟨0, by omega⟩ : Fin 8) = 0 by rfl, L.a_zero]
    by_cases hi2 : i < 2
    · have hx := L.a_x ⟨i, hi2⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A1_X (G := G) C))
            (Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩)
            (by simpa [Nat.add_comm] using hx)
      simp [hn]
    · have hr := L.a_r ⟨i - 2, by omega⟩
      have hn : ¬G.Adj C.a1 (L.a ⟨3 + i, by omega⟩).1 := by
        intro ha
        have hA1 : (L.a ⟨3 + i, by omega⟩).1 ∈ C.A1 :=
          Finset.mem_filter.mpr ⟨(L.a _).2, ha⟩
        have heq : (⟨i - 2 + 5, by omega⟩ : Fin 8) =
            ⟨3 + i, by omega⟩ := Fin.ext (by simp; omega)
        rw [heq] at hr
        exact (Finset.mem_sdiff.mp hr).2
          (Finset.mem_union_left {C.a1} (Finset.mem_union_left C.X hA1))
      simp [hn]
  have hA1R : all 6 (fun k =>
      !aArc b (1 + k / 3) (5 + k % 3)) = true := by
    rw [all_eq_true_iff]
    intro k hk
    rw [aArc_coreBits G.Adj L (1 + k / 3) (5 + k % 3)
      (by omega) (by omega)]
    have hn := RSeven.XFourNoRoot.RepeatedSharedOmissionBridge.A1_not_adj_R
      G C (L.a ⟨1 + k / 3, by omega⟩).1 (L.a ⟨5 + k % 3, by omega⟩).1
      (by
        have heq : (⟨k / 3 + 1, by omega⟩ : Fin 8) =
            ⟨1 + k / 3, by omega⟩ := Fin.ext (by simp; omega)
        rw [← heq]
        exact L.a_aOne ⟨k / 3, by omega⟩)
      (by
        have heq : (⟨k % 3 + 5, by omega⟩ : Fin 8) =
            ⟨5 + k % 3, by omega⟩ := Fin.ext (by simp; omega)
        rw [← heq]
        exact L.a_r ⟨k % 3, by omega⟩)
    exact by simpa using decide_eq_false hn
  simp only [fixedA, Bool.and_eq_true]
  exact ⟨⟨⟨h01, h02⟩, hTail⟩, hA1R⟩

theorem structural_no_arcs_graphBits (C : G.LocalConfiguration) (q : V)
    (L : ReachedLabels G C q) (hG : G.IsOriented) :
    (∀ a, a < 2 → aArc (bits G L) (1 + a) 0 = false) ∧
      (∀ h, h < 4 → hArc (bits G L) h h = false) := by
  constructor
  · intro a ha
    rw [aArc_coreBits G.Adj L (1 + a) 0 (by omega) (by omega)]
    apply decide_eq_false
    intro hadj
    have huA1 := L.a_aOne ⟨a, ha⟩
    have hzero := BSixKTwoCoreGraphBridge.directCount_protected_eq_zero_of_mem_A1
      G C hG (L.a ⟨a + 1, by omega⟩).1 huA1
    have hmem : C.a1 ∈ BSixKTwoCoreGraphBridge.protectedTargets G C := by
      simp [BSixKTwoCoreGraphBridge.protectedTargets]
    have hpos : 0 < Shared.directCount G
        (BSixKTwoCoreGraphBridge.protectedTargets G C) (L.a ⟨a + 1, by omega⟩).1 := by
      unfold Shared.directCount internalFirstNeighbors
      apply Finset.card_pos.mpr
      refine ⟨C.a1, Finset.mem_filter.mpr ⟨hmem, ?_⟩⟩
      have hs : (⟨1 + a, by omega⟩ : Fin 8) = ⟨a + 1, by omega⟩ :=
        Fin.ext (Nat.add_comm 1 a)
      simpa [L.a_zero, hs] using hadj
    omega
  · intro h hh
    rw [hArc, aArc_coreBits G.Adj L (1 + h) (1 + h) (by omega) (by omega)]
    simpa using decide_eq_false (hG.1 (L.a ⟨1 + h, by omega⟩).1)

theorem pDirectCore_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hNoRoot : epsilonS G C = 0) (E : Finset V) (hE : E = {q} ∪ C.Z)
    (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (p : Nat) (hp : p < 6) :
    (pOut (bits G L) p + pHOut (bits G L) p + pEOut 5 (bits G L) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hBlocks := GraphBridge.pBlockCounts G C q L hG hHCard E eEq
    (by omega) hELab p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hCaptured : G.outNeighborFinset v ⊆ C.P ∪ C.H ∪ E := by
    intro w hw
    have hc := BSixKThree.P_outgoingCaptured_general G C hG v hvP hw
    simp only [Finset.mem_union] at hc ⊢
    rcases hc with (((hwH | hwP) | hwQ) | hwExt)
    · exact Or.inl (Or.inr hwH)
    · exact Or.inl (Or.inl hwP)
    · have hwq : w = q := by simpa [hQ] using hwQ
      subst w
      exact Or.inr (by rw [hE]; exact Finset.mem_union_left C.Z (by simp))
    · exact Or.inr (by rw [hE]; exact Finset.mem_union_right {q} (hExt ▸ hwExt))
  have hPH : Disjoint C.P C.H :=
    (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [hE, Finset.disjoint_left]
    intro w hwPH hwE
    rcases Finset.mem_union.mp hwPH with hwP | hwH
    · rcases Finset.mem_union.mp hwE with hwq | hwZ
      · have hwEq : w = q := Finset.mem_singleton.mp hwq
        subst w
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
    · rcases Finset.mem_union.mp hwE with hwq | hwZ
      · have hwEq : w = q := Finset.mem_singleton.mp hwq
        subst w
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hwZ hwH
  have hDegree := outdegree_eq_directCount_of_captured G
    (C.P ∪ C.H ∪ E) v hCaptured
  rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
    directCount_union_of_disjoint G C.P C.H v hPH] at hDegree
  simp only [BitVec.toNat_add]
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  have hSmall : Shared.directCount G C.P v + Shared.directCount G C.H v +
      Shared.directCount G E v < 256 := by
    have h1 := Finset.card_le_card (Finset.filter_subset (G.Adj v) C.P)
    have h2 := Finset.card_le_card (Finset.filter_subset (G.Adj v) C.H)
    have h3 := Finset.card_le_card (Finset.filter_subset (G.Adj v) E)
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have hECard : E.card = 5 := by simpa using (Fintype.card_congr eEq).symm
    change Shared.directCount G C.P v ≤ C.P.card at h1
    change Shared.directCount G C.H v ≤ C.H.card at h2
    change Shared.directCount G E v ≤ E.card at h3
    rw [hpCard] at h1
    rw [hHCard] at h2
    rw [hECard] at h3
    omega
  have hSmallPH : Shared.directCount G C.P v + Shared.directCount G C.H v < 256 := by
    omega
  rw [Nat.mod_eq_of_lt hSmallPH, Nat.mod_eq_of_lt hSmall]
  exact hDegree.symm

theorem pDirectFour_toNat (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hHCard : C.H.card = 4)
    (hNoRoot : epsilonS G C = 0) (E : Finset V) (hE : E = {q} ∪ C.Z)
    (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (p : Nat) (hp : p < 6) :
    (pOut (bits G L) p + pHOut (bits G L) p + pEOut 4 (bits G L) p).toNat =
      G.outdegree (L.p ⟨p, hp⟩).1 := by
  have hBlocks := GraphBridge.pBlockCounts G C q L hG hHCard E eEq
    (by omega) hELab p hp
  let v := (L.p ⟨p, hp⟩).1
  have hvP : v ∈ C.P := (L.p ⟨p, hp⟩).2
  have hRootEmpty : rootSecondFinset G C = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [epsilonS] using hNoRoot
  have hExt : externalTargets G C = C.Z := by
    simp [externalTargets, hRootEmpty]
  have hCaptured : G.outNeighborFinset v ⊆ C.P ∪ C.H ∪ E := by
    intro w hw
    have hc := BSixKThree.P_outgoingCaptured_general G C hG v hvP hw
    simp only [Finset.mem_union] at hc ⊢
    rcases hc with (((hwH | hwP) | hwQ) | hwExt)
    · exact Or.inl (Or.inr hwH)
    · exact Or.inl (Or.inl hwP)
    · have hwq : w = q := by simpa [hQ] using hwQ
      subst w
      exact Or.inr (by rw [hE]; exact Finset.mem_union_left C.Z (by simp))
    · exact Or.inr (by rw [hE]; exact Finset.mem_union_right {q} (hExt ▸ hwExt))
  have hPH : Disjoint C.P C.H :=
    (Digraph.LocalConfiguration.disjoint_H_P (G := G) C).symm
  have hPHE : Disjoint (C.P ∪ C.H) E := by
    rw [hE, Finset.disjoint_left]
    intro w hwPH hwE
    rcases Finset.mem_union.mp hwPH with hwP | hwH
    · rcases Finset.mem_union.mp hwE with hwq | hwZ
      · have hwEq : w = q := Finset.mem_singleton.mp hwq
        subst w
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_P_Q (G := G) C)) hwP hqQ
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_P (G := G) C)) hwZ hwP
    · rcases Finset.mem_union.mp hwE with hwq | hwZ
      · have hwEq : w = q := Finset.mem_singleton.mp hwq
        subst w
        exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_A_B (G := G) C))
            (Digraph.LocalConfiguration.H_subset_A (G := G) C hwH)
            (Digraph.LocalConfiguration.Q_subset_B (G := G) C hqQ)
      · exact (Finset.disjoint_left.mp
          (Digraph.LocalConfiguration.disjoint_Z_H (G := G) C)) hwZ hwH
  have hDegree := outdegree_eq_directCount_of_captured G
    (C.P ∪ C.H ∪ E) v hCaptured
  rw [directCount_union_of_disjoint G (C.P ∪ C.H) E v hPHE,
    directCount_union_of_disjoint G C.P C.H v hPH] at hDegree
  simp only [BitVec.toNat_add]
  rw [hBlocks.1, hBlocks.2.1, hBlocks.2.2]
  have hSmall : Shared.directCount G C.P v + Shared.directCount G C.H v +
      Shared.directCount G E v < 256 := by
    have h1 := Finset.card_le_card (Finset.filter_subset (G.Adj v) C.P)
    have h2 := Finset.card_le_card (Finset.filter_subset (G.Adj v) C.H)
    have h3 := Finset.card_le_card (Finset.filter_subset (G.Adj v) E)
    have hpCard : C.P.card = 6 := by simpa using (Fintype.card_congr L.p).symm
    have hECard : E.card = 4 := by simpa using (Fintype.card_congr eEq).symm
    change Shared.directCount G C.P v ≤ C.P.card at h1
    change Shared.directCount G C.H v ≤ C.H.card at h2
    change Shared.directCount G E v ≤ E.card at h3
    rw [hpCard] at h1
    rw [hHCard] at h2
    rw [hECard] at h3
    omega
  have hSmallPH : Shared.directCount G C.P v + Shared.directCount G C.H v < 256 := by
    omega
  rw [Nat.mod_eq_of_lt hSmallPH, Nat.mod_eq_of_lt hSmall]
  exact hDegree.symm


theorem all_hRestrictedNonSeymourCore_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e) (c : Nat) :
    all 4 (hRestrictedNonSeymourCore c (bits G L)) = true := by
  have hFixed := fixedA_graphBits_true G C q L hG
  have hStruct := structural_no_arcs_graphBits G C q L hG
  rw [all_eq_true_iff]
  intro h hh
  simp only [hRestrictedNonSeymourCore, BitVec.ult_eq_decide,
    decide_eq_true_eq]
  have hSubset := hRestrictedSecondCountCore_le_local c (bits G L) h hh
    hFixed hStruct.1 hStruct.2
  have hLocal := localSecondCount_lt_outdegree G C q hqQ L hG he0 heZ heInj
    hNoSeymour (1 + h) (by omega)
  have hLabel : labelledVertex G L (1 + h) = (L.a ⟨h + 1, by omega⟩).1 := by
    simp [labelledVertex, show 1 + h < 8 by omega]
    omega
  rw [hLabel] at hLocal
  have hDirect := GraphBridge.hDirectCore_toNat G C q hqQ hQ L hG hHCard
    hRCard h hh
  change (hRestrictedSecondCountCore c (bits G L) h).toNat <
    (hDirectCore c (bits G L) h).toNat
  have hc : hDirectCore c (bits G L) h = hDirectCore 0 (bits G L) h := rfl
  rw [hc, hDirect]
  exact hSubset.trans_lt hLocal

theorem all_hRestrictedNonSeymourFour_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4) (hRCard : C.R.card = 3)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e) (c : Nat) :
    all 4 (hRestrictedNonSeymourFour c (bits G L)) = true := by
  have hFixed := fixedA_graphBits_true G C q L hG
  have hStruct := structural_no_arcs_graphBits G C q L hG
  rw [all_eq_true_iff]
  intro h hh
  simp only [hRestrictedNonSeymourFour, BitVec.ult_eq_decide,
    decide_eq_true_eq]
  have hFourCore := hRestrictedSecondCountFour_le_core c (bits G L) h
  have hSubset := hRestrictedSecondCountCore_le_local c (bits G L) h hh
    hFixed hStruct.1 hStruct.2
  have hLocal := localSecondCount_lt_outdegree G C q hqQ L hG he0 heZ heInj
    hNoSeymour (1 + h) (by omega)
  have hLabel : labelledVertex G L (1 + h) = (L.a ⟨h + 1, by omega⟩).1 := by
    simp [labelledVertex, show 1 + h < 8 by omega]
    omega
  rw [hLabel] at hLocal
  have hDirect := GraphBridge.hDirectCore_toNat G C q hqQ hQ L hG hHCard
    hRCard h hh
  change (hRestrictedSecondCountFour c (bits G L) h).toNat <
    (hDirectCore c (bits G L) h).toNat
  have hc : hDirectCore c (bits G L) h = hDirectCore 0 (bits G L) h := rfl
  rw [hc, hDirect]
  exact (hFourCore.trans hSubset).trans_lt hLocal

theorem all_pMicroNonSeymourCore_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4) (hNoRoot : epsilonS G C = 0)
    (E : Finset V) (hE : E = {q} ∪ C.Z) (eEq : Fin 5 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 5, L.e i = (eEq i).1)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (c : Nat) : all 6 (pMicroNonSeymourCore c (bits G L)) = true := by
  have heInj : Function.Injective L.e := by
    intro i j hij
    apply eEq.injective
    apply Subtype.ext
    simpa [hELab] using hij
  have hNoHLoop := (structural_no_arcs_graphBits G C q L hG).2
  rw [all_eq_true_iff]
  intro p hp
  simp only [pMicroNonSeymourCore, BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSubset := pMicroSecondCountCore_le_local c (bits G L) p hp hNoHLoop
  have hLocal := localSecondCount_lt_outdegree G C q hqQ L hG he0 heZ heInj
    hNoSeymour (8 + p) (by omega)
  have hLabel : labelledVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega]
  rw [hLabel] at hLocal
  rw [pDirectCore_toNat G C q hqQ hQ L hG hHCard hNoRoot E hE eEq hELab p hp]
  exact hSubset.trans_lt hLocal

theorem all_pMicroNonSeymourFour_true (C : G.LocalConfiguration) (q : V)
    (hqQ : q ∈ C.Q) (hQ : C.Q = {q}) (L : ReachedLabels G C q)
    (hG : G.IsOriented) (hNoSeymour : ¬G.HasSeymourVertex)
    (hHCard : C.H.card = 4) (hNoRoot : epsilonS G C = 0)
    (E : Finset V) (hE : E = {q} ∪ C.Z) (eEq : Fin 4 ≃ {v : V // v ∈ E})
    (hELab : ∀ i : Fin 4, L.e ⟨i.val, by omega⟩ = (eEq i).1)
    (he0 : L.e 0 = q)
    (heZ : ∀ i : Fin 4, L.e ⟨i.val + 1, by omega⟩ ∈ C.Z ∪ {C.s})
    (heInj : Function.Injective L.e) (c : Nat) :
    all 6 (pMicroNonSeymourFour c (bits G L)) = true := by
  have hNoHLoop := (structural_no_arcs_graphBits G C q L hG).2
  rw [all_eq_true_iff]
  intro p hp
  simp only [pMicroNonSeymourFour, BitVec.ult_eq_decide, decide_eq_true_eq]
  have hSubset := pMicroSecondCountCore_le_local c (bits G L) p hp hNoHLoop
  have hLocal := localSecondCount_lt_outdegree G C q hqQ L hG he0 heZ heInj
    hNoSeymour (8 + p) (by omega)
  have hLabel : labelledVertex G L (8 + p) = (L.p ⟨p, hp⟩).1 := by
    simp [labelledVertex, show ¬8 + p < 8 by omega,
      show 8 + p < 14 by omega]
  rw [hLabel] at hLocal
  rw [pDirectFour_toNat G C q hqQ hQ L hG hHCard hNoRoot E hE eEq
    hELab p hp]
  exact hSubset.trans_lt hLocal

end SeymourEight.BSevenKTwo.RSix.XTwoNoRoot.MicroScratch
