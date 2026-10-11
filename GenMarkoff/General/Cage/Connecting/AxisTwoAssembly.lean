module

public import GenMarkoff.General.Cage.Connecting.DirectedRelay
public import GenMarkoff.General.Cage.Connecting.PrimitiveWitness
public import BGS.NumberTheory.ExplicitDivisorBound
public import BGS.Markoff.Endgame.PrimitiveInclusionExclusion
public import GenMarkoff.General.Arithmetic.ReasonableCutoff

@[expose] public section

/-!
# Assembly of the directed second-axis connecting relay

This file defines the second-axis endpoint predicates
(`IsPrimitiveRegularConnectingAxisTwo` and its two refinements) and proves
that, for `p ≥ reasonableAnalyticCutoff`, two such endpoints whose traces form
a connecting incidence pair lie in one full-Vieta component.  The good
three-root witness comes from
`exists_primitive_candidateRegular_connectingGoodThreeRootWitness_of_explicitInequality`
and is turned into a Vieta path by
`sameVietaComponent_of_connectingSecondAxisThreeRootWitness`.  The
coefficient order is the simultaneous left cycle `(a₂,a₃,a₁)`, so a
second-axis outer fiber is connected through the third axis of the original
fixed surface.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly

noncomputable section

/-- The connecting-incidence predicate is symmetric in its two outer
labels. -/
theorem IsConnectingIncidencePair.symm
    {K : Type*} [Field K]
    {a : Coefficients K} {xi eta : K}
    (h : IsConnectingIncidencePair a xi eta) :
    IsConnectingIncidencePair a eta xi := by
  refine ⟨⟨h.1.1.symm, ?_⟩, h.2.2, h.2.1⟩
  rw [incidencePairObstruction_comm]
  exact h.1.2

/-- A point lies on a primitive, candidate-regular, connecting second-axis
split fiber. -/
def IsPrimitiveRegularConnectingAxisTwo
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  ∃ q : (ZMod p)ˣ,
    traceAt a .second x.1 = splitTorusTrace q ∧
      orderOf q = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a2 a.a3 a.a1 (traceAt a .second x.1) ∧
          ¬ IsSquare
            (centeredNorm a.a3 a.a1
              (traceAt a .second x.1))

/-- A normalized second-axis endpoint with the extra branch-separation
condition required when it is used as a prescribed reference label. -/
def IsObstructionReadyPrimitiveRegularConnectingAxisTwo
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  IsPrimitiveRegularConnectingAxisTwo p a x ∧
    incidenceCenteredNormObstruction
      (directedCycleLeftCoefficients a)
        (traceAt a .second x.1) ≠ 0

/-- A normalized second-axis endpoint whose trace forms the full
branch-separated connecting pair with a prescribed reference trace. -/
def IsConnectingPairPrimitiveRegularConnectingAxisTwo
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (eta : ZMod p)
    (x : SolutionSurface a) : Prop :=
  IsPrimitiveRegularConnectingAxisTwo p a x ∧
    IsConnectingIncidencePair
      (directedCycleLeftCoefficients a)
        (traceAt a .second x.1) eta

/-- For `p ≥ reasonableAnalyticCutoff`, two points on primitive,
candidate-regular, connecting second-axis fibers whose traces form a
connecting incidence pair in the left-cycled frame lie in the same full-Vieta
component. -/
theorem sameVietaComponent_of_primitiveRegularConnectingAxisTwo_of_reasonableCutoff
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4) (hmoving : (a.a1, a.a2) ≠ (0, 0))
    (x y : SolutionSurface a)
    (hx : IsPrimitiveRegularConnectingAxisTwo p a x)
    (hy : IsPrimitiveRegularConnectingAxisTwo p a y)
    (hpair :
      IsConnectingIncidencePair
        (directedCycleLeftCoefficients a)
        (traceAt a .second x.1)
        (traceAt a .second y.1)) :
    SameVietaComponent x y := by
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
  have hpTwo : p ≠ 2 := by omega
  obtain ⟨qx, hxTrace, hxOrder, hxRegular, hxConnecting⟩ := hx
  obtain ⟨qy, hyTrace, hyOrder, hyRegular, hyConnecting⟩ := hy
  -- Fix a nonsquare scalar and restate the hypotheses in the left-cycled
  -- coefficient frame.
  have hchar : ringChar (ZMod p) ≠ 2 :=
    (ZMod.ringChar_zmod_n p).substr hpTwo
  obtain ⟨omegaInv, homegaInv⟩ :=
    FiniteField.exists_nonsquare hchar
  have hA1' :
      (directedCycleLeftCoefficients a).a1 ^ 2 ≠ 4 := by
    simpa [directedCycleLeftCoefficients] using hA2
  have hA2' :
      (directedCycleLeftCoefficients a).a2 ^ 2 ≠ 4 := by
    simpa [directedCycleLeftCoefficients] using hA3
  have hA3' :
      (directedCycleLeftCoefficients a).a3 ^ 2 ≠ 4 := by
    simpa [directedCycleLeftCoefficients] using hA1
  have hmoving' :
      ((directedCycleLeftCoefficients a).a3,
          (directedCycleLeftCoefficients a).a1) ≠ (0, 0) := by
    simpa [directedCycleLeftCoefficients] using hmoving
  have hxRegular' :
      OrderedTraceCandidateRegular
        (directedCycleLeftCoefficients a).a1
        (directedCycleLeftCoefficients a).a2
        (directedCycleLeftCoefficients a).a3
        (traceAt a .second x.1) := by
    simpa [directedCycleLeftCoefficients] using hxRegular
  have hyRegular' :
      OrderedTraceCandidateRegular
        (directedCycleLeftCoefficients a).a1
        (directedCycleLeftCoefficients a).a2
        (directedCycleLeftCoefficients a).a3
        (traceAt a .second y.1) := by
    simpa [directedCycleLeftCoefficients] using hyRegular
  -- The explicit inequality at the cutoff yields a good three-root witness
  -- with primitive candidate-regular middle trace.
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_one
      hp (coefficient := 952) (by norm_num)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  obtain ⟨qm, w, hmTrace, hmOrder, hmRegular⟩ :=
    exists_primitive_candidateRegular_connectingGoodThreeRootWitness_of_explicitInequality
      p hpFive (directedCycleLeftCoefficients a)
      (traceAt a .second x.1) (traceAt a .second y.1) omegaInv
      hA1' hA2' hA3' hmoving' hxRegular' hyRegular' hpair homegaInv
      (by rw [hcard]; simpa using hexplicit)
  -- Feed the witness into the directed relay.
  apply
    sameVietaComponent_of_connectingSecondAxisThreeRootWitness
      p hpTwo a hmultiplier x y
      (traceAt a .second x.1) (traceAt a .second y.1)
      omegaInv rfl rfl qx qy qm hxTrace hyTrace
      hxOrder hyOrder hxRegular hyRegular
      hxConnecting hyConnecting homegaInv w hmTrace
  · exact hmOrder.trans hcard.symm
  · simpa [directedCycleLeftCoefficients] using hmRegular

end

end GenMarkoff.General.Cage
