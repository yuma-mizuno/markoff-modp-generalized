import GenMarkoff.General.Cage.ConnectingGoodPowerCover
import GenMarkoff.General.Cage.DirectedConnectingFiber
import GenMarkoff.General.Cage.IncidenceAlgebra

/-!
# Turning a three-root witness into a full-Vieta relay

The three equations counted by the connecting cover retain enough data to
construct two actual points of the fixed generalized surface.  They lie on
the prescribed first-axis fibers and share the middle second-axis fiber.
When all three fibers are primitive and connecting, the local fiber
theorems concatenate to a full-Vieta path.

This is a pointwise assembly lemma.  It makes no counting or existence
claim; those are supplied separately by the power-cover estimate and the
primitive-order sieve.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly

universe u

noncomputable section

/-- A nonzero square root of a nonsquare multiple of a centered norm forces
that centered norm itself to be a nonsquare. -/
theorem centeredNorm_not_isSquare_of_goodThreeRootWitness
    {p : ℕ} [Fact p.Prime]
    {a : Coefficients (ZMod p)} {xi eta omegaInv : ZMod p}
    (homegaInv : ¬ IsSquare omegaInv)
    (w : ConnectingGoodThreeRootWitness a xi eta omegaInv) :
    ¬ IsSquare (centeredNorm a.a3 a.a1 w.1.middle) := by
  have homegaInvZero : omegaInv ≠ 0 := by
    intro hzero
    apply homegaInv
    rw [hzero]
    exact IsSquare.zero
  have hnormZero :
      centeredNorm a.a3 a.a1 w.1.middle ≠ 0 := by
    intro hzero
    have hrootZero : w.1.thirdRoot ^ 2 = 0 := by
      rw [w.1.thirdEquation, hzero, mul_zero]
    exact w.2 (sq_eq_zero_iff.mp hrootZero)
  intro hnormSquare
  apply homegaInv
  have hrootSquare : IsSquare (w.1.thirdRoot ^ 2) := by
    exact ⟨w.1.thirdRoot, by ring⟩
  have hquotient :
      IsSquare
        (w.1.thirdRoot ^ 2 /
          centeredNorm a.a3 a.a1 w.1.middle) :=
    hrootSquare.div hnormSquare
  rw [w.1.thirdEquation] at hquotient
  simpa [hnormZero] using hquotient

/-- A good three-root witness with a primitive candidate-regular middle
trace joins two primitive connecting first-axis fibers.

The incidence roots are first converted to points of the unequal trace
cubic and then pulled back by the fixed coefficient-ordered affine trace
change.  No coordinate permutation is used. -/
theorem sameVietaComponent_of_connectingThreeRootWitness
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (x y : SolutionSurface a)
    (xi eta omegaInv : ZMod p)
    (htraceX : traceAt a .first x.1 = xi)
    (htraceY : traceAt a .first y.1 = eta)
    (qx qy qm : (ZMod p)ˣ)
    (heigenX : xi = splitTorusTrace qx)
    (heigenY : eta = splitTorusTrace qy)
    (hprimitiveX : orderOf qx = Nat.card (ZMod p)ˣ)
    (hprimitiveY : orderOf qy = Nat.card (ZMod p)ˣ)
    (hregularX :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hregularY :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hconnectingX : ¬ IsSquare (centeredNorm a.a2 a.a3 xi))
    (hconnectingY : ¬ IsSquare (centeredNorm a.a2 a.a3 eta))
    (homegaInv : ¬ IsSquare omegaInv)
    (w : ConnectingGoodThreeRootWitness a xi eta omegaInv)
    (heigenMiddle : w.1.middle = splitTorusTrace qm)
    (hprimitiveMiddle : orderOf qm = Nat.card (ZMod p)ˣ)
    (hregularMiddle :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1 w.1.middle) :
    SameVietaComponent x y := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact two_ne_zero_zmod
      (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hpTwo))
  let incidence : IncidenceEquationWitness a xi eta :=
    { middle := w.1.middle
      firstRoot := w.1.firstRoot
      secondRoot := w.1.secondRoot
      firstEquation := w.1.firstEquation
      secondEquation := w.1.secondEquation }
  let firstPoint : SolutionSurface a :=
    ⟨inverseTracePoint a incidence.firstTracePoint,
      incidence.firstPoint_isSolution htwo hmultiplier⟩
  let secondPoint : SolutionSurface a :=
    ⟨inverseTracePoint a incidence.secondTracePoint,
      incidence.secondPoint_isSolution htwo hmultiplier⟩
  have hfirstTrace :
      traceAt a .first firstPoint.1 = xi := by
    change (tracePoint a firstPoint.1).x1 = xi
    rw [tracePoint_inverseTracePoint a incidence.firstTracePoint hmultiplier]
    rfl
  have hsecondTrace :
      traceAt a .first secondPoint.1 = eta := by
    change (tracePoint a secondPoint.1).x1 = eta
    rw [tracePoint_inverseTracePoint a incidence.secondTracePoint hmultiplier]
    rfl
  have hfirstMiddle :
      traceAt a .second firstPoint.1 = w.1.middle := by
    change (tracePoint a firstPoint.1).x2 = w.1.middle
    rw [tracePoint_inverseTracePoint a incidence.firstTracePoint hmultiplier]
    rfl
  have hsecondMiddle :
      traceAt a .second secondPoint.1 = w.1.middle := by
    change (tracePoint a secondPoint.1).x2 = w.1.middle
    rw [tracePoint_inverseTracePoint a incidence.secondTracePoint hmultiplier]
    rfl
  have hsameFirstX : x.1.x1 = firstPoint.1.x1 := by
    have htrace :
        a.multiplier * x.1.x1 - a.a1 =
          a.multiplier * firstPoint.1.x1 - a.a1 := by
      simpa [traceAt_first] using htraceX.trans hfirstTrace.symm
    apply (mul_left_cancel₀ hmultiplier)
    linear_combination htrace
  have hsameFirstY : y.1.x1 = secondPoint.1.x1 := by
    have htrace :
        a.multiplier * y.1.x1 - a.a1 =
          a.multiplier * secondPoint.1.x1 - a.a1 := by
      simpa [traceAt_first] using htraceY.trans hsecondTrace.symm
    apply (mul_left_cancel₀ hmultiplier)
    linear_combination htrace
  have hsameMiddle :
      firstPoint.1.x2 = secondPoint.1.x2 := by
    have htrace :
        a.multiplier * firstPoint.1.x2 - a.a2 =
          a.multiplier * secondPoint.1.x2 - a.a2 := by
      simpa [traceAt_second] using hfirstMiddle.trans hsecondMiddle.symm
    apply (mul_left_cancel₀ hmultiplier)
    linear_combination htrace
  have hxFirst :
      SameVietaComponent x firstPoint := by
    apply
      sameVietaComponent_of_same_firstCoordinate_of_primitiveConnecting
        p hpTwo a x firstPoint hsameFirstX qx
    · exact htraceX.trans heigenX
    · exact hprimitiveX
    · simpa [htraceX] using hregularX
    · simpa [htraceX] using hconnectingX
  have hySecond :
      SameVietaComponent y secondPoint := by
    apply
      sameVietaComponent_of_same_firstCoordinate_of_primitiveConnecting
        p hpTwo a y secondPoint hsameFirstY qy
    · exact htraceY.trans heigenY
    · exact hprimitiveY
    · simpa [htraceY] using hregularY
    · simpa [htraceY] using hconnectingY
  have hmiddleConnecting :
      ¬ IsSquare (centeredNorm a.a3 a.a1 w.1.middle) :=
    centeredNorm_not_isSquare_of_goodThreeRootWitness
      homegaInv w
  have hfirstSecond :
      SameVietaComponent firstPoint secondPoint := by
    apply
      sameVietaComponent_of_same_secondCoordinate_of_primitiveConnecting
        p hpTwo a firstPoint secondPoint hsameMiddle qm
    · exact hfirstMiddle.trans heigenMiddle
    · exact hprimitiveMiddle
    · simpa [hfirstMiddle] using hregularMiddle
    · simpa [hfirstMiddle] using hmiddleConnecting
  exact
    sameVietaComponent_trans hxFirst
      (sameVietaComponent_trans hfirstSecond
        (sameVietaComponent_symm hySecond))

end

end GenMarkoff.General.Cage
