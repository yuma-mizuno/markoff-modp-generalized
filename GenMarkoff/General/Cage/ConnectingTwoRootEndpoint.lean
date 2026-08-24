import GenMarkoff.General.Cage.ConnectingFiber
import GenMarkoff.General.Cage.IncidenceGeometry

/-!
# Pointwise reconstruction from a two-root connecting witness

The nonsquare canonical endpoint needs only one incidence root: it constructs
an actual point with the same first trace and the prescribed middle second
trace.  The primitive connecting theorem on the original first-axis fiber
then joins that point to the endpoint.

This is essentially new relative to the classical `c = 0` argument.  The
second square root is retained because its nonvanishing and nonsquare scale
certify that the newly reached second-axis fiber is connecting.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly

noncomputable section

/-- A nonzero square root of a nonsquare multiple of the target centered norm
forces the target centered norm to be a nonsquare. -/
theorem centeredNorm_not_isSquare_of_twoRootData
    {p : ℕ} [Fact p.Prime]
    {a : Coefficients (ZMod p)}
    {omegaInv middle secondRoot : ZMod p}
    (homegaInv : ¬ IsSquare omegaInv)
    (hsecondEquation :
      secondRoot ^ 2 =
        omegaInv * centeredNorm a.a3 a.a1 middle)
    (hsecondRoot : secondRoot ≠ 0) :
    ¬ IsSquare (centeredNorm a.a3 a.a1 middle) := by
  have homegaInvZero : omegaInv ≠ 0 := by
    intro hzero
    apply homegaInv
    rw [hzero]
    exact IsSquare.zero
  have hnormZero :
      centeredNorm a.a3 a.a1 middle ≠ 0 := by
    intro hzero
    have hrootZero : secondRoot ^ 2 = 0 := by
      rw [hsecondEquation, hzero, mul_zero]
    exact hsecondRoot (sq_eq_zero_iff.mp hrootZero)
  intro hnormSquare
  apply homegaInv
  have hrootSquare : IsSquare (secondRoot ^ 2) :=
    ⟨secondRoot, by ring⟩
  have hquotient :
      IsSquare
        (secondRoot ^ 2 /
          centeredNorm a.a3 a.a1 middle) :=
    hrootSquare.div hnormSquare
  rw [hsecondEquation] at hquotient
  simpa [hnormZero] using hquotient

/-- Raw pointwise form of the two-root endpoint construction.

The first root reconstructs an actual point of the fixed generalized surface.
Because it has the same first coordinate as `x`, primitive connecting
first-fiber transitivity puts it in the same full Vieta component.  The second
root certifies that the reached second-axis fiber is connecting.  An arbitrary
additional property `P` of the chosen middle trace is transported to the
actual point, allowing both the obstruction-ready and prescribed-pair sieves
to reuse this theorem. -/
theorem
    exists_sameVietaComponent_secondAxisPoint_of_connectingTwoRootData
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (x : SolutionSurface a)
    (xi omegaInv middle firstRoot secondRoot : ZMod p)
    (htraceX : traceAt a .first x.1 = xi)
    (qx qm : (ZMod p)ˣ)
    (heigenX : xi = splitTorusTrace qx)
    (hprimitiveX : orderOf qx = Nat.card (ZMod p)ˣ)
    (hregularX :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (hconnectingX :
      ¬ IsSquare (centeredNorm a.a2 a.a3 xi))
    (homegaInv : ¬ IsSquare omegaInv)
    (hfirstEquation :
      firstRoot ^ 2 = incidenceDiscriminant a xi middle)
    (hsecondEquation :
      secondRoot ^ 2 =
        omegaInv * centeredNorm a.a3 a.a1 middle)
    (hsecondRoot : secondRoot ≠ 0)
    (heigenMiddle : middle = splitTorusTrace qm)
    (hprimitiveMiddle : orderOf qm = Nat.card (ZMod p)ˣ)
    (hregularMiddle :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1 middle)
    (P : ZMod p → Prop) (hP : P middle) :
    ∃ y : SolutionSurface a,
      SameVietaComponent x y ∧
        traceAt a .second y.1 = splitTorusTrace qm ∧
          orderOf qm = Nat.card (ZMod p)ˣ ∧
            OrderedTraceCandidateRegular
              a.a2 a.a3 a.a1 (traceAt a .second y.1) ∧
              ¬ IsSquare
                (centeredNorm a.a3 a.a1
                  (traceAt a .second y.1)) ∧
                P (traceAt a .second y.1) := by
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by
      rw [ZMod.ringChar_zmod_n]
      omega)
  let traceY : Point (ZMod p) :=
    incidenceRootPoint a xi middle firstRoot
  have htraceY :
      tracePolynomial a traceY = 0 := by
    simpa [traceY] using
      tracePolynomial_incidenceRootPoint_eq_zero
        a xi middle firstRoot htwo hfirstEquation
  let y : SolutionSurface a :=
    ⟨inverseTracePoint a traceY,
      isSolution_inverseTracePoint a traceY hmultiplier htraceY⟩
  have hyFirstTrace : traceAt a .first y.1 = xi := by
    change (tracePoint a y.1).x1 = xi
    rw [tracePoint_inverseTracePoint a traceY hmultiplier]
    rfl
  have hyMiddleTrace : traceAt a .second y.1 = middle := by
    change (tracePoint a y.1).x2 = middle
    rw [tracePoint_inverseTracePoint a traceY hmultiplier]
    rfl
  have hsameFirst : x.1.x1 = y.1.x1 := by
    have htrace :
        a.multiplier * x.1.x1 - a.a1 =
          a.multiplier * y.1.x1 - a.a1 := by
      simpa [traceAt_first] using htraceX.trans hyFirstTrace.symm
    apply (mul_left_cancel₀ hmultiplier)
    linear_combination htrace
  have hxy : SameVietaComponent x y := by
    apply
      sameVietaComponent_of_same_firstCoordinate_of_primitiveConnecting
        p hpTwo a x y hsameFirst qx
    · exact htraceX.trans heigenX
    · exact hprimitiveX
    · simpa [htraceX] using hregularX
    · simpa [htraceX] using hconnectingX
  have hmiddleConnecting :
      ¬ IsSquare (centeredNorm a.a3 a.a1 middle) :=
    centeredNorm_not_isSquare_of_twoRootData
      homegaInv hsecondEquation hsecondRoot
  refine ⟨y, hxy, ?_, hprimitiveMiddle, ?_, ?_, ?_⟩
  · exact hyMiddleTrace.trans heigenMiddle
  · simpa [hyMiddleTrace] using hregularMiddle
  · simpa [hyMiddleTrace] using hmiddleConnecting
  · simpa [hyMiddleTrace] using hP

end

end GenMarkoff.General.Cage
