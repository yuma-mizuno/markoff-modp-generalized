module

public import GenMarkoff.General.Trace.Parameters
public import GenMarkoff.General.Assembly.RotationComponent
public import GenMarkoff.General.Assembly.SmallOrderCount
public import GenMarkoff.Arithmetic.EventualAdmissibility
public import GenMarkoff.Core.Action
public import GenMarkoff.Core.Statements
public import GenMarkoff.Assembly.RotationDivisibility
public import BGS.Markoff.Assembly.GiantOrbit
public import GenMarkoff.General.Assembly.RegularMiddleIteration
public import BGS.NumberTheory.ExplicitDivisorBound
public import BGS.Markoff.Endgame.PrimitiveInclusionExclusion
public import GenMarkoff.General.MiddleGame.RotationEigenvalueOrder
public import GenMarkoff.General.FiberDynamics
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import GenMarkoff.TraceCurve.ExceptionalRouting
public import BGS.Markoff.Core.FiniteRotationEigenvalues
public import BGS.Markoff.Opening.PeriodicSemisimple
public import GenMarkoff.General.Assembly.RegularMiddleThreshold
public import GenMarkoff.General.Assembly.RegularNonsplitEndgame

@[expose] public section

/-!
# Actual rotation order in the two trace branches

The middle game measures the order of the actual two-Vieta rotation, whose
linear part is the square of the fiber matrix.  For a nonparabolic trace,
the classification `exists_split_or_quadraticNormOneTrace` writes the trace
as `q + q⁻¹` for a split eigenvalue `q` or as the trace of an element `w` of
the quadratic norm-one torus.  This file shows that the actual order
`alternatingActualOrder` is then `orderOf (q ^ 2)`, respectively
`orderOf (w ^ 2)`, which is the order hypothesis used by the split and
nonsplit endgames.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame
open GenMarkoff.General.MiddleGame
open GenMarkoff.ShiftedTrace.Endgame.Nonsplit

noncomputable section

/-- In the split branch of the nonparabolic trace dichotomy, the actual
rotation order carried by an alternating state is the order of the squared
split eigenvalue. -/
theorem alternatingActualOrder_eq_orderOf_sq_of_splitTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (state : AlternatingRegularState a)
    (q : (ZMod p)ˣ)
    (htrace :
      traceAt a state.direction.fixed state.point.1 =
        splitTorusTrace q)
    (hq : (q : ZMod p) ^ 2 ≠ 1) :
    alternatingActualOrder state = orderOf (q ^ 2) := by
  -- `alternatingActualOrder` unfolds through `rotationLinearOrderAt` to
  -- `rotationLinearOrder (traceAt ..)`; restate so that
  -- `rotationLinearOrder_eq_bgsRotationOrder_div_gcd` can rewrite it.
  change
    rotationLinearOrder
        (traceAt a state.direction.fixed state.point.1) =
      orderOf (q ^ 2)
  rw [Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
    htrace, rotationOrder_splitTorusTrace q hq, orderOf_pow]

/-- In the nonsplit branch, the same actual-order quantity is the order of
the squared quadratic norm-one eigenvalue. -/
theorem alternatingActualOrder_eq_orderOf_sq_of_quadraticNormOneTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (state : AlternatingRegularState a)
    (w : quadraticNormOneTorus p)
    (htrace :
      traceAt a state.direction.fixed state.point.1 =
        quadraticNormOneTrace p w)
    (hw :
      (((w : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p) ^ 2 ≠ 1)) :
    alternatingActualOrder state = orderOf (w ^ 2) := by
  -- `alternatingActualOrder` unfolds through `rotationLinearOrderAt` to
  -- `rotationLinearOrder (traceAt ..)`; restate so that
  -- `rotationLinearOrder_eq_bgsRotationOrder_div_gcd` can rewrite it.
  change
    rotationLinearOrder
        (traceAt a state.direction.fixed state.point.1) =
      orderOf (w ^ 2)
  rw [Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
    htrace, rotationOrder_quadraticNormOneTrace p w hw, orderOf_pow]

end

end GenMarkoff.General.Assembly
