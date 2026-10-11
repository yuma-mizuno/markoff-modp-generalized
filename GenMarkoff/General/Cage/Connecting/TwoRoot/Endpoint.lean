module

public import GenMarkoff.General.Cage.Connecting.Fiber
public import GenMarkoff.General.Cage.Incidence.Geometry

@[expose] public section

/-!
# Pointwise reconstruction from a two-root connecting witness

Starting from a point on a primitive connecting first-axis fiber, one
incidence root suffices to construct a point of the surface with the same
first trace and a prescribed middle second trace.  The primitive connecting
theorem on the first-axis fiber
(`sameVietaComponent_of_same_firstCoordinate_of_primitiveConnecting`) then
joins the two points.  The second square root is retained because its
nonvanishing and nonsquare scale certify that the second-axis fiber reached
is connecting.
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

/-- Pointwise two-root step.  Let `x` lie on a primitive, candidate-regular,
connecting first-axis fiber with trace `xi`, and let `firstRoot`,
`secondRoot ≠ 0` be two-root data over a primitive, candidate-regular middle
trace `middle`, with `omegaInv` a nonsquare.  Then some `y` in the same
full-Vieta component as `x` has second-axis trace `middle` and lies on a
connecting second-axis fiber.  Any property `P` of `middle` is transferred to
`traceAt a .second y`, so that the different sieves can use this theorem. -/
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
    -- `traceAt a .first` and `(tracePoint a ·).x1` both unfold to
    -- `orderedTrace a.multiplier a.a1 _`; restate so that
    -- `tracePoint_inverseTracePoint` rewrites.
    change (tracePoint a y.1).x1 = xi
    rw [tracePoint_inverseTracePoint a traceY hmultiplier]
    rfl
  have hyMiddleTrace : traceAt a .second y.1 = middle := by
    -- `traceAt a .second` and `(tracePoint a ·).x2` both unfold to
    -- `orderedTrace a.multiplier a.a2 _`; restate as above.
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
