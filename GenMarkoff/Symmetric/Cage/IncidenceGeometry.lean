import GenMarkoff.Symmetric.Cage.IncidenceAlgebra
import GenMarkoff.Symmetric.Cage.RegularSplitFiber

/-!
# Incidence geometry for the symmetric split cage

This module turns the explicit discriminant and resultant identities into the
exact geometric interface needed by a cage point count.  Everything is
written in the affine trace coordinates

`X² + Y² + Z² - XYZ + A(X+Y+Z) + B = 0`.

The remaining Hasse--Weil input can therefore count the concrete
fiber-product witness type below; it does not need to assume an abstract
graph edge.
-/

namespace GenMarkoff.Symmetric.Cage

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- A trace-coordinate point with prescribed first two traces. -/
def incidenceTracePoint (xi middle z : K) : Point K :=
  ⟨xi, middle, z⟩

@[simp]
theorem incidenceTracePoint_x1 (xi middle z : K) :
    (incidenceTracePoint xi middle z).x1 = xi :=
  rfl

@[simp]
theorem incidenceTracePoint_x2 (xi middle z : K) :
    (incidenceTracePoint xi middle z).x2 = middle :=
  rfl

@[simp]
theorem incidenceTracePoint_x3 (xi middle z : K) :
    (incidenceTracePoint xi middle z).x3 = z :=
  rfl

/-- The trace-surface equation is the expected monic quadratic in the third
coordinate. -/
theorem tracePolynomial_incidenceTracePoint_eq_quadratic
    (c xi middle z : K) :
    tracePolynomial c (incidenceTracePoint xi middle z) =
      z ^ 2 + (traceSurfaceA c - xi * middle) * z +
        (xi ^ 2 + middle ^ 2 +
          traceSurfaceA c * (xi + middle) + traceSurfaceB c) := by
  simp only [tracePolynomial, incidenceTracePoint, traceSurfaceA,
    traceSurfaceB]
  ring

/-- Division-free completion of the square for the incidence quadratic. -/
theorem incidence_square_sub_discriminant
    (c xi middle z : K) :
    (2 * z + (traceSurfaceA c - xi * middle)) ^ 2 -
        incidenceDiscriminant c xi middle =
      4 * tracePolynomial c (incidenceTracePoint xi middle z) := by
  rw [tracePolynomial_incidenceTracePoint_eq_quadratic]
  simp only [incidenceDiscriminant]
  ring

/-- The quadratic-form point recovered from a square root of the incidence
discriminant. -/
def incidenceRootPoint
    (c xi middle root : K) : Point K :=
  incidenceTracePoint xi middle
    ((root - (traceSurfaceA c - xi * middle)) / 2)

@[simp]
theorem incidenceRootPoint_x1 (c xi middle root : K) :
    (incidenceRootPoint c xi middle root).x1 = xi :=
  rfl

@[simp]
theorem incidenceRootPoint_x2 (c xi middle root : K) :
    (incidenceRootPoint c xi middle root).x2 = middle :=
  rfl

/-- A square root of the explicit discriminant gives an actual point on the
trace surface. -/
theorem tracePolynomial_incidenceRootPoint_eq_zero
    (c xi middle root : K) (h2 : (2 : K) ≠ 0)
    (hroot : root ^ 2 = incidenceDiscriminant c xi middle) :
    tracePolynomial c (incidenceRootPoint c xi middle root) = 0 := by
  have hfour : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  apply (mul_eq_zero_iff_left hfour).mp
  change
    4 * tracePolynomial c
      (incidenceTracePoint xi middle
        ((root - (traceSurfaceA c - xi * middle)) / 2)) = 0
  rw [← incidence_square_sub_discriminant]
  have hlinear :
      2 * ((root - (traceSurfaceA c - xi * middle)) / 2) +
          (traceSurfaceA c - xi * middle) =
        root := by
    field_simp [h2]
    ring
  rw [hlinear, hroot]
  simp

/-- Conversely, every point of the incidence quadratic supplies the
canonical discriminant square root. -/
theorem incidenceDiscriminant_eq_square_of_tracePolynomial_eq_zero
    (c xi middle z : K)
    (hz : tracePolynomial c (incidenceTracePoint xi middle z) = 0) :
    incidenceDiscriminant c xi middle =
      (2 * z + (traceSurfaceA c - xi * middle)) ^ 2 := by
  have hcompletion := incidence_square_sub_discriminant c xi middle z
  rw [hz, mul_zero] at hcompletion
  exact (sub_eq_zero.mp hcompletion).symm

/-- A concrete point of the two incidence quadratics sharing one middle
trace.  This is the affine fiber product to be counted in the cage. -/
structure IncidenceEquationWitness (c xi eta : K) where
  middle : K
  firstRoot : K
  secondRoot : K
  firstEquation :
    firstRoot ^ 2 = incidenceDiscriminant c xi middle
  secondEquation :
    secondRoot ^ 2 = incidenceDiscriminant c eta middle

/-- The first trace-surface point represented by an incidence witness. -/
def IncidenceEquationWitness.firstTracePoint
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta) : Point K :=
  incidenceRootPoint c xi w.middle w.firstRoot

/-- The second trace-surface point represented by an incidence witness. -/
def IncidenceEquationWitness.secondTracePoint
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta) : Point K :=
  incidenceRootPoint c eta w.middle w.secondRoot

@[simp]
theorem IncidenceEquationWitness.firstTracePoint_x1
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta) :
    w.firstTracePoint.x1 = xi :=
  rfl

@[simp]
theorem IncidenceEquationWitness.secondTracePoint_x1
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta) :
    w.secondTracePoint.x1 = eta :=
  rfl

@[simp]
theorem IncidenceEquationWitness.firstTracePoint_x2
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta) :
    w.firstTracePoint.x2 = w.middle :=
  rfl

@[simp]
theorem IncidenceEquationWitness.secondTracePoint_x2
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta) :
    w.secondTracePoint.x2 = w.middle :=
  rfl

theorem IncidenceEquationWitness.firstTracePoint_mem
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta)
    (h2 : (2 : K) ≠ 0) :
    tracePolynomial c w.firstTracePoint = 0 :=
  tracePolynomial_incidenceRootPoint_eq_zero
    c xi w.middle w.firstRoot h2 w.firstEquation

theorem IncidenceEquationWitness.secondTracePoint_mem
    {c xi eta : K} (w : IncidenceEquationWitness c xi eta)
    (h2 : (2 : K) ≠ 0) :
    tracePolynomial c w.secondTracePoint = 0 :=
  tracePolynomial_incidenceRootPoint_eq_zero
    c eta w.middle w.secondRoot h2 w.secondEquation

/-- Candidate regularity makes the individual incidence quadratic separable.
The factor `xi + c² - 2` is exactly the second factor of the centered-norm
condition in the equal-coefficient specialization. -/
theorem incidenceQuadraticDiscriminant_ne_zero_of_candidateRegular
    (c xi : K) (h2 : (2 : K) ≠ 0)
    (hregular : OrderedTraceCandidateRegular c c c xi) :
    incidenceQuadraticDiscriminant c xi ≠ 0 := by
  have hD : xi ^ 2 - 4 ≠ 0 := by
    simpa only [eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hxiPlusTwo : xi + 2 ≠ 0 := by
    intro hzero
    apply hD
    have hxi : xi = -2 := by linear_combination hzero
    rw [hxi]
    ring
  have hxiPlusC : xi + c ≠ 0 := hregular.2.1
  have hcenter :
      xi ^ 2 - 4 + c ^ 2 + c ^ 2 + xi * c * c ≠ 0 := by
    simpa only [eval_orderedTraceCenteredNormPolynomial] using
      hregular.2.2.1
  have hcenterFactor :
      xi ^ 2 - 4 + c ^ 2 + c ^ 2 + xi * c * c =
        (xi + 2) * (xi + c ^ 2 - 2) := by
    ring
  have hxiLast : xi + c ^ 2 - 2 ≠ 0 := by
    intro hzero
    apply hcenter
    rw [hcenterFactor, hzero]
    simp
  rw [incidenceQuadraticDiscriminant_factor]
  have hsixteen : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 * 2 * (2 * 2) by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h2) (mul_ne_zero h2 h2)
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero hsixteen hxiPlusTwo)
      (pow_ne_zero 2 hxiPlusC))
    hxiLast

/-- Off the diagonal and the explicit obstruction locus, the two incidence
quadratics are coprime.  This is the precise resultant condition available
to an eventual irreducibility/Hasse--Weil argument. -/
theorem incidencePairResultant_ne_zero
    (c xi eta : K) (hc : c ^ 2 ≠ 4) (hxiEta : xi ≠ eta)
    (hobstruction : incidencePairObstruction c xi eta ≠ 0) :
    incidencePairResultant c xi eta ≠ 0 := by
  have hcPlus : c + 2 ≠ 0 := by
    intro hzero
    apply hc
    have hc' : c = -2 := by linear_combination hzero
    rw [hc']
    ring
  have hcMinus : c - 2 ≠ 0 := by
    intro hzero
    apply hc
    have hc' : c = 2 := by linear_combination hzero
    rw [hc']
    ring
  have hetaXi : eta - xi ≠ 0 := sub_ne_zero.mpr hxiEta.symm
  rw [incidencePairResultant_factor]
  exact
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hetaXi))
          (pow_ne_zero 2 hcPlus))
        (pow_ne_zero 3 hcMinus))
      hobstruction

/-- The generic off-diagonal hypotheses exposed to the Hasse--Weil layer. -/
def IsHasseWeilReadyIncidencePair
    (c xi eta : K) : Prop :=
  xi ≠ eta ∧ incidencePairObstruction c xi eta ≠ 0

theorem IsHasseWeilReadyIncidencePair.resultant_ne_zero
    {c xi eta : K} (h : IsHasseWeilReadyIncidencePair c xi eta)
    (hc : c ^ 2 ≠ 4) :
    incidencePairResultant c xi eta ≠ 0 :=
  incidencePairResultant_ne_zero c xi eta hc h.1 h.2

/-- Inverse of one affine trace coordinate when the symmetric multiplier is
nonzero. -/
def inverseTraceCoordinate (c t : K) : K :=
  (t + c) / multiplier c

/-- Coordinatewise inverse trace transformation. -/
def inverseTracePoint (c : K) (t : Point K) : Point K :=
  ⟨inverseTraceCoordinate c t.x1,
    inverseTraceCoordinate c t.x2,
    inverseTraceCoordinate c t.x3⟩

@[simp]
theorem trace_inverseTraceCoordinate
    (c t : K) (hmultiplier : multiplier c ≠ 0) :
    trace c (inverseTraceCoordinate c t) = t := by
  simp only [trace, inverseTraceCoordinate]
  field_simp [hmultiplier]
  ring

@[simp]
theorem tracePoint_inverseTracePoint
    (c : K) (t : Point K) (hmultiplier : multiplier c ≠ 0) :
    tracePoint c (inverseTracePoint c t) = t := by
  ext <;>
    simp [tracePoint, inverseTracePoint,
      trace_inverseTraceCoordinate c _ hmultiplier]

/-- A trace-surface point pulls back to an actual symmetric surface point. -/
theorem isSolution_inverseTracePoint
    (c : K) (t : Point K) (hmultiplier : multiplier c ≠ 0)
    (ht : tracePolynomial c t = 0) :
    IsSolution (coefficients c) (inverseTracePoint c t) := by
  rw [isSolution_iff_tracePolynomial_tracePoint c _ hmultiplier]
  simpa [tracePoint_inverseTracePoint c t hmultiplier] using ht

end

end GenMarkoff.Symmetric.Cage
