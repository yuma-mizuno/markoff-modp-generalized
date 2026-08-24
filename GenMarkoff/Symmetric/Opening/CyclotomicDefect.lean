import GenMarkoff.Symmetric.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# The cyclotomic defect for the equal-coefficient family

This module isolates the characteristic-zero algebra needed by the opening
argument.  For the equal coefficient triple `(c, c, c)`, the reciprocal
eigenvalue traces satisfy the shifted trace equation from
`GenMarkoff.Symmetric.Basic`.  We record that equation as a cyclotomic defect
and prove an explicit archimedean bound.  The later number-field reduction and
the rigidity of its zero locus are deliberately not assumed here.
-/

namespace GenMarkoff.Symmetric.Opening

universe u

/-- The polynomial defect in three trace variables for the equal-coefficient
generalized Markoff family. -/
def traceDefect {R : Type u} [CommRing R]
    (c t₁ t₂ t₃ : R) : R :=
  t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃ +
    c * (c + 2) * (t₁ + t₂ + t₃) + c ^ 2 * (2 * c + 3)

/-- The trace defect is exactly the symmetric trace-coordinate polynomial. -/
theorem traceDefect_eq_tracePolynomial {R : Type u} [CommRing R]
    (c t₁ t₂ t₃ : R) :
    traceDefect c t₁ t₂ t₃ =
      tracePolynomial c ⟨t₁, t₂, t₃⟩ :=
  rfl

/-- The shifted trace of the affine origin is a zero of the trace defect. -/
@[simp]
theorem traceDefect_neg_self (R : Type u) [CommRing R] (c : R) :
    traceDefect c (-c) (-c) (-c) = 0 := by
  simp [traceDefect]
  ring

/-- The reciprocal-eigenvalue trace. -/
def cyclotomicTrace {K : Type u} [Field K] (z : K) : K :=
  z + z⁻¹

/-- The generalized symmetric defect of three reciprocal-eigenvalue traces. -/
def cyclotomicDefect {K : Type u} [Field K]
    (c z₁ z₂ z₃ : K) : K :=
  traceDefect c (cyclotomicTrace z₁) (cyclotomicTrace z₂)
    (cyclotomicTrace z₃)

/-- Expanding the definition identifies the cyclotomic defect with the
trace-coordinate polynomial. -/
theorem cyclotomicDefect_eq_tracePolynomial {K : Type u} [Field K]
    (c z₁ z₂ z₃ : K) :
    cyclotomicDefect c z₁ z₂ z₃ =
      tracePolynomial c
        ⟨cyclotomicTrace z₁, cyclotomicTrace z₂,
          cyclotomicTrace z₃⟩ :=
  rfl

/-- If the reciprocal traces are the three affine trace coordinates of a
point, their cyclotomic defect is the square of the multiplier times the
original surface polynomial. -/
theorem cyclotomicDefect_eq_multiplier_sq_mul_polynomial
    {K : Type u} [Field K] (c z₁ z₂ z₃ : K) (x : Point K)
    (h₁ : cyclotomicTrace z₁ = trace c x.x1)
    (h₂ : cyclotomicTrace z₂ = trace c x.x2)
    (h₃ : cyclotomicTrace z₃ = trace c x.x3) :
    cyclotomicDefect c z₁ z₂ z₃ =
      multiplier c ^ 2 * polynomial (coefficients c) x := by
  rw [cyclotomicDefect_eq_tracePolynomial, h₁, h₂, h₃]
  exact tracePolynomial_tracePoint c x

/-- On the complex unit circle, the reciprocal-eigenvalue trace is twice the
real part. -/
theorem cyclotomicTrace_eq_two_mul_re {z : ℂ} (hz : ‖z‖ = 1) :
    cyclotomicTrace z = (2 * z.re : ℂ) := by
  rw [cyclotomicTrace, Complex.inv_eq_conj hz]
  apply Complex.ext
  · simp
    ring
  · simp

/-- A reciprocal trace on the complex unit circle has norm at most two. -/
theorem norm_cyclotomicTrace_le_two {z : ℂ} (hz : ‖z‖ = 1) :
    ‖cyclotomicTrace z‖ ≤ 2 := by
  rw [cyclotomicTrace]
  calc
    ‖z + z⁻¹‖ ≤ ‖z‖ + ‖z⁻¹‖ := norm_add_le _ _
    _ = 2 := by simp [hz]; norm_num

/-- The explicit embedding-wise bound used by the symmetric opening. -/
noncomputable def archimedeanBound (c : ℂ) : ℝ :=
  20 + 6 * ‖c * (c + 2)‖ + ‖c ^ 2 * (2 * c + 3)‖

theorem archimedeanBound_nonneg (c : ℂ) : 0 ≤ archimedeanBound c := by
  simp only [archimedeanBound]
  positivity

/-- Algebraic archimedean estimate for the generalized trace defect.  This is
separated from roots of unity so that later opening arguments can reuse it for
every complex embedding. -/
theorem norm_traceDefect_le
    (c t₁ t₂ t₃ : ℂ)
    (ht₁ : ‖t₁‖ ≤ 2) (ht₂ : ‖t₂‖ ≤ 2) (ht₃ : ‖t₃‖ ≤ 2) :
    ‖traceDefect c t₁ t₂ t₃‖ ≤
      archimedeanBound c := by
  have ht₁sq : ‖t₁ ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg t₁]
  have ht₂sq : ‖t₂ ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg t₂]
  have ht₃sq : ‖t₃ ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg t₃]
  have htprod : ‖t₁ * t₂ * t₃‖ ≤ 8 := by
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg t₁, norm_nonneg t₂, norm_nonneg t₃,
      mul_nonneg (norm_nonneg t₁) (norm_nonneg t₂)]
  have htraceSum : ‖t₁ + t₂ + t₃‖ ≤ 6 := by
    calc
      ‖t₁ + t₂ + t₃‖ ≤ ‖t₁ + t₂‖ + ‖t₃‖ := norm_add_le _ _
      _ ≤ (‖t₁‖ + ‖t₂‖) + ‖t₃‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ 6 := by linarith
  have hquadraticSum : ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2‖ ≤ 12 := by
    calc
      ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2‖ ≤
          ‖t₁ ^ 2 + t₂ ^ 2‖ + ‖t₃ ^ 2‖ := norm_add_le _ _
      _ ≤ (‖t₁ ^ 2‖ + ‖t₂ ^ 2‖) + ‖t₃ ^ 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ 12 := by linarith
  have hmarkoffPart :
      ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃‖ ≤ 20 := by
    calc
      ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃‖ ≤
          ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2‖ + ‖t₁ * t₂ * t₃‖ :=
        norm_sub_le _ _
      _ ≤ 20 := by linarith
  have hlinear :
      ‖c * (c + 2) * (t₁ + t₂ + t₃)‖ ≤ 6 * ‖c * (c + 2)‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (c * (c + 2))]
  rw [traceDefect]
  change _ ≤ 20 + 6 * ‖c * (c + 2)‖ + ‖c ^ 2 * (2 * c + 3)‖
  calc
    ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃ +
        c * (c + 2) * (t₁ + t₂ + t₃) + c ^ 2 * (2 * c + 3)‖ ≤
        ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃‖ +
          ‖c * (c + 2) * (t₁ + t₂ + t₃)‖ +
            ‖c ^ 2 * (2 * c + 3)‖ := by
      calc
        _ ≤ ‖(t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃) +
              c * (c + 2) * (t₁ + t₂ + t₃)‖ +
                ‖c ^ 2 * (2 * c + 3)‖ := norm_add_le _ _
        _ ≤ (‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃‖ +
              ‖c * (c + 2) * (t₁ + t₂ + t₃)‖) +
                ‖c ^ 2 * (2 * c + 3)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 20 + 6 * ‖c * (c + 2)‖ + ‖c ^ 2 * (2 * c + 3)‖ := by
      nlinarith [norm_nonneg (c * (c + 2))]

/-- Explicit archimedean bound for the generalized cyclotomic defect. -/
theorem norm_cyclotomicDefect_le
    (c : ℂ) {z₁ z₂ z₃ : ℂ}
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hz₃ : ‖z₃‖ = 1) :
    ‖cyclotomicDefect c z₁ z₂ z₃‖ ≤
      archimedeanBound c := by
  exact norm_traceDefect_le c (cyclotomicTrace z₁) (cyclotomicTrace z₂)
    (cyclotomicTrace z₃) (norm_cyclotomicTrace_le_two hz₁)
      (norm_cyclotomicTrace_le_two hz₂) (norm_cyclotomicTrace_le_two hz₃)

end GenMarkoff.Symmetric.Opening
