import GenMarkoff.Symmetric.MiddleGame.ShiftedTraceEquation
import GenMarkoff.Symmetric.TraceParameters

/-!
# Actual symmetric fiber parameters

This module turns the ordered candidate-regular predicate into the exact
nonvanishing hypotheses for the affine one-step trace equation.  It also
records the normalization `H = alpha * h`, which changes

`alpha * h + beta / h + gamma`

to

`H + sigma / H + gamma`, with `sigma = alpha * beta`.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open GenMarkoff

noncomputable section

variable {K : Type*} [Field K]

theorem actualAlpha_ne_zero
    (c : K) (hmultiplier : multiplier c ≠ 0) :
    actualAlpha c ≠ 0 := by
  simpa [actualAlpha] using hmultiplier

/-- Candidate regularity identifies the actual normalized weight product and
makes it nonzero. -/
theorem actualSigma_ne_zero_of_candidateRegular
    (c u t : K) (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    actualSigma c u t ≠ 0 := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  rw [actualSigma_eq_orderedTraceSigma c u t htrace hD]
  exact hregular.sigma_ne_zero

/-- Candidate regularity forces the symmetric surface multiplier to be
nonzero.  This is the middle-game version of the same observation used by the
split primitive endgame. -/
theorem multiplier_ne_zero_of_candidateRegular
    (c u t : K) (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    multiplier c ≠ 0 := by
  intro hzero
  apply actualSigma_ne_zero_of_candidateRegular c u t htrace hregular
  change multiplier c * (multiplier c * centeredFiberProduct c u t) = 0
  rw [hzero]
  simp

/-- Candidate regularity excludes equal normalized weights for the actual
affine trace equation. -/
theorem actualSigma_ne_one_of_candidateRegular
    (c u t : K) (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    actualSigma c u t ≠ 1 := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  rw [actualSigma_eq_orderedTraceSigma c u t htrace hD]
  exact hregular.sigma_ne_one

/-- If the surface multiplier is nonzero, candidate regularity makes the
second actual weight nonzero as well. -/
theorem actualBeta_ne_zero_of_candidateRegular
    (c u t : K) (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    actualBeta c u t ≠ 0 := by
  intro hbeta
  apply actualSigma_ne_zero_of_candidateRegular c u t htrace hregular
  simp [actualSigma, hbeta]

/-- The actual parameters satisfy the common-even Kummer condition. -/
theorem actualEvenObstruction_ne_zero_of_candidateRegular
    (c u t : K) (htrace : t = trace c u) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    shiftedTraceEvenObstruction (actualSigma c u t)
        (actualGamma c u t) ≠ 0 := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  rw [actualSigma_eq_orderedTraceSigma c u t htrace hD,
    actualGamma_eq_orderedTraceGamma c u t htrace hD]
  exact hregular.evenObstruction_ne_zero hc

/-- Exact normalization of the actual adjacent-trace formula. -/
theorem trace_fiberPoint_x2_normalized
    (c u t q h : K) (hmultiplier : multiplier c ≠ 0) (hh : h ≠ 0) :
    trace c (fiberPoint c u t q h).x2 =
      actualAlpha c * h +
        actualSigma c u t / (actualAlpha c * h) + actualGamma c u t := by
  rw [trace_fiberPoint_x2 c u t q h hh]
  have halpha : actualAlpha c ≠ 0 :=
    actualAlpha_ne_zero c hmultiplier
  simp only [actualSigma]
  field_simp [halpha, hh]

/-- The scalar used to normalize the leading shifted-trace weight to one. -/
def actualAlphaUnit (c : K) (hmultiplier : multiplier c ≠ 0) : Kˣ :=
  Units.mk0 (actualAlpha c) (actualAlpha_ne_zero c hmultiplier)

@[simp]
theorem actualAlphaUnit_val (c : K) (hmultiplier : multiplier c ≠ 0) :
    (actualAlphaUnit c hmultiplier : K) = actualAlpha c :=
  rfl

/-- The actual adjacent trace is exactly the normalized shifted weighted
trace at the rescaled torus parameter. -/
theorem shiftedWeightedTrace_normalizedParameter_eq_trace_fiberPoint_x2
    (c u t q : K) (h : Kˣ) (hmultiplier : multiplier c ≠ 0) :
    BGS.Markoff.weightedSplitTorusTrace 1 (actualSigma c u t)
          (actualAlphaUnit c hmultiplier * h) + actualGamma c u t =
      trace c (fiberPoint c u t q h).x2 := by
  rw [trace_fiberPoint_x2_normalized c u t q h hmultiplier (Units.ne_zero h)]
  simp only [BGS.Markoff.weightedSplitTorusTrace, actualAlphaUnit_val,
    Units.val_mul, Units.val_inv_eq_inv_val, one_mul]
  have halpha : actualAlpha c ≠ 0 := actualAlpha_ne_zero c hmultiplier
  have hh : (h : K) ≠ 0 := Units.ne_zero h
  field_simp [halpha, hh]

/-- Candidate regularity supplies all normalized parameter hypotheses used by
the shifted-cover Kummer tower. -/
theorem actual_shiftedCover_parameters_regular
    (c u t : K) (htrace : t = trace c u)
    (hmultiplier : multiplier c ≠ 0) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    actualAlpha c ≠ 0 ∧ actualBeta c u t ≠ 0 ∧
      actualSigma c u t ≠ 0 ∧ actualSigma c u t ≠ 1 ∧
        shiftedTraceEvenObstruction (actualSigma c u t)
          (actualGamma c u t) ≠ 0 := by
  exact ⟨actualAlpha_ne_zero c hmultiplier,
    actualBeta_ne_zero_of_candidateRegular c u t htrace hregular,
    actualSigma_ne_zero_of_candidateRegular c u t htrace hregular,
    actualSigma_ne_one_of_candidateRegular c u t htrace hregular,
    actualEvenObstruction_ne_zero_of_candidateRegular c u t htrace hc hregular⟩

end

end GenMarkoff.Symmetric.MiddleGame
