import GenMarkoff.General.Arithmetic.ReasonableCutoff
import GenMarkoff.General.Assembly.SmallOrderCount
import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.Assembly.RotationComponent

/-!
# Source-order-preserving coarse startup

The eventual startup first found a large first/second rotation cycle and then
changed the active axis to obtain candidate regularity.  That change costs one
extra factor of the simultaneous divisor count.

For the first explicit reasonable cutoff we instead count, on both axes at
once, the trace labels which are either small-order or roots of the ordered
safe polynomial.  A point outside that trace-pair set is already an
alternating candidate-regular source, so its actual order is preserved.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Explicit

noncomputable section

/-- The strict actual-order threshold at which the coefficient-`192`
Corvaja--Zannier cube is available. -/
def coarseRegularBound (p : ℕ) : ℕ :=
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  (192 * T) ^ 3 + 1

theorem corvajaZannierCube_lt_coarseRegularBound (p : ℕ) :
    (192 * ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
      coarseRegularBound p := by
  simp [coarseRegularBound]

/-- A `p`-divisible punctured component contains an alternating
candidate-regular state beyond the Corvaja--Zannier cube, at the reasonable
cutoff. -/
theorem exists_sameRotationComponent_coarseRegularState_of_dvd
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (hpCutoff : reasonableAnalyticCutoff ≤ p)
    (a : Coefficients (ZMod p)) (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (x : PuncturedSolutionSurface a)
    (hdiv : p ∣ (puncturedRotationOrbit x).ncard) :
    ∃ state : AlternatingRegularState a,
      SameRotationComponent x.1 state.point ∧
        coarseRegularBound p ≤ alternatingActualOrder state := by
  obtain ⟨y, hyOrbit, hy⟩ :=
    exists_mem_rotationOrbit_with_candidateRegular_large_first_or_second_of_dvd
      p hpTwo a hmultiplier hA1 hA2 (coarseRegularBound p) x hdiv
        (by
          simpa [coarseRegularBound] using
            reasonable_coarseRegularTracePairCount_lt hpCutoff)
  have hcomponent : SameRotationComponent x.1 y.1 :=
    (mem_puncturedRotationOrbit_iff_sameRotationComponent x y).mp hyOrbit
  rcases hy with hyFirst | hySecond
  · let state : AlternatingRegularState a :=
      ⟨.firstSecond, y.1, by
        simpa [alternatingTraceRegular, traceAt,
          coordinateTrace1, coefficientAt, coordinateAt, orderedTrace] using
          hyFirst.1⟩
    refine ⟨state, ?_, ?_⟩
    · simpa [state] using hcomponent
    · simpa [state, alternatingActualOrder,
        AlternatingDirectedAxis.fixed, rotationLinearOrderAt, traceAt,
        coordinateTrace1, coefficientAt, coordinateAt, orderedTrace] using
        hyFirst.2
  · let state : AlternatingRegularState a :=
      ⟨.secondFirst, y.1, by
        simpa [alternatingTraceRegular, traceAt,
          coordinateTrace2, coefficientAt, coordinateAt, orderedTrace] using
          hySecond.1⟩
    refine ⟨state, ?_, ?_⟩
    · simpa [state] using hcomponent
    · simpa [state, alternatingActualOrder,
        AlternatingDirectedAxis.fixed, rotationLinearOrderAt, traceAt,
        coordinateTrace2, coefficientAt, coordinateAt, orderedTrace] using
        hySecond.2

end

end GenMarkoff.General.Assembly
