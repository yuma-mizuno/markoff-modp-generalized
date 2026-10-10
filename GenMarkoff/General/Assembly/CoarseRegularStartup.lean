import GenMarkoff.General.Arithmetic.ReasonableCutoff
import GenMarkoff.General.Assembly.SmallOrderCount
import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.Assembly.RotationComponent

/-!
# Coarse startup of the regular middle game

Write `T = #divisors (p - 1) + #divisors (p + 1)` and
`coarseRegularBound p = (192 T)^3 + 1`.  Beyond `reasonableAnalyticCutoff`,
every `p`-divisible punctured rotation orbit contains an alternating
candidate-regular state of actual order at least `coarseRegularBound p`
(`exists_sameRotationComponent_coarseRegularState_of_dvd`).

The count is made on both axes at once: fewer than `p` surface points have
both their first and second traces of small actual order or at a root of an
ordered safe polynomial, so some point of the orbit has a first- or
second-axis trace that is candidate regular of large order
(`exists_mem_rotationOrbit_with_candidateRegular_large_first_or_second_of_dvd`).
That point is used directly as the starting state.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Explicit

noncomputable section

/-- The actual-order threshold `(192 T)^3 + 1`, with
`T = #divisors (p - 1) + #divisors (p + 1)`, above which the middle game's
Corvaja--Zannier cube estimate applies. -/
def coarseRegularBound (p : ℕ) : ℕ :=
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  (192 * T) ^ 3 + 1

/-- The cube `(192 T)^3` lies strictly below `coarseRegularBound p`. -/
theorem corvajaZannierCube_lt_coarseRegularBound (p : ℕ) :
    (192 * ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
      coarseRegularBound p := by
  simp [coarseRegularBound]

/-- Beyond `reasonableAnalyticCutoff`, for coefficients with nonzero
multiplier and `a₁ ^ 2 ≠ 4`, `a₂ ^ 2 ≠ 4`, a `p`-divisible punctured rotation
orbit contains an alternating candidate-regular state of actual order at
least `coarseRegularBound p`. -/
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
