import GenMarkoff.Divisibility.RegularAngles
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The raw-angle defect at zero coordinates

Lean's division is total, so the three raw angle functions are defined even
when a coordinate vanishes.  They do not then satisfy the pointwise total and
pairing identities from the regular locus.  This file computes the exact
defect: `rawAngle_balance_with_zero_correction` is a pointwise identity at
every punctured solution whose only correction term is
`zeroRawAngleCorrection`, the raw angle attached to a vanishing coordinate
(whose denominators are still nonzero there).  Its sum over a Vieta-invariant
finite set is taken in `GenMarkoff.Divisibility.RawAngle.Orbit`.
-/

namespace GenMarkoff

universe u

section Field

variable {K : Type u} [Field K]

/-- The sum of the raw angles whose own coordinate vanishes.  On a punctured
solution at most one summand is nonzero. -/
noncomputable def zeroRawAngleCorrection (a : Coefficients K) (x : Point K) : K := by
  classical
  exact
    (if x.x1 = 0 then rawAngle1 a x else 0) +
      (if x.x2 = 0 then rawAngle2 a x else 0) +
      (if x.x3 = 0 then rawAngle3 a x else 0)

private theorem rawAngle_total_of_x1_eq_zero
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx1 : x.x1 = 0) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0) :
    rawAngle1 a x + rawAngle2 a x + rawAngle3 a x = 2 * rawAngle1 a x := by
  unfold rawAngle1 rawAngle2 rawAngle3
  rw [hx1]
  field_simp [h2, hx2, hx3]
  ring

private theorem adjacent_rawAngle_pairs_of_x1_eq_zero
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx1 : x.x1 = 0) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0) :
    (rawAngle2 a x + rawAngle2 a (vieta2 a x)) +
        (rawAngle3 a x + rawAngle3 a (vieta3 a x)) =
      2 * rawAngle1 a x := by
  unfold rawAngle1 rawAngle2 rawAngle3 vieta2 vieta3
  rw [hx1]
  field_simp [h2, hx2, hx3]
  ring

private theorem rawAngle_total_of_x2_eq_zero
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx2 : x.x2 = 0) (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0) :
    rawAngle1 a x + rawAngle2 a x + rawAngle3 a x = 2 * rawAngle2 a x := by
  unfold rawAngle1 rawAngle2 rawAngle3
  rw [hx2]
  field_simp [h2, hx1, hx3]
  ring

private theorem adjacent_rawAngle_pairs_of_x2_eq_zero
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx2 : x.x2 = 0) (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0) :
    (rawAngle1 a x + rawAngle1 a (vieta1 a x)) +
        (rawAngle3 a x + rawAngle3 a (vieta3 a x)) =
      2 * rawAngle2 a x := by
  unfold rawAngle1 rawAngle2 rawAngle3 vieta1 vieta3
  rw [hx2]
  field_simp [h2, hx1, hx3]
  ring

private theorem rawAngle_total_of_x3_eq_zero
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx3 : x.x3 = 0) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0) :
    rawAngle1 a x + rawAngle2 a x + rawAngle3 a x = 2 * rawAngle3 a x := by
  unfold rawAngle1 rawAngle2 rawAngle3
  rw [hx3]
  field_simp [h2, hx1, hx2]
  ring

private theorem adjacent_rawAngle_pairs_of_x3_eq_zero
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx3 : x.x3 = 0) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0) :
    (rawAngle1 a x + rawAngle1 a (vieta1 a x)) +
        (rawAngle2 a x + rawAngle2 a (vieta2 a x)) =
      2 * rawAngle3 a x := by
  unfold rawAngle1 rawAngle2 rawAngle3 vieta1 vieta2
  rw [hx3]
  field_simp [h2, hx1, hx2]
  ring

/-- Exact pointwise balance for the totalized raw angles at a punctured
solution: `2 (Δ₁ + Δ₂ + Δ₃) + s` equals the sum of the three Vieta pairs
`Δᵢ x + Δᵢ (μᵢ x)` plus twice `zeroRawAngleCorrection a x`.  Away from the
coordinate planes the correction vanishes and this combines `rawAngle_total`
with the three pairing identities. -/
theorem rawAngle_balance_with_zero_correction
    (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx : IsSolution a x) (hpunctured : x ≠ origin) :
    2 * (rawAngle1 a x + rawAngle2 a x + rawAngle3 a x) + a.multiplier =
      ((rawAngle1 a x + rawAngle1 a (vieta1 a x)) +
        (rawAngle2 a x + rawAngle2 a (vieta2 a x)) +
        (rawAngle3 a x + rawAngle3 a (vieta3 a x))) +
        2 * zeroRawAngleCorrection a x := by
  by_cases hx1 : x.x1 = 0
  · have hne := coordinates_ne_zero_of_x1_eq_zero a x hx hpunctured hx1
    have htotal := rawAngle_total_of_x1_eq_zero a x h2 hx1 hne.1 hne.2
    have hadjacent := adjacent_rawAngle_pairs_of_x1_eq_zero a x h2 hx1 hne.1 hne.2
    have hpair := rawAngle1_add_vieta1 a x h2 hne.1 hne.2
    simp [zeroRawAngleCorrection, hx1, hne.1, hne.2]
    linear_combination 2 * htotal - hpair - hadjacent
  · by_cases hx2 : x.x2 = 0
    · have hne := coordinates_ne_zero_of_x2_eq_zero a x hx hpunctured hx2
      have htotal := rawAngle_total_of_x2_eq_zero a x h2 hx2 hne.1 hne.2
      have hadjacent := adjacent_rawAngle_pairs_of_x2_eq_zero a x h2 hx2 hne.1 hne.2
      have hpair := rawAngle2_add_vieta2 a x h2 hne.1 hne.2
      simp [zeroRawAngleCorrection, hx1, hx2, hne.2]
      linear_combination 2 * htotal - hpair - hadjacent
    · by_cases hx3 : x.x3 = 0
      · have hne := coordinates_ne_zero_of_x3_eq_zero a x hx hpunctured hx3
        have htotal := rawAngle_total_of_x3_eq_zero a x h2 hx3 hne.1 hne.2
        have hadjacent := adjacent_rawAngle_pairs_of_x3_eq_zero a x h2 hx3 hne.1 hne.2
        have hpair := rawAngle3_add_vieta3 a x h2 hne.1 hne.2
        simp [zeroRawAngleCorrection, hx1, hx2, hx3]
        linear_combination 2 * htotal - hpair - hadjacent
      · have htotal := rawAngle_total a x h2 hx1 hx2 hx3 hx
        have hpair1 := rawAngle1_add_vieta1 a x h2 hx2 hx3
        have hpair2 := rawAngle2_add_vieta2 a x h2 hx1 hx3
        have hpair3 := rawAngle3_add_vieta3 a x h2 hx1 hx2
        simp [zeroRawAngleCorrection, hx1, hx2, hx3]
        linear_combination 2 * htotal - hpair1 - hpair2 - hpair3

end Field

end GenMarkoff
