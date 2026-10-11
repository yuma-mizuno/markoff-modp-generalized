module

public import GenMarkoff.General.Trace.Parameters

@[expose] public section

/-!
# The third Vieta involution on a first-axis torus chart

Keep the coefficient triple fixed, fix the first coordinate `u`, and put
`t = a.multiplier * u - a₁` with `t = q + q⁻¹`.  On the torus chart
`fiberPoint1` of the first-coordinate fiber, with
`P = centeredFiberProduct a.a2 a.a3 u t`, the third Vieta involution acts by

`vieta3 : h ↦ P / h`

(`vieta3_fiberPoint1`).  Because the two affine translations on the fiber
differ, the reflection is computed after centering the moving pair
(`centerCoordinates_reflect_second`), where it becomes the linear reflection
`(Y, Z) ↦ (Y, t * Y - Z)` (`torusPair_reflect_second`).  The formulas require
`q ≠ 0`, `P ≠ 0` and `h ≠ 0`.  The two centered lemmas are stated for an
arbitrary ordered frame `(B, C)` and are reused for the second axis.
-/

namespace GenMarkoff.General.Cage

universe u

noncomputable section

open scoped Pointwise

variable {K : Type u} [Field K]

/-- The centered second-coordinate reflection sends `h` to `P / h`. -/
theorem torusPair_reflect_second
    (t q P h : K) (hq : q ≠ 0) (hP : P ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹) :
    ((torusPair q P h).1,
        t * (torusPair q P h).1 - (torusPair q P h).2) =
      torusPair q P (P / h) := by
  subst t
  apply Prod.ext
  · simp [torusPair]
    field_simp [hP, hh]
    ring
  · simp [torusPair]
    field_simp [hq, hP, hh]
    ring

/-- Centering conjugates the affine reflection changing the second moving
coordinate to `(Y, Z) ↦ (Y, tY - Z)`. -/
theorem centerCoordinates_reflect_second
    (B C u t : K) (v : K × K) (hD : discriminant t ≠ 0) :
    centerCoordinates (fiberCenter B C u t)
        (v.1, t * v.1 - v.2 - B * u) =
      let w := centerCoordinates (fiberCenter B C u t) v
      (w.1, t * w.1 - w.2) := by
  apply Prod.ext
  · simp [centerCoordinates]
  · simp [centerCoordinates, fiberCenter]
    field_simp [hD]
    simp only [discriminant]
    ring

/-- On the first-axis torus chart, `vieta3` sends `h` to `P / h`. -/
theorem vieta3_fiberPoint1
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a2 a.a3 u t ≠ 0)
    (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    vieta3 a (fiberPoint1 a u t q h) =
      fiberPoint1 a u t q
        (centeredFiberProduct a.a2 a.a3 u t / h) := by
  let v := fiberPair a.a2 a.a3 u t q h
  have hvieta :
      movingCoordinates1 (vieta3 a (fiberPoint1 a u t q h)) =
        (v.1, t * v.1 - v.2 - a.a2 * u) := by
    apply Prod.ext
    · rfl
    -- `movingCoordinates1`, `vieta3` and `fiberPoint1` unfold the left side
    -- to the new `x₃` coordinate given by the `vieta3` formula; restate it
    -- explicitly so that `hcoordinate` and `ring` apply.
    · change
        a.multiplier * u * v.1 - v.2 - a.a2 * u - a.a1 * v.1 =
          t * v.1 - v.2 - a.a2 * u
      rw [hcoordinate]
      simp only [orderedTrace]
      ring
  have hmoving :
      movingCoordinates1 (vieta3 a (fiberPoint1 a u t q h)) =
        fiberPair a.a2 a.a3 u t q
          (centeredFiberProduct a.a2 a.a3 u t / h) := by
    apply centerCoordinates_injective (fiberCenter a.a2 a.a3 u t)
    rw [hvieta]
    rw [centerCoordinates_reflect_second a.a2 a.a3 u t v hD]
    -- Zeta-reduce the `let w := centerCoordinates _ v` in the statement of
    -- `centerCoordinates_reflect_second`, exposing `centerCoordinates _ v`.
    change
      ((centerCoordinates (fiberCenter a.a2 a.a3 u t) v).1,
          t * (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).1 -
            (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).2) =
        centerCoordinates (fiberCenter a.a2 a.a3 u t)
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / h))
    -- `v` is the local name for `fiberPair a.a2 a.a3 u t q h`; unfold it so
    -- that `centerCoordinates_fiberPair` rewrites both sides.
    rw [show v = fiberPair a.a2 a.a3 u t q h by rfl]
    rw [centerCoordinates_fiberPair, centerCoordinates_fiberPair]
    exact torusPair_reflect_second t q
      (centeredFiberProduct a.a2 a.a3 u t) h hq hP hh heigen
  apply Point.ext
  · simp [vieta3]
  -- The `x₂` coordinate is `(movingCoordinates1 _).1`, and the `x₂` of
  -- `fiberPoint1` is `(fiberPair _).1`, by definition; restate the goal in
  -- this form so that it is the first component of `hmoving`.
  · change
      (movingCoordinates1
        (vieta3 a (fiberPoint1 a u t q h))).1 =
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / h)).1
    exact congrArg Prod.fst hmoving
  -- Likewise the `x₃` coordinate is `(movingCoordinates1 _).2` and
  -- `(fiberPair _).2`; restate as the second component of `hmoving`.
  · change
      (movingCoordinates1
        (vieta3 a (fiberPoint1 a u t q h))).2 =
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / h)).2
    exact congrArg Prod.snd hmoving

end

end GenMarkoff.General.Cage
