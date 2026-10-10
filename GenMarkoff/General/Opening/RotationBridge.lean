import GenMarkoff.General.FiberDynamics
import BGS.Markoff.Core.FiniteRotationEigenvalues

/-!
# Rotation orders through the BGS trace matrix

The common linear step `fiberMatrixSL t` on a generalized affine fiber is
definitionally the classical trace matrix `BGS.Markoff.rhoSL t`, whose order
is `BGS.Markoff.rotationOrder t`.  The fixed-coefficient rotation has its
square as linear part, so its order `rotationLinearOrder t` is
`BGS.Markoff.rotationOrder t` divided by its greatest common divisor with `2`.
This lets the order estimates for the classical Markoff rotations in
`BGS.Markoff` apply to the generalized surface.
-/

namespace GenMarkoff.General.Opening

universe u

open scoped Matrix

/-- The order of the common linear step matrix is the BGS rotation order. -/
theorem fiberMatrixOrder_eq_bgsRotationOrder
    {R : Type u} [CommRing R] (t : R) :
    orderOf (fiberMatrixSL t) = BGS.Markoff.rotationOrder t :=
  rfl

/-- The rotation linear order is the BGS trace-matrix order divided by its
greatest common divisor with `2`. -/
theorem rotationLinearOrder_eq_bgsRotationOrder_div_gcd
    {R : Type u} [CommRing R] (t : R) :
    rotationLinearOrder t =
      BGS.Markoff.rotationOrder t /
        Nat.gcd (BGS.Markoff.rotationOrder t) 2 := by
  simpa only [fiberMatrixOrder_eq_bgsRotationOrder] using
    rotationLinearOrder_eq_order_div_gcd t

/-- If the rotation linear order is below `bound`, the BGS trace-matrix order
is below `2 * bound`. -/
theorem bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
    {R : Type u} [CommRing R] [Finite R]
    (t : R) (bound : ℕ)
    (hsmall : rotationLinearOrder t < bound) :
    BGS.Markoff.rotationOrder t < 2 * bound := by
  let n := BGS.Markoff.rotationOrder t
  let g := Nat.gcd n 2
  have hgPos : 0 < g := Nat.gcd_pos_of_pos_right n (by norm_num)
  have hgDvd : g ∣ n := Nat.gcd_dvd_left n 2
  have hgLe : g ≤ 2 := Nat.gcd_le_right n (by norm_num)
  have hn : n / g < bound := by
    simpa [n, g, rotationLinearOrder_eq_bgsRotationOrder_div_gcd] using hsmall
  have hnEq : n = n / g * g := by
    exact (Nat.div_mul_cancel hgDvd).symm
  -- The goal mentions `BGS.Markoff.rotationOrder t`, which is the local `n`;
  -- restate so that `rw [hnEq]` applies.
  change n < 2 * bound
  rw [hnEq]
  have hmul : n / g * g < bound * 2 :=
    Nat.mul_lt_mul_of_lt_of_le hn hgLe (by omega)
  simpa [Nat.mul_comm] using hmul

end GenMarkoff.General.Opening
