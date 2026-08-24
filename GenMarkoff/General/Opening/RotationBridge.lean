import GenMarkoff.General.FiberDynamics
import BGS.Markoff.Core.FiniteRotationEigenvalues

/-!
# Reusing the BGS trace-matrix kernel for actual rotations

The common linear half-step in a general affine fiber is definitionally the
BGS trace matrix.  The fixed-coefficient rotation has its square as linear
part, so its order is the BGS rotation order divided by the parity factor.
-/

namespace GenMarkoff.General.Opening

universe u

open scoped Matrix

theorem fiberMatrix_eq_bgsRho
    {R : Type u} [CommRing R] (t : R) :
    fiberMatrix t = BGS.Markoff.rho t :=
  rfl

theorem fiberMatrixSL_eq_bgsRhoSL
    {R : Type u} [CommRing R] (t : R) :
    fiberMatrixSL t = BGS.Markoff.rhoSL t :=
  rfl

/-- The order of the common half-step matrix is the BGS rotation order. -/
theorem fiberMatrixOrder_eq_bgsRotationOrder
    {R : Type u} [CommRing R] (t : R) :
    orderOf (fiberMatrixSL t) = BGS.Markoff.rotationOrder t :=
  rfl

/-- The actual rotation linear order is the BGS trace-matrix order divided by
the possible factor `2`. -/
theorem rotationLinearOrder_eq_bgsRotationOrder_div_gcd
    {R : Type u} [CommRing R] (t : R) :
    rotationLinearOrder t =
      BGS.Markoff.rotationOrder t /
        Nat.gcd (BGS.Markoff.rotationOrder t) 2 := by
  simpa only [fiberMatrixOrder_eq_bgsRotationOrder] using
    rotationLinearOrder_eq_order_div_gcd t

/-- A small actual rotation order forces the BGS half-step order into the
same range up to the parity factor `2`. -/
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
  change n < 2 * bound
  rw [hnEq]
  have hmul : n / g * g < bound * 2 :=
    Nat.mul_lt_mul_of_lt_of_le hn hgLe (by omega)
  simpa [Nat.mul_comm] using hmul

/-- Reused eigenvalue parametrization for the common trace matrix. -/
theorem exists_torsionEigenvalue_of_finiteOrder_fiberMatrix
    {K : Type u} [Field K] [IsAlgClosed K] (t : K)
    (hfinite : IsOfFinOrder (fiberMatrixSL t)) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ t = BGS.Markoff.splitTorusTrace w := by
  rw [fiberMatrixSL_eq_bgsRhoSL] at hfinite
  exact BGS.Markoff.finiteOrderRotation_has_torsion_eigenvalue t hfinite

end GenMarkoff.General.Opening
