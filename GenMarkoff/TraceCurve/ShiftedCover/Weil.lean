import GenMarkoff.TraceCurve.ShiftedCover.ResidueBlocks
import BGS.HasseWeil.GeneralBivariateAffineHasseWeil
import BGS.Markoff.Endgame.WeilFromGeneralHasse

/-!
# Hasse--Weil inputs for shifted trace covers

This file proves the two geometric facts needed to apply the affine
Hasse--Weil theorem to `shiftedTraceCoverPolynomial alpha beta gamma d e`:
its bidegree is at most `(2d, 2e)`, and for positive exponents and
`beta ≠ 0` its only zero on the coordinate axes is the origin.  Both are as for the unshifted cover
`BGS.Markoff.splitTraceCoverPolynomial`.  The Hasse--Weil estimate itself is
applied in `TraceCurve.WeightedShiftedCover.Counting`.
-/

namespace GenMarkoff

open Polynomial

noncomputable section

section Degrees

variable {K : Type*} [Field K]

private theorem shiftedCover_degreeOf_first_monomial_le
    (a b : ℕ) (r : K) :
    MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C r * MvPolynomial.X 0 ^ a *
          MvPolynomial.X 1 ^ b) ≤ a := by
  calc
    _ ≤ MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C r * MvPolynomial.X 0 ^ a) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ b) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C r) +
          MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0 ^ a)) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ b) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ a := by
      have ha : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K) ≤ a := by
        calc
          _ ≤ a * MvPolynomial.degreeOf (0 : Fin 2)
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = a := by rw [MvPolynomial.degreeOf_X]; norm_num
      have hb : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ b * MvPolynomial.degreeOf (0 : Fin 2)
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      omega

private theorem shiftedCover_degreeOf_second_monomial_le
    (a b : ℕ) (r : K) :
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C r * MvPolynomial.X 0 ^ a *
          MvPolynomial.X 1 ^ b) ≤ b := by
  calc
    _ ≤ MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.C r * MvPolynomial.X 0 ^ a) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1 ^ b) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C r) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0 ^ a)) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1 ^ b) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ b := by
      have ha : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ a * MvPolynomial.degreeOf (1 : Fin 2)
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      have hb : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K) ≤ b := by
        calc
          _ ≤ b * MvPolynomial.degreeOf (1 : Fin 2)
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = b := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      omega

/-- The shifted cover has degree at most `2 * d` in the first variable. -/
theorem weightedShiftedTraceCoverPolynomial_degreeOf_first_le
    (alpha beta gamma : K) (d e : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (shiftedTraceCoverPolynomial alpha beta gamma d e) ≤ 2 * d := by
  unfold shiftedTraceCoverPolynomial
  -- Each `show` below only states the arithmetic bound passed to `trans`; nothing is unfolded.
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
        · simpa using
            (shiftedCover_degreeOf_first_monomial_le d (2 * e) alpha).trans
              (show d ≤ 2 * d by omega)
        · simpa using
            (shiftedCover_degreeOf_first_monomial_le d 0 beta).trans
              (show d ≤ 2 * d by omega)
      · simpa using
          (shiftedCover_degreeOf_first_monomial_le d e gamma).trans
            (show d ≤ 2 * d by omega)
    · simpa using
        (shiftedCover_degreeOf_first_monomial_le (2 * d) e (1 : K))
  · simpa using
      (shiftedCover_degreeOf_first_monomial_le 0 e (1 : K)).trans
        (show 0 ≤ 2 * d by omega)

/-- The shifted cover has degree at most `2 * e` in the second variable. -/
theorem weightedShiftedTraceCoverPolynomial_degreeOf_second_le
    (alpha beta gamma : K) (d e : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (shiftedTraceCoverPolynomial alpha beta gamma d e) ≤ 2 * e := by
  unfold shiftedTraceCoverPolynomial
  -- Each `show` below only states the arithmetic bound passed to `trans`; nothing is unfolded.
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
        · simpa using
            shiftedCover_degreeOf_second_monomial_le d (2 * e) alpha
        · simpa using
            (shiftedCover_degreeOf_second_monomial_le d 0 beta).trans
              (show 0 ≤ 2 * e by omega)
      · simpa using
          (shiftedCover_degreeOf_second_monomial_le d e gamma).trans
            (show e ≤ 2 * e by omega)
    · simpa using
        (shiftedCover_degreeOf_second_monomial_le (2 * d) e (1 : K)).trans
          (show e ≤ 2 * e by omega)
  · simpa using
      (shiftedCover_degreeOf_second_monomial_le 0 e (1 : K)).trans
        (show e ≤ 2 * e by omega)

/-- The shifted cover has bidegree at most `(2 * d, 2 * e)`. -/
theorem weightedShiftedTraceCoverPolynomial_hasBidegreeAtMost
    (alpha beta gamma : K) (d e : ℕ) :
    BGS.External.HasBidegreeAtMost
      (shiftedTraceCoverPolynomial alpha beta gamma d e)
      (2 * d) (2 * e) := by
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp
      (weightedShiftedTraceCoverPolynomial_degreeOf_first_le
        alpha beta gamma d e))
        monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp
      (weightedShiftedTraceCoverPolynomial_degreeOf_second_le
        alpha beta gamma d e))
        monomial hmonomial⟩

end Degrees

section Boundary

variable {K : Type*} [Field K]

/-- For positive exponents and `beta ≠ 0`, a zero of the shifted cover on a
coordinate axis is the origin. -/
theorem weightedShiftedTraceCoverPolynomial_axis_zero_eq_origin
    (alpha beta gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hbeta : beta ≠ 0) (x y : K)
    (hzero : MvPolynomial.eval ![x, y]
      (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0)
    (haxis : x = 0 ∨ y = 0) :
    x = 0 ∧ y = 0 := by
  rw [eval_shiftedTraceCoverPolynomial] at hzero
  have htwoD : 2 * d ≠ 0 := by omega
  have htwoE : 2 * e ≠ 0 := by omega
  rcases haxis with rfl | rfl
  · constructor
    · rfl
    · have hyPow : y ^ e = 0 := by
        have hneg : -(y ^ e) = 0 := by
          simpa only [zero_pow hd.ne', zero_pow htwoD, zero_mul, mul_zero,
            add_zero, sub_zero, zero_sub] using hzero
        exact neg_eq_zero.mp hneg
      exact (pow_eq_zero_iff he.ne').mp hyPow
  · constructor
    · have hxPow : x ^ d = 0 := by
        have hbetaPow : beta * x ^ d = 0 := by
          simpa only [zero_pow he.ne', zero_pow htwoE, mul_zero,
            add_zero, sub_zero, zero_add] using hzero
        exact (mul_eq_zero.mp hbetaPow).resolve_left hbeta
      exact (pow_eq_zero_iff hd.ne').mp hxPow
    · rfl

/-- For positive exponents the origin is a zero of the shifted cover. -/
theorem weightedShiftedTraceCoverPolynomial_origin_zero
    (alpha beta gamma : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    MvPolynomial.eval ![(0 : K), (0 : K)]
      (shiftedTraceCoverPolynomial alpha beta gamma d e) = 0 := by
  rw [eval_shiftedTraceCoverPolynomial]
  have htwoD : 2 * d ≠ 0 := by omega
  have htwoE : 2 * e ≠ 0 := by omega
  simp only [zero_pow hd.ne', zero_pow he.ne', zero_pow htwoD,
    zero_pow htwoE, mul_zero, add_zero, sub_zero]

end Boundary

end

end GenMarkoff
