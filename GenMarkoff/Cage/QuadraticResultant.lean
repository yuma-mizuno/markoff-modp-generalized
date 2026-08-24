import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A closed resultant formula for two formal quadratics

This generic identity is shared by coefficient-dependent cage calculations.
The formal degrees are fixed at two, so the formula remains valid when a
displayed leading coefficient specializes to zero.
-/

namespace GenMarkoff.Cage

open Polynomial

noncomputable section

variable {K : Type*} [CommRing K]

/-- Closed formula for the formal-degree-two resultant of two quadratics. -/
theorem resultant_quadratic_quadratic
    (a b d e f h : K) :
    Polynomial.resultant
        (C a * X ^ 2 + C b * X + C d)
        (C e * X ^ 2 + C f * X + C h) 2 2 =
      (a * h - d * e) ^ 2 -
        (a * f - b * e) * (b * h - d * f) := by
  rw [Polynomial.resultant]
  let M : Matrix (Fin 4) (Fin 4) K :=
    !![h, 0, d, 0;
       f, h, b, d;
       e, f, a, b;
       0, e, 0, a]
  have hsyl :
      Polynomial.sylvester
          (C a * X ^ 2 + C b * X + C d)
          (C e * X ^ 2 + C f * X + C h) 2 2 =
        M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.sylvester, Fin.addCases, Fin.castAdd, Fin.natAdd,
        Polynomial.coeff_X, M]
  have hM00 : M 0 0 = h := by rfl
  have hM01 : M 0 1 = 0 := by rfl
  have hM02 : M 0 2 = d := by rfl
  have hM03 : M 0 3 = 0 := by rfl
  have hsub0 :
      M.submatrix Fin.succ Fin.succ =
        !![h, b, d;
           f, a, b;
           e, 0, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hsub2 :
      M.submatrix Fin.succ (Fin.succAbove (2 : Fin 4)) =
        !![f, h, d;
           e, f, b;
           0, e, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hsyl, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  rw [hM00, hM01, hM02, hM03]
  norm_num [Fin.succAbove_zero]
  rw [hsub0, hsub2]
  simp [Matrix.det_fin_three]
  ring

end

end GenMarkoff.Cage
