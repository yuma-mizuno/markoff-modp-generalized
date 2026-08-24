import GenMarkoff.Divisibility.RawAngleDefect
import GenMarkoff.Core.Action

/-!
# Summing the raw-angle defect on an invariant finite set

The totalized raw-angle balance has a correction precisely at zero
coordinates.  On a finite set invariant under the three individual Vieta
involutions, all non-correction raw-angle terms cancel after reindexing.
-/

namespace GenMarkoff

universe u

section Field

variable {K : Type u} [Field K]

/-- Summing the totalized raw-angle balance over a finite set invariant under
the three Vieta involutions leaves only the zero-coordinate correction. -/
theorem multiplier_mul_card_cast_eq_two_mul_sum_zeroRawAngleCorrection_of_vieta_invariant
    (a : Coefficients K) (h2 : (2 : K) ≠ 0)
    (C : Finset (PuncturedSolutionSurface a))
    (hC1 : ∀ x, vieta1PuncturedPerm a x ∈ C ↔ x ∈ C)
    (hC2 : ∀ x, vieta2PuncturedPerm a x ∈ C ↔ x ∈ C)
    (hC3 : ∀ x, vieta3PuncturedPerm a x ∈ C ↔ x ∈ C) :
    a.multiplier * (C.card : K) =
      2 * ∑ x : C, zeroRawAngleCorrection a x.1.1 := by
  classical
  have hreindex1 :
      (∑ x : C, rawAngle1 a (vieta1 a x.1.1)) =
        ∑ x : C, rawAngle1 a x.1.1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp ((vieta1PuncturedPerm a).subtypePerm hC1)
        (fun x : C ↦ rawAngle1 a x.1.1))
  have hreindex2 :
      (∑ x : C, rawAngle2 a (vieta2 a x.1.1)) =
        ∑ x : C, rawAngle2 a x.1.1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp ((vieta2PuncturedPerm a).subtypePerm hC2)
        (fun x : C ↦ rawAngle2 a x.1.1))
  have hreindex3 :
      (∑ x : C, rawAngle3 a (vieta3 a x.1.1)) =
        ∑ x : C, rawAngle3 a x.1.1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp ((vieta3PuncturedPerm a).subtypePerm hC3)
        (fun x : C ↦ rawAngle3 a x.1.1))
  calc
    a.multiplier * (C.card : K) = ∑ _x : C, a.multiplier := by
      simp [mul_comm]
    _ = ∑ x : C, (
        (((rawAngle1 a x.1.1 + rawAngle1 a (vieta1 a x.1.1)) +
            (rawAngle2 a x.1.1 + rawAngle2 a (vieta2 a x.1.1)) +
            (rawAngle3 a x.1.1 + rawAngle3 a (vieta3 a x.1.1))) +
          2 * zeroRawAngleCorrection a x.1.1) -
          2 * (rawAngle1 a x.1.1 + rawAngle2 a x.1.1 + rawAngle3 a x.1.1)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      have hbalance := rawAngle_balance_with_zero_correction
        a x.1.1 h2 x.1.1.2 (by
          intro hpoint
          apply x.1.2
          apply Subtype.ext
          exact hpoint)
      linear_combination hbalance
    _ = 2 * ∑ x : C, zeroRawAngleCorrection a x.1.1 := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hreindex1, hreindex2, hreindex3]
      simp_rw [Finset.sum_add_distrib]
      ring

end Field

end GenMarkoff
