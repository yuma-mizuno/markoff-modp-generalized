import GenMarkoff.General.TraceParameters
import BGS.Markoff.TraceCurve.Geometry

/-!
# Wiring a general first-coordinate fiber to the actual rotation

On a first-coordinate fiber, the two-Vieta rotation `rotation1` multiplies the
torus parameter by `q ^ 2`.  Consequently the parameters reachable from a
starting unit `r` form the translated coset

`r * Subgroup.zpowers (q ^ 2)`.

This is a genuine parity distinction from the symmetric one-step wiring,
which uses `Subgroup.zpowers q`: when `q` has even order, the square-generated
subgroup can be a proper parity class.  The middle game must therefore use
the actual square subgroup and its actual order throughout.

Translation by `r` changes the first-directed weights from
`actualAlpha s` and `actualBeta s B C u t` to
`actualAlpha s * r` and `actualBeta s B C u t / r`; their product remains
`actualSigma s B C u t`, and the affine shift remains
`actualGammaFirst s B C u t`.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- One actual first-axis rotation multiplies the torus parameter by
`q ^ 2`. -/
theorem rotation1_fiberPoint1_eq_sq_mul
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    rotation1 a (fiberPoint1 a u t q h) =
      fiberPoint1 a u t q (q ^ 2 * h) :=
  rotation1_fiberPoint1
    a u t q h hD hq hh heigen hcoordinate

/-- Every forward iterate of the first-axis rotation has the expected
square-power torus parameter. -/
theorem iterate_rotation1_fiberPoint1_eq_pow_mul
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) (n : ℕ) :
    ((rotation1 a)^[n]) (fiberPoint1 a u t q h) =
      fiberPoint1 a u t q ((q ^ 2) ^ n * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [rotation1_fiberPoint1_eq_sq_mul
        a u t q ((q ^ 2) ^ n * h) hD hq
        (mul_ne_zero (pow_ne_zero n (pow_ne_zero 2 hq)) hh)
        heigen hcoordinate]
      congr 1
      rw [pow_succ]
      ring

/-- Every point in the translated square-generated parameter coset is a
forward iterate of the first-axis rotation.  Finiteness is used only to
replace an integral power by a nonnegative power. -/
theorem exists_iterate_fiberPoint1_eq_mul_zpowers_sq
    [Finite K] (a : Coefficients K) (u t : K) (q r : Kˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = (q : K) + ((q⁻¹ : Kˣ) : K))
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (h : Subgroup.zpowers (q ^ 2)) :
    ∃ n : ℕ,
      ((rotation1 a)^[n])
          (fiberPoint1 a u t (q : K) (r : K)) =
        fiberPoint1 a u t (q : K)
          ((r * (h : Kˣ) : Kˣ) : K) := by
  have hhPowers : (h : Kˣ) ∈ Submonoid.powers (q ^ 2) :=
    mem_powers_iff_mem_zpowers.mpr h.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (h : Kˣ) (q ^ 2)).mp hhPowers
  refine ⟨n, ?_⟩
  have heigen' : t = (q : K) + (q : K)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using heigen
  rw [iterate_rotation1_fiberPoint1_eq_pow_mul
    a u t (q : K) (r : K) hD (Units.ne_zero q) (Units.ne_zero r)
    heigen' hcoordinate n]
  congr 1
  have hnVal :
      ((h : Kˣ) : K) = (((q ^ 2) ^ n : Kˣ) : K) :=
    congrArg (fun z : Kˣ => (z : K)) hn.symm
  simp only [Units.val_pow_eq_pow_val] at hnVal
  simp only [Units.val_mul]
  rw [hnVal]
  ring

/-- Exact first-directed adjacent trace on a translated actual-rotation
parameter coset. -/
theorem orderedTrace_fiberPoint1_mul_eq_weightedSplitTorusTrace
    (a : Coefficients K) (u t : K) (q r h : Kˣ) :
    orderedTrace a.multiplier a.a2
        (fiberPoint1 a u t (q : K)
          ((r * h : Kˣ) : K)).x2 =
      weightedSplitTorusTrace
          (actualAlpha a.multiplier * (r : K))
          (actualBeta a.multiplier a.a2 a.a3 u t / (r : K)) h +
        actualGammaFirst a.multiplier a.a2 a.a3 u t := by
  change
    a.multiplier *
          (fiberPair a.a2 a.a3 u t (q : K)
            ((r * h : Kˣ) : K)).1 -
        a.a2 =
      weightedSplitTorusTrace
          (actualAlpha a.multiplier * (r : K))
          (actualBeta a.multiplier a.a2 a.a3 u t / (r : K)) h +
        actualGammaFirst a.multiplier a.a2 a.a3 u t
  rw [firstTrace_fiberPair a.multiplier a.a2 a.a3 u t
    (q : K) ((r * h : Kˣ) : K) (Units.ne_zero (r * h))]
  simp only [weightedSplitTorusTrace, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero r, Units.ne_zero h]

/-- Translating the first-directed weights changes them individually but
preserves their invariant product. -/
theorem actual_firstDirected_coset_weights_mul
    (s B C u t : K) (r : Kˣ) :
    (actualAlpha s * (r : K)) *
        (actualBeta s B C u t / (r : K)) =
      actualSigma s B C u t := by
  simp only [actualSigma]
  field_simp [Units.ne_zero r]

end

end GenMarkoff.General.MiddleGame
