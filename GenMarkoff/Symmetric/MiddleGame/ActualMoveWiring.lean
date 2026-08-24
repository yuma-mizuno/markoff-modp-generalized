import GenMarkoff.Symmetric.MiddleGame.ActualParameters
import GenMarkoff.Symmetric.OneStepParabolic

/-!
# Wiring actual symmetric fibers to the one-step action

The torus parameter on a fixed first-coordinate fiber is multiplied by the
chosen eigenvalue under each application of `oneStep1`.  Consequently an
orbit through parameter `s` runs through the coset
`s * Subgroup.zpowers q`, rather than through the subgroup itself.

The adjacent trace on that coset has weights

`alpha = actualAlpha c * s`, `beta = actualBeta c u t / s`,

whose product is the fiber invariant `actualSigma c u t`.
-/

namespace GenMarkoff.Symmetric.MiddleGame

open BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- One concrete symmetric one-step multiplies the torus parameter by the
chosen eigenvalue. -/
theorem oneStep1_fiberPoint_eq_mul
    (c u t q h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htraceEigenvalue : t = q + q⁻¹)
    (htraceCoordinate : t = trace c u) (ht : t ≠ 2) :
    oneStep1 c (fiberPoint c u t q h) =
      fiberPoint c u t q (q * h) := by
  apply Point.ext
  · exact oneStep1_x1 c (fiberPoint c u t q h)
  · have hmoving :
        movingCoordinates1 (oneStep1 c (fiberPoint c u t q h)) =
          movingCoordinates1 (fiberPoint c u t q (q * h)) := by
      rw [movingCoordinates1_oneStep1, fiberPoint_x1]
      change affineStep c u (trace c u)
          (movingCoordinates1 (fiberPoint c u t q h)) =
        movingCoordinates1 (fiberPoint c u t q (q * h))
      rw [← htraceCoordinate]
      exact affineStep_fiberPoint_movingCoordinates
        c u t q h hq hh htraceEigenvalue ht
    exact congrArg Prod.fst hmoving
  · have hmoving :
        movingCoordinates1 (oneStep1 c (fiberPoint c u t q h)) =
          movingCoordinates1 (fiberPoint c u t q (q * h)) := by
      rw [movingCoordinates1_oneStep1, fiberPoint_x1]
      change affineStep c u (trace c u)
          (movingCoordinates1 (fiberPoint c u t q h)) =
        movingCoordinates1 (fiberPoint c u t q (q * h))
      rw [← htraceCoordinate]
      exact affineStep_fiberPoint_movingCoordinates
        c u t q h hq hh htraceEigenvalue ht
    exact congrArg Prod.snd hmoving

/-- Every forward iterate has the expected torus parameter. -/
theorem iterate_oneStep1_fiberPoint_eq_pow_mul
    (c u t q h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htraceEigenvalue : t = q + q⁻¹)
    (htraceCoordinate : t = trace c u) (ht : t ≠ 2) (n : ℕ) :
    ((oneStep1 c)^[n]) (fiberPoint c u t q h) =
      fiberPoint c u t q (q ^ n * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [oneStep1_fiberPoint_eq_mul c u t q (q ^ n * h)
        hq (mul_ne_zero (pow_ne_zero n hq) hh)
        htraceEigenvalue htraceCoordinate ht]
      congr 1
      rw [pow_succ]
      ring

/-- Every point in the translated cyclic parameter coset is a forward
one-step iterate of the point with parameter `s`.  Finiteness is used only to
replace an integral power by a nonnegative power. -/
theorem exists_iterate_fiberPoint_eq_mul_zpowers
    [Finite K] (c u t : K) (q s : Kˣ)
    (htraceEigenvalue : t = (q : K) + ((q⁻¹ : Kˣ) : K))
    (htraceCoordinate : t = trace c u) (ht : t ≠ 2)
    (h : Subgroup.zpowers q) :
    ∃ n : ℕ,
      ((oneStep1 c)^[n]) (fiberPoint c u t (q : K) (s : K)) =
        fiberPoint c u t (q : K) ((s * (h : Kˣ) : Kˣ) : K) := by
  have hhPowers : (h : Kˣ) ∈ Submonoid.powers q :=
    mem_powers_iff_mem_zpowers.mpr h.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (h : Kˣ) q).mp hhPowers
  refine ⟨n, ?_⟩
  have htraceEigenvalue' : t = (q : K) + (q : K)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using htraceEigenvalue
  rw [iterate_oneStep1_fiberPoint_eq_pow_mul c u t
    (q : K) (s : K) (Units.ne_zero q) (Units.ne_zero s)
    htraceEigenvalue' htraceCoordinate ht n]
  congr 1
  have hnVal : ((h : Kˣ) : K) = ((q ^ n : Kˣ) : K) :=
    congrArg (fun z : Kˣ => (z : K)) hn.symm
  simp only [Units.val_pow_eq_pow_val] at hnVal
  simp only [Units.val_mul]
  rw [hnVal]
  ring

/-- Exact adjacent-trace formula on the translated parameter coset. -/
theorem trace_fiberPoint_mul_eq_weightedSplitTorusTrace
    (c u t : K) (q s h : Kˣ) :
    trace c
        (fiberPoint c u t (q : K) ((s * h : Kˣ) : K)).x2 =
      weightedSplitTorusTrace
          (actualAlpha c * (s : K))
          (actualBeta c u t / (s : K)) h +
        actualGamma c u t := by
  rw [trace_fiberPoint_x2 c u t (q : K)
    ((s * h : Kˣ) : K) (Units.ne_zero (s * h))]
  simp only [weightedSplitTorusTrace, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero s, Units.ne_zero h]

/-- Translation changes the two trace weights individually but preserves
their product. -/
theorem actual_coset_weights_mul
    (c u t : K) (s : Kˣ) :
    (actualAlpha c * (s : K)) *
        (actualBeta c u t / (s : K)) =
      actualSigma c u t := by
  simp only [actualSigma]
  field_simp [Units.ne_zero s]

end

end GenMarkoff.Symmetric.MiddleGame
