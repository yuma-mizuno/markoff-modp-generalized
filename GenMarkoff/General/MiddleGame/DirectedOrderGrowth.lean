module

public import GenMarkoff.General.MiddleGame.ActualOrderGrowth

@[expose] public section

/-!
# Second-axis move wiring and reverse-frame parameters

This file is the second-coordinate companion of
`GenMarkoff.General.MiddleGame.ActualMoveWiring` and
`GenMarkoff.General.MiddleGame.ActualParameters`.  A coordinate permutation is
not a symmetry of a fixed coefficient triple with distinct entries, so the
statements are proved directly for `rotation2` and `fiberPoint2`, whose moving
coordinates are ordered `(x₃, x₁)`.

* `rotation2` multiplies the torus parameter of `fiberPoint2` by `q ^ 2`, so
  the parameters reachable from `r` form `r * Subgroup.zpowers (q ^ 2)`.
* On the parameter `r * h`, the trace of the second moving coordinate of
  `fiberPair B C u t q` is a weighted split-torus trace of `h` with weights
  `s * q * r` and `s * centeredFiberProduct B C u t / q / r`, weight product
  `actualSigma s B C u t`, and shift `actualGammaSecond s B C u t`.
* Candidate regularity in the reverse frame `(A, C, B)` makes this weight
  product nonzero and, with `C ^ 2 ≠ 4`, makes the common-even obstruction
  nonzero.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.ShiftedTrace.MiddleGame

noncomputable section

section DirectedMoveWiring

variable {K : Type*} [Field K]

/-- Every second-axis rotation iterate multiplies the torus parameter by the
corresponding power of `q ^ 2`. -/
theorem iterate_rotation2_fiberPoint2_eq_pow_mul
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) (n : ℕ) :
    ((rotation2 a)^[n]) (fiberPoint2 a u t q h) =
      fiberPoint2 a u t q ((q ^ 2) ^ n * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [rotation2_fiberPoint2
        a u t q ((q ^ 2) ^ n * h) hD hq
        (mul_ne_zero (pow_ne_zero n (pow_ne_zero 2 hq)) hh)
        heigen hcoordinate]
      congr 1
      rw [pow_succ]
      ring

/-- Every translated square-coset parameter on a second-coordinate fiber is
reached by a forward `rotation2` iterate. -/
theorem exists_iterate_fiberPoint2_eq_mul_zpowers_sq
    [Finite K] (a : Coefficients K) (u t : K) (q r : Kˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = (q : K) + ((q⁻¹ : Kˣ) : K))
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (h : Subgroup.zpowers (q ^ 2)) :
    ∃ n : ℕ,
      ((rotation2 a)^[n])
          (fiberPoint2 a u t (q : K) (r : K)) =
        fiberPoint2 a u t (q : K) ((r * (h : Kˣ) : Kˣ) : K) := by
  have hhPowers : (h : Kˣ) ∈ Submonoid.powers (q ^ 2) :=
    mem_powers_iff_mem_zpowers.mpr h.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (h : Kˣ) (q ^ 2)).mp hhPowers
  refine ⟨n, ?_⟩
  have heigen' : t = (q : K) + (q : K)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using heigen
  rw [iterate_rotation2_fiberPoint2_eq_pow_mul
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

/-- At the translated parameter `r * h`, the trace of the second moving
coordinate is the weighted split-torus trace of `h` with weights
`s * q * r` and `s * centeredFiberProduct B C u t / q / r`, shifted by
`actualGammaSecond s B C u t`. -/
theorem secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
    (s B C u t : K) (q r h : Kˣ) :
    s * (fiberPair B C u t (q : K) ((r * h : Kˣ) : K)).2 - C =
      weightedSplitTorusTrace
          ((s * (q : K)) * (r : K))
          ((s * centeredFiberProduct B C u t / (q : K)) / (r : K)) h +
        actualGammaSecond s B C u t := by
  rw [secondTrace_fiberPair s B C u t
    (q : K) ((r * h : Kˣ) : K)
    (Units.ne_zero q) (Units.ne_zero (r * h))]
  simp only [weightedSplitTorusTrace, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero q, Units.ne_zero r, Units.ne_zero h]

/-- Translating the second-directed weights preserves the common invariant
product `actualSigma`. -/
theorem actual_secondDirected_coset_weights_mul
    (s B C u t : K) (q r : Kˣ) :
    ((s * (q : K)) * (r : K)) *
        ((s * centeredFiberProduct B C u t / (q : K)) / (r : K)) =
      actualSigma s B C u t := by
  calc
    ((s * (q : K)) * (r : K)) *
          ((s * centeredFiberProduct B C u t / (q : K)) / (r : K)) =
        (s * (q : K)) *
          (s * centeredFiberProduct B C u t / (q : K)) := by
            field_simp [Units.ne_zero r]
    _ = actualSigma s B C u t :=
      secondTrace_weight_product s B C u t (q : K) (Units.ne_zero q)

/-- The ordered weight product is symmetric in the two moving
coefficients. -/
theorem orderedTraceSigma_swap (A B C t : K) :
    orderedTraceSigma A B C t = orderedTraceSigma A C B t := by
  simp only [orderedTraceSigma]
  ring

/-- Candidate regularity for the reverse directed frame makes the common
actual weight product nonzero. -/
theorem actualSigma_ne_zero_of_reverseCandidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A C B t) :
    actualSigma s B C u t ≠ 0 := by
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace,
    orderedTraceSigma_swap A B C t]
  exact hregular.sigma_ne_zero

/-- Candidate regularity for the reverse directed frame `(A, C, B)` and
`C ^ 2 ≠ 4` make the common-even obstruction of the second-directed actual
parameters nonzero. -/
theorem actualSecondEvenObstruction_ne_zero_of_candidateRegular
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u) (hC : C ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular A C B t) :
    shiftedTraceEvenObstruction (actualSigma s B C u t)
        (actualGammaSecond s B C u t) ≠ 0 := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  rw [actualSigma_eq_orderedTraceSigma s A B C u t htrace,
    orderedTraceSigma_swap A B C t,
    actualGammaSecond_eq_orderedTraceGamma
      s A B C u t hD htrace]
  exact hregular.evenObstruction_ne_zero hC

end DirectedMoveWiring

end

end GenMarkoff.General.MiddleGame
